module

public import CFSG.RankThree.PartOne.K159W.Defs
public import CFSG.RankThree.PartOne.K159.CoverLift

public section

namespace CFSG.RankThree.PartOne.K159W

open CFSG.RankThree.PartOne.K159

section Lift

variable {Y : Type} {T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem exists_elemAbelian_card_ge_comap [Finite Y] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {p : ℕ} (hp : p.Prime)
    (S : Set T) (hSp : ∀ s ∈ S, s ^ p = 1) (hSinv : ∀ s ∈ S, ∃ g : T, g * s * g⁻¹ = s⁻¹)
    (hF : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ,
      x * y = y * x)
    {z : Y} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, B ≤ (Subgroup.closure S).comap φ ∧ (∀ b ∈ B, b ^ p = 1) ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ p * Nat.card (Subgroup.closure S) ≤ Nat.card B ∧
      ∀ s ∈ S, ∃ y ∈ B, φ y = s := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hlift : ∀ s : S, ∃ y : Y, φ y = s ∧ y ^ p = 1 := fun s =>
    exists_lift_pow_eq_one hker hodd (hSp s s.2) (hSinv s s.2).choose
      (hSinv s s.2).choose_spec hφ
  choose y hyφ hyp using hlift
  set G : Set Y := Set.range y ∪ {z} with hG
  have hyF : ∀ s : S, y s ∈ (Subgroup.closure S).comap φ := fun s => by
    rw [Subgroup.mem_comap, hyφ]
    exact Subgroup.subset_closure s.2
  have hzc : z ∈ Subgroup.center Y := hker hz
  have hGcomm : ∀ a ∈ G, ∀ b ∈ G, Commute a b := by
    rintro a (⟨s, rfl⟩ | rfl) b (⟨t, rfl⟩ | rfl)
    · exact hF _ (hyF s) _ (hyF t)
    · exact Subgroup.mem_center_iff.1 hzc _
    · exact (Subgroup.mem_center_iff.1 hzc _).symm
    · exact Commute.refl _
  have hGp : ∀ a ∈ G, a ^ p = 1 := by
    rintro a (⟨s, rfl⟩ | rfl)
    · exact hyp s
    · exact hzp
  set B : Subgroup Y := Subgroup.closure G with hB
  have hzB : z ∈ B := Subgroup.subset_closure (Or.inr rfl)
  refine ⟨B, ?_, fun b hb => pow_eq_one_of_mem_closure' hGcomm hGp hb,
    fun a ha b hb => (commute_of_mem_closure' hGcomm ha hb).eq, ?_, ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro a (⟨s, rfl⟩ | rfl)
    · exact hyF s
    · exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 hz]; exact Subgroup.one_mem _)
  · let ψ : B →* T := φ.comp B.subtype
    have hcard := Subgroup.card_ker_mul_card_range ψ
    have hrange : Subgroup.closure S ≤ ψ.range := by
      refine (Subgroup.closure_le _).2 fun s hs => ?_
      exact ⟨⟨y ⟨s, hs⟩, Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)⟩, hyφ ⟨s, hs⟩⟩
    have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
    have hkerle : Subgroup.zpowers (⟨z, hzB⟩ : B) ≤ ψ.ker := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
      exact hz
    have ho : orderOf (⟨z, hzB⟩ : B) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hzo
    have h1 : p ≤ Nat.card ψ.ker := by
      have := Subgroup.card_le_of_le hkerle
      rwa [Nat.card_zpowers, ho] at this
    have hfinr : Finite ψ.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective ψ)
    have h2 : Nat.card (Subgroup.closure S) ≤ Nat.card ψ.range := Subgroup.card_le_of_le hrange
    calc p * Nat.card (Subgroup.closure S) ≤ Nat.card ψ.ker * Nat.card ψ.range :=
          Nat.mul_le_mul h1 h2
      _ = Nat.card B := hcard
  · exact fun s hs => ⟨y ⟨s, hs⟩, Subgroup.subset_closure (Or.inl ⟨_, rfl⟩), hyφ ⟨s, hs⟩⟩

@[expose] def torsionOf (H : Subgroup Y) (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (p : ℕ) :
    Subgroup Y where
  carrier := {y | y ∈ H ∧ y ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haH, hap⟩ ⟨hbH, hbp⟩
    refine ⟨H.mul_mem haH hbH, ?_⟩
    rw [(show Commute a b from hH a haH b hbH).mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨H.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨haH, hap⟩
    exact ⟨H.inv_mem haH, by rw [inv_pow, hap, inv_one]⟩

theorem weylFive_of_cover [Finite Y] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {z : Y} (hz : z ∈ φ.ker)
    (hz1 : z ≠ 1) (hzp : z ^ 5 = 1) (S : Set T) (hSp : ∀ s ∈ S, s ^ 5 = 1)
    (hSinv : ∀ s ∈ S, ∃ g : T, g * s * g⁻¹ = s⁻¹)
    (hF : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ,
      x * y = y * x)
    (hcard : 5 ^ 3 ≤ Nat.card (Subgroup.closure S))
    {w₃ w₅ : T} (hw₃ : ∀ d ∈ Subgroup.closure S, w₃ * d * w₃⁻¹ ∈ Subgroup.closure S)
    (hw₃' : ∀ d ∈ Subgroup.closure S, w₃⁻¹ * d * w₃ ∈ Subgroup.closure S) (hw₃c : w₃ ^ 3 = 1)
    {s₃ : T} (hs₃ : s₃ ∈ S) (hs₃m : w₃ * s₃ * w₃⁻¹ ≠ s₃)
    (hw₅ : ∀ d ∈ Subgroup.closure S, w₅ * d * w₅⁻¹ ∈ Subgroup.closure S)
    (hw₅' : ∀ d ∈ Subgroup.closure S, w₅⁻¹ * d * w₅ ∈ Subgroup.closure S) (hw₅c : w₅ ^ 5 = 1)
    {s₅ : T} (hs₅ : s₅ ∈ S) (hs₅m : w₅ * s₅ * w₅⁻¹ ≠ s₅) : WeylFive Y := by
  classical
  obtain ⟨B, hBle, hBp, hBc, hBcard, hBlift⟩ := exists_elemAbelian_card_ge_comap hφ hker hodd
    Nat.prime_five S hSp hSinv hF hz hz1 hzp
  set D : Subgroup T := Subgroup.closure S with hD
  set Ep : Subgroup Y := D.comap φ with hEp
  set Ω : Subgroup Y := torsionOf Ep hF 5 with hΩ
  have hBΩ : B ≤ Ω := fun b hb => ⟨hBle hb, hBp b hb⟩
  have hclosed : ∀ (n : Y) (w : T), φ n = w → (∀ d ∈ D, w * d * w⁻¹ ∈ D) →
      ∀ y ∈ Ω, n * y * n⁻¹ ∈ Ω := by
    rintro n w hn hw y ⟨hyEp, hyp⟩
    refine ⟨?_, ?_⟩
    · show φ (n * y * n⁻¹) ∈ D
      rw [map_mul, map_mul, map_inv, hn]
      exact hw _ hyEp
    · rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  have hnorm : ∀ (n : Y) (w : T), φ n = w → (∀ d ∈ D, w * d * w⁻¹ ∈ D) →
      (∀ d ∈ D, w⁻¹ * d * w ∈ D) → n ∈ Subgroup.normalizer (Ω : Set Y) := by
    intro n w hn hw hw'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hclosed n w hn hw y, fun hy => ?_⟩
    have h1 := hclosed n⁻¹ w⁻¹ (by rw [map_inv, hn]) (fun d hd => by rw [inv_inv]; exact hw' d hd) _ hy
    simpa [mul_assoc] using h1
  refine ⟨Ω, fun b hb => hb.2, fun a ha b hb => hF a ha.1 b hb.1, ?_, ?_, ?_⟩
  · calc 5 ^ 4 = 5 * 5 ^ 3 := by norm_num
      _ ≤ 5 * Nat.card D := Nat.mul_le_mul_left _ hcard
      _ ≤ Nat.card B := hBcard
      _ ≤ Nat.card Ω := Subgroup.card_le_of_le hBΩ
  · obtain ⟨n₃, hn₃⟩ := hφ w₃
    refine ⟨n₃, hnorm n₃ w₃ hn₃ hw₃ hw₃', hker (MonoidHom.mem_ker.2 (by rw [map_pow, hn₃, hw₃c])), ?_⟩
    obtain ⟨y, hyB, hyφ⟩ := hBlift s₃ hs₃
    refine ⟨y, hBΩ hyB, fun h => hs₃m ?_⟩
    have := congrArg φ h
    rwa [map_mul, map_mul, map_inv, hn₃, hyφ] at this
  · obtain ⟨n₅, hn₅⟩ := hφ w₅
    refine ⟨n₅, hnorm n₅ w₅ hn₅ hw₅ hw₅', hker (MonoidHom.mem_ker.2 (by rw [map_pow, hn₅, hw₅c])), ?_⟩
    obtain ⟨y, hyB, hyφ⟩ := hBlift s₅ hs₅
    refine ⟨y, hBΩ hyB, fun h => hs₅m ?_⟩
    have := congrArg φ h
    rwa [map_mul, map_mul, map_inv, hn₅, hyφ] at this

end Lift

end CFSG.RankThree.PartOne.K159W
