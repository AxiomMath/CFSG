module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.K159

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem exists_lift_pow_eq_one [Finite Y] (hker : φ.ker ≤ Subgroup.center Y)
    (hodd : Odd (Nat.card φ.ker)) {p : ℕ} {s : T} (hs : s ^ p = 1) (g : T) (hg : g * s * g⁻¹ = s⁻¹)
    (hφ : Function.Surjective φ) : ∃ y : Y, φ y = s ∧ y ^ p = 1 := by
  obtain ⟨ŝ, hŝ⟩ := hφ s
  obtain ⟨ĝ, hĝ⟩ := hφ g
  set z : Y := ĝ * ŝ * ĝ⁻¹ * ŝ with hz
  have hzker : z ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hz]
    simp only [map_mul, map_inv, hŝ, hĝ, hg, inv_mul_cancel]
  have hzc : z ∈ Subgroup.center Y := hker hzker
  have hconj : ĝ * ŝ * ĝ⁻¹ = z * ŝ⁻¹ := by rw [hz]; group
  set w : Y := ŝ ^ p with hw
  have hwker : w ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hw, map_pow, hŝ, hs]
  have hwc : w ∈ Subgroup.center Y := hker hwker
  have hw2 : w ^ 2 = z ^ p := by
    have h1 : ĝ * w * ĝ⁻¹ = w := by
      have := Subgroup.mem_center_iff.1 hwc ĝ
      calc ĝ * w * ĝ⁻¹ = w * ĝ * ĝ⁻¹ := by rw [this]
        _ = w := by group
    have h2 : ĝ * w * ĝ⁻¹ = (z * ŝ⁻¹) ^ p := by
      rw [hw, ← hconj, ← conj_pow]
    have h3 : (z * ŝ⁻¹) ^ p = z ^ p * (ŝ ^ p)⁻¹ := by
      have hcomm : Commute z ŝ⁻¹ := (Subgroup.mem_center_iff.1 hzc ŝ⁻¹).symm
      rw [hcomm.mul_pow, inv_pow]
    rw [h1, h3, ← hw] at h2
    have h4 : w * w = z ^ p := by
      calc w * w = z ^ p * w⁻¹ * w := by rw [← h2]
        _ = z ^ p := by group
    rw [pow_two]
    exact h4
  obtain ⟨n, hn⟩ := hodd
  have hnk : Nat.card φ.ker = 2 * n + 1 := hn
  set c : Y := z ^ (n + 1) with hc
  have hwpow : w ^ (2 * n + 1) = 1 := by
    have := pow_card_eq_one' (G := φ.ker) (x := (⟨w, hwker⟩ : φ.ker))
    rw [hnk] at this
    exact congrArg Subtype.val this
  have hwc' : w = c ^ p := by
    calc w = w ^ (2 * (n + 1)) := by
          have : w ^ (2 * (n + 1)) = w ^ (2 * n + 1) * w := by
            rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ]
          rw [this, hwpow, one_mul]
      _ = (w ^ 2) ^ (n + 1) := by rw [pow_mul]
      _ = (z ^ p) ^ (n + 1) := by rw [hw2]
      _ = (z ^ (n + 1)) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hcker : c ∈ φ.ker := φ.ker.pow_mem hzker _
  have hcc : c ∈ Subgroup.center Y := hker hcker
  refine ⟨ŝ * c⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, hŝ, (MonoidHom.mem_ker.1 hcker), inv_one, mul_one]
  · have hcomm : Commute ŝ c⁻¹ := (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hcc) ŝ)
    rw [hcomm.mul_pow, inv_pow, ← hw, hwc', mul_inv_cancel]

theorem commute_of_mem_closure' {S : Set Y} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) {x y : Y}
    (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S) : Commute x y := by
  have hyS : ∀ s ∈ S, Commute s y := by
    intro s hs
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {s} :=
      (Subgroup.closure_le _).2 fun t ht =>
        Subgroup.mem_centralizer_singleton_iff.2 (hS t ht s hs).eq
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {y} :=
    (Subgroup.closure_le _).2 fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hyS s hs).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)

theorem pow_eq_one_of_mem_closure' {S : Set Y} (hS : ∀ s ∈ S, ∀ t ∈ S, Commute s t) {n : ℕ}
    (hSn : ∀ s ∈ S, s ^ n = 1) {x : Y} (hx : x ∈ Subgroup.closure S) : x ^ n = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hSn s hs
  | one => exact one_pow n
  | mul a b ha hb iha ihb =>
    rw [(commute_of_mem_closure' hS ha hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem exists_elemAbelian_card_ge [Finite Y] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {p : ℕ} (hp : p.Prime)
    (S : Set T) (hSp : ∀ s ∈ S, s ^ p = 1) (hSinv : ∀ s ∈ S, ∃ g : T, g * s * g⁻¹ = s⁻¹)
    (hF : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ, x * y = y * x)
    {z : Y} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p * Nat.card (Subgroup.closure S) ≤ Nat.card B := by
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
  refine ⟨B, fun b hb => pow_eq_one_of_mem_closure' hGcomm hGp hb,
    fun a ha b hb => (commute_of_mem_closure' hGcomm ha hb).eq, ?_⟩
  have hzB : z ∈ B := Subgroup.subset_closure (Or.inr rfl)
  let ψ : B →* T := φ.comp B.subtype
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

theorem closure_range_ofAdd_single {p : ℕ} [NeZero p] {m : ℕ} :
    Subgroup.closure (Set.range fun j : Fin m =>
      (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) : Multiplicative (Fin m → ZMod p))) =
        ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have h : a = ∏ j : Fin m, (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
      Multiplicative (Fin m → ZMod p)) ^ (Multiplicative.toAdd a j).val := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    funext i
    simp only [toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj.symm]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h]
  exact Subgroup.prod_mem _ fun j _ =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _

end CFSG.RankThree.PartOne.K159
