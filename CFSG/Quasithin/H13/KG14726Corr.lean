module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.KG14726Core

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Quasithin

section ElementsOfB

variable {Y : Type*} [Group Y] {B : Subgroup Y}

theorem not_prime_dvd_two_pow_mul {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℕ) :
    ¬ p ∣ 2 ^ a * 27 := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at h
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega

end ElementsOfB

theorem false_of_surjective_prime {X W : Type*} [Group X] [Group W]
    {B : Subgroup (MulAut X)} (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27) (ψ : X →* W)
    (hψ : Function.Surjective ψ) (hZ : ∀ w ∈ center W, w ^ 3 = 1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {x : X} (hxB : MulAut.conj x ∈ B) (hx : orderOf (ψ x) = p) : False := by
  obtain ⟨a, ha⟩ := hB
  set N := 2 ^ a * 27 with hN
  have hpow : MulAut.conj x ^ N = 1 := by
    have h : (⟨MulAut.conj x, hxB⟩ : ↥B) ^ Nat.card B = 1 := pow_card_eq_one'
    rw [ha] at h
    exact congrArg Subtype.val h
  have hxN : x ^ N ∈ center X := by
    rw [← ker_conj_eq_center, MonoidHom.mem_ker, map_pow]
    exact hpow
  have hψN : ψ x ^ N ∈ center W := by
    rw [mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := hψ w
    rw [← map_pow, ← map_mul, ← map_mul, (mem_center_iff.mp hxN) y]
  have hcop : (orderOf (ψ x)).Coprime N := by
    rw [hx]
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (not_prime_dvd_two_pow_mul hp hp5 a))).symm
  have hord : orderOf (ψ x ^ N) = p := by
    rw [Nat.Coprime.orderOf_pow hcop, hx]
  have h3 : orderOf (ψ x ^ N) ∣ 3 := orderOf_dvd_of_pow_eq_one (hZ _ hψN)
  rw [hord] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

section Inner

variable {X : Type*} [Group X] {A B : Subgroup (MulAut X)}

theorem relIndex_inn_dvd [Finite X] (hA : (MulAut.conj : X →* MulAut X).range ≤ A)
    (hBA : B ≤ A) :
    B.relIndex (MulAut.conj : X →* MulAut X).range ∣ (B.subgroupOf A).index := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have : Finite (MulAut X) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have : I.Normal := inn_normal
  have hle : B ≤ B ⊔ I := le_sup_left
  have hsup : B ⊔ I ≤ A := sup_le hBA hA
  have h1 : I.relIndex (B ⊔ I) = I.relIndex B := Subgroup.relIndex_sup_right B I
  have hcard1 : Nat.card ↥(B ⊔ I) = I.relIndex B * Nat.card I := by
    rw [← h1, ← Subgroup.relIndex_mul_card I (B ⊔ I), inf_eq_left.mpr le_sup_right]
  have hcard2 : Nat.card B = I.relIndex B * Nat.card ↥(I ⊓ B) := by
    rw [Subgroup.relIndex_mul_card I B]
  have hcard3 : Nat.card I = B.relIndex I * Nat.card ↥(B ⊓ I) := by
    rw [Subgroup.relIndex_mul_card B I]
  have hpos : 0 < Nat.card ↥(B ⊓ I) := Nat.card_pos
  have hpos2 : 0 < I.relIndex B := by
    have hB0 : 0 < Nat.card B := Nat.card_pos
    rw [hcard2] at hB0
    exact Nat.pos_of_mul_pos_right hB0
  have hBsup : B.relIndex (B ⊔ I) = B.relIndex I := by
    have h4 := Subgroup.relIndex_mul_card B (B ⊔ I)
    rw [inf_eq_left.mpr hle, hcard1, hcard2, hcard3, inf_comm] at h4
    have h5 : B.relIndex (B ⊔ I) * (I.relIndex B * Nat.card ↥(B ⊓ I)) =
        B.relIndex I * (I.relIndex B * Nat.card ↥(B ⊓ I)) := by
      rw [h4]; ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos2 hpos) h5
  have h6 : B.relIndex (B ⊔ I) * (B ⊔ I).relIndex A = B.relIndex A :=
    Subgroup.relIndex_mul_relIndex B (B ⊔ I) A hle hsup
  rw [← hBsup]
  exact ⟨_, h6.symm⟩

theorem odd_relIndex_inn [Finite X] (hA : (MulAut.conj : X →* MulAut X).range ≤ A)
    (hBA : B ≤ A) (hBi : ¬ 2 ∣ (B.subgroupOf A).index) :
    ¬ 2 ∣ B.relIndex (MulAut.conj : X →* MulAut X).range :=
  fun h => hBi (h.trans (relIndex_inn_dvd hA hBA))

theorem twentyseven_dvd_card_inf_inn (hB : ∃ a : ℕ, Nat.card B = 2 ^ a * 27)
    (hin : ∀ b ∈ B, b ^ 27 = 1 → b ∈ (MulAut.conj : X →* MulAut X).range) :
    27 ∣ Nat.card ↥(B ⊓ (MulAut.conj : X →* MulAut X).range) := by
  obtain ⟨a, ha⟩ := hB
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [ha]; positivity)
  have h27 : 3 ^ 3 ∣ Nat.card B := ⟨2 ^ a, by rw [ha]; ring⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 3 h27
  have hle : P.map B.subtype ≤ B ⊓ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_inf.mpr ⟨y.2, hin _ y.2 ?_⟩
    have hy27 : (⟨y, hy⟩ : ↥P) ^ 27 = 1 := by
      have h : (⟨y, hy⟩ : ↥P) ^ Nat.card P = 1 := pow_card_eq_one'
      rwa [hP] at h
    have := congrArg (fun z : ↥P => ((z : ↥B) : MulAut X)) hy27
    simpa using this
  have hcard : Nat.card ↥(P.map B.subtype) = 27 := by
    rw [card_map_of_injective B.subtype_injective, hP]
    norm_num
  rw [← hcard]
  exact card_dvd_of_le hle

end Inner

theorem card_le_factorial_index {G : Type*} [Group G] [IsSimpleGroup G] {H : Subgroup G}
    (hH : H ≠ ⊤) [H.FiniteIndex] : Nat.card G ≤ H.index.factorial := by
  have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker]
    rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ Subgroup.normalCore_le H)) hH
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_perm, ← Subgroup.index] at this

end CFSG.Quasithin.H13.KG14726

end
