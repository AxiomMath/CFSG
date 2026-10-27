module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixCard
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.QuasithinUnique CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_of_card {S H : Subgroup G} (hSH : S ≤ H) (hp : IsPGroup 2 S) {m : ℕ}
    (hm : ¬ 2 ∣ m) (hc : Nat.card H = Nat.card S * m) : IsSylowTwoOf S H := by
  refine ⟨hSH, hp, ?_⟩
  have h := Subgroup.relIndex_mul_card S H
  rw [inf_of_le_left hSH, hc] at h
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h1 : S.relIndex H = m := Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  show ¬ 2 ∣ S.relIndex H
  rw [h1]
  exact hm

theorem isSylowTwoOf_of_le_of_le {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by
    rw [← h1]
    exact Dvd.dvd.mul_right hdvd _
  exact h2

end Generic

section J


variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)

@[expose] noncomputable def Jfix : Subgroup (Cm σ) :=
  (fieldActor σ δ).toMonoidHom.eqLocus (MonoidHom.id _)

theorem Ug_le_Jfix : Ug σ δ ≤ Jfix σ δ := inf_le_right

variable {e : ℕ} (he : 1 ≤ e) (hK : Nat.card K = (2 ^ (2 * e)) ^ 3)
  (hσ : ∀ c, σ.toRingHom c = c ^ 2 ^ (2 * e)) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include he hK hσ hδ in
theorem card_Jfix : Nat.card (Jfix σ δ) = (2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
    ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
  have hK6 : Nat.card K = 2 ^ (6 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  obtain ⟨-, hk0, hσ0, -, -, hJ, -⟩ :=
    even_triality_canonical_field_full_centralizer he K hK6 σ (fun c => hσ c) δ hδ
  have : Finite (fixSubfield δ) := Subtype.finite
  have hK0 : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by
    rw [hk0, ← pow_mul, mul_comm]
  have hσ0' : ∀ c, (fixSubfieldRestrict σ δ).toRingHom c = c ^ ((2 ^ e) ^ 2) := fun c => by
    refine Subtype.ext ?_
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ0, SubmonoidClass.coe_pow]
    calc σ (c : K) = (c : K) ^ 2 ^ (2 * e) := hσ (c : K)
      _ = (c : K) ^ ((2 ^ e) ^ 2) := by rw [← pow_mul, mul_comm]
  obtain ⟨hcard, -⟩ := triality_both_orientations_exact_finite_order 2 e Nat.prime_two he
    (fixSubfield δ) hK0 2 (Or.inr rfl) _ hσ0'
  have hJcard : Nat.card (trialityFieldImage σ δ) = (2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) *
      ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
    rw [trialityFieldImage, Subgroup.card_map_of_injective (baseChangeGL_injective _), hcard]
  rw [← hJcard, ← hJ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rfl

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : Even (2 ^ n) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  rw [Nat.odd_iff]
  rw [Nat.even_iff] at h2
  omega

include he hK hσ hδ in
theorem isSylowTwoOf_Ug_Jfix : IsSylowTwoOf (Ug σ δ) (Jfix σ δ) := by
  have hug := card_Ug σ δ he hK hσ hδ
  have hpow : (2 ^ (2 * e)) ^ 6 = (2 ^ e) ^ 12 := by
    rw [← pow_mul, ← pow_mul]
    ring_nf
  have hodd1 : Odd ((2 ^ e) ^ 2 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have hodd2 : Odd ((2 ^ e) ^ 6 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have hodd3 : Odd ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
    have h2 : Even (2 ^ e) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact ((h2.pow_of_ne_zero (by norm_num)).add (h2.pow_of_ne_zero (by norm_num))).add_one
  have hm : Odd (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1)) :=
    (hodd1.mul hodd2).mul hodd3
  refine isSylowTwoOf_of_card (Ug_le_Jfix σ δ) (IsPGroup.of_card (n := 12 * e) ?_)
    (m := ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) * ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1))
    hm.not_two_dvd_nat ?_
  · rw [hug, hpow, ← pow_mul]
    ring_nf
  · rw [card_Jfix σ δ he hK hσ hδ, hug, hpow]
    ring

end J

end CFSG.Quasithin.H13.F431.D4q.Out
