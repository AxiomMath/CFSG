module

public import CFSG.Quasithin.Recognition.L34CIT.TorusOrbits
public import CFSG.Quasithin.Recognition.L34CIT.Order
public import CFSG.Quasithin.Recognition.L34CIT.Plane

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

namespace Config

theorem oppositeCount (C : Config A) [Finite A] : C.OppositeCount := by
  classical
  obtain ⟨k, hkB, hk⟩ := C.exists_orderOf_eq_three
  let j := {P : Sylow 2 A |
    (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥ ∧ k • P = P}.ncard
  have hOpp : {P : Sylow 2 A |
      (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥}.ncard = 64 * j :=
    C.ncard_opposite_eq_mul hkB hk
  have hj : j ≤ 5 := C.ncard_opposite_fixed_le hkB hk
  have hmeets : ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥} :
      Set (Sylow 2 A)).ncard = 41 := C.ncard_meets
  have hdisj : Disjoint {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥}
      {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥} := by
    rw [Set.disjoint_left]
    intro P h1 h2
    exact h2 h1
  have hunion : ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥} ∪
      {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) ≠ ⊥}) = Set.univ := by
    ext P
    by_cases h : (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥
    · simp [h]
    · simp [h]
  have hpart := Set.ncard_union_eq hdisj
  rw [hunion, Set.ncard_univ, hmeets, hOpp] at hpart
  have h5A : 5 ∣ Nat.card A := by
    have h := Subgroup.card_subgroup_dvd_card (normalizer (C.L : Set A))
    rw [C.card_normalizer_L] at h
    exact dvd_trans (by norm_num : 5 ∣ 960) h
  have hA : Nat.card A = Nat.card (Sylow 2 A) * 192 := by
    rw [C.card_eq_card_sylow_mul, C.card_normalizer_T]
  have h5Syl : 5 ∣ Nat.card (Sylow 2 A) :=
    Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 5 192) (by rwa [← hA])
  have h5j : 5 ∣ 64 * j + 41 := by
    rw [← hpart]
    exact h5Syl
  have hj1 : j = 1 := by
    interval_cases j <;> norm_num at h5j
    rfl
  change {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = ⊥}.ncard = 64
  rw [hOpp, hj1]

theorem card_eq (C : Config A) [Finite A] : Nat.card A = 20160 :=
  C.card_eq_of_opposite C.oppositeCount

end Config

theorem typeL34_of_config
    {A : Type} [Group A] [Finite A] (C : Config A) :
    CFSG.ComponentClassification.AS81.TypeL34 A :=
  C.typeL34 C.card_eq

end CFSG.Quasithin.L34CIT
