module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelSylB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup

theorem s16h_orth3_sylow_fixed {T : Subgroup (MulAut Orth3)}
    (hT : T ≤ Subgroup.normalizer (orth3L : Set (MulAut Orth3)))
    (hT2 : IsPGroup 2 ↥T) : ∃ v : Orth3, v ∉ orth3Z ∧ ∀ t ∈ T, t v = v := by
  classical
  let α := {v : Orth3 // v ∈ s16h_orth3Sing}
  have hsmul : ∀ (t : ↥T) (v : α), (t : MulAut Orth3) v ∈ s16h_orth3Sing := by
    intro t v
    exact s16h_orth3Sing_normalizer_mem (hT t.2) v.2
  letI : MulAction ↥T α :=
    { smul := fun t v => ⟨(t : MulAut Orth3) v, hsmul t v⟩
      one_smul := by
        intro v
        apply Subtype.ext
        rfl
      mul_smul := by
        intro a b v
        apply Subtype.ext
        rfl }
  have hcard : Nat.card α = 15 := by
    haveI : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card]
    change Fintype.card ↥s16h_orth3Sing = 15
    rw [Fintype.card_coe, s16h_orth3Sing_card]
  have hnotdvd : ¬ 2 ∣ Nat.card α := by
    rw [hcard]
    decide
  obtain ⟨x, hx⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card α hnotdvd
  obtain ⟨v, hv⟩ := x
  refine ⟨v, s16h_orth3Sing_not_mem_Z hv, ?_⟩
  intro t ht
  have h := (MulAction.mem_fixedPoints (M := ↥T) (α := α)).mp hx ⟨t, ht⟩
  have h' := congrArg Subtype.val h
  change (t : MulAut Orth3) v = v at h'
  exact h'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
