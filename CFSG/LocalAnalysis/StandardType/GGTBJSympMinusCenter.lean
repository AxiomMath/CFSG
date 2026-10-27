module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueBound

public section

namespace CFSG.StandardType.SympMinus

open CFSG CFSG.Assembly

theorem sympMinus_center_two
    {Y : Type} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {m : ℕ} (hm : 3 ≤ m) (e : Y ⧸ Subgroup.center Y ≃* LargeEvenProj (LargeEvenSpGroup K m)) :
    IsPGroup 2 (Subgroup.center Y) ∧ (4 ≤ m → Subgroup.center Y = ⊥) := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hbot : 4 ≤ m → Subgroup.center Y = ⊥ := fun h4 =>
    center_eq_bot_of_quot_psp_even hY hK' le_rfl (by omega) (fun h => by omega) e
  refine ⟨?_, hbot⟩
  by_cases h4 : 4 ≤ m
  · exact IsPGroup.of_card (n := 0) (by simp [hbot h4])
  · obtain rfl : m = 3 := by omega
    have hadm : CFSG.Open.StatedLieAdmissible .PSp 3 2 1 :=
      ⟨Nat.prime_two, le_rfl, by norm_num, fun h => by
        have h1 : (3 : ℕ) = 2 := congrArg Prod.fst h
        omega⟩
    have hX : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv e.symm
        (CFSG.LieType.Steinberg.CentralExt.SpClosed.lieModel_statedProj_sp hK' hadm)
    haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hY
    have hle := CFSG.EvenSmallLie.SympSix.card_ker_le_two hX
      (QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective (N := Subgroup.center Y)) (by rw [QuotientGroup.ker_mk'])
    rw [QuotientGroup.ker_mk'] at hle
    have hpos : 0 < Nat.card ↥(Subgroup.center Y) := Nat.card_pos
    obtain h1 | h2 : Nat.card ↥(Subgroup.center Y) = 1 ∨ Nat.card ↥(Subgroup.center Y) = 2 := by
      omega
    · exact IsPGroup.of_card (n := 0) (by simp [h1])
    · exact IsPGroup.of_card (n := 1) (by simp [h2])

end CFSG.StandardType.SympMinus

end
