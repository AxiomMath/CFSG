module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bar
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

theorem inEP_top_of_inE_of_solvable {Q : Type} [Group Q] [Finite Q] [Group.IsSolvable Q]
    (h : CFSG.Quasithin.E1.InE 1 (⊤ : Subgroup Q)) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InEP 1 (⊤ : Subgroup Q) := by
  classical
  intro T hT Ω hΩ hne hnt
  have hTs : CFSG.Quasithin.IsSylowIn 2 T ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T) (K := ⊤)).mp hT
  have hgen := h T hTs Ω hΩ
  have hle : CFSG.Quasithin.E1.eGen 1 (⊤ : Subgroup Q) T Ω ≤
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP 1 (⊤ : Subgroup Q) T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have : Group.IsSolvable ↥K := inferInstance
    exact le_iSup₂_of_le A hA (le_iSup_of_le hAT
      (le_iSup₂_of_le K ⟨hK.1, hK.2.1, hK.2.2.1,
        Or.inl (CFSG.Quasithin.E1.isE_eOne_of_isSolvable hK inferInstance)⟩ le_rfl))
  exact top_le_iff.mp (hgen.symm.trans_le (sup_le_sup hle le_rfl))

theorem inFSq_one_of_isSolvable_of_calNIn {Q : Type} [Group Q] [Finite Q] {H T M : Subgroup Q}
    (hT : CFSG.Quasithin.IsSylowIn 2 T H) (hU : calNIn H T = {M})
    (hH : Group.IsSolvable ↥H) : InFSq 1 H := by
  classical
  have : Group.IsSolvable ↥H := hH
  let Q' := Bar2 H
  have : Group.IsSolvable Q' := by
    dsimp only [Q']
    infer_instance
  have hO2 : CFSG.pCore 2 Q' = ⊥ := pCore_two_bar2_eq_bot H
  have hInE : CFSG.Quasithin.E1.InE 1 (⊤ : Subgroup Q') :=
    CFSG.Quasithin.E1.inE_one_top_of_isSolvable (Nat.card Q') Q' le_rfl inferInstance
  have hInEP : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InEP 1 (⊤ : Subgroup Q') :=
    inEP_top_of_inE_of_solvable hInE
  refine inF_top_of_inEP 1 hInEP ?_ hO2
  exact ⟨barImage H T, isSylowOf_two_iff_isSylowIn.mpr (isSylowIn_barImage hT),
    hasUniqueMaxOver_barImage hT hU⟩

end CFSG.LocalAnalysis.WeakClosure81

end
