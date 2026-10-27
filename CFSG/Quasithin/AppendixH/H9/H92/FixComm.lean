module

public import CFSG.Quasithin.AppendixH.H9.H92.RadCard
public import CFSG.Quasithin.AppendixH.H9.H92.FixComm.SplitSubgroup
public import CFSG.Quasithin.AppendixH.H9.H92.FixComm.FixedAndCommutator

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem fixV_commV_radV1_hyperplane (U : Subgroup (PairN 5)) (hU : U ≤ V1n 5) (hr : rk ↥U = 3)
    (A : Subgroup (MulAut (PairN 5))) (hA : A ≤ RadV1 5 U)
    (hcard : Nat.card A * 2 = Nat.card (RadV1 5 U)) :
    fixV A = commV A ∧ commV A = fixV (RadV1 5 U) ∧ fixV (RadV1 5 U) = commV (RadV1 5 U) ∧
      commV (RadV1 5 U) = U ⊔ (V2n 5 ⊓ perpN 5 U) ∧ rk ↥(U ⊔ (V2n 5 ⊓ perpN 5 U)) = 5 := by
  have hD : Module.finrank (ZMod 2) (v1Space 5 U) = 3 := by
    rw [finrank_v1Space_eq_rk U hU]
    exact hr
  have h64 : Nat.card ↥(RadV1 5 U) = 64 := card_radV1 U hU (Or.inr hr)
  have hA32 : 32 ≤ Nat.card ↥A := by omega
  obtain ⟨hfA, hcA⟩ := fixV_commV_eq_splitSub hD hA hA32
  obtain ⟨hfR, hcR⟩ := fixV_commV_eq_splitSub hD (le_refl (RadV1 5 U)) (by omega)
  have hZ := splitSub_dotPerp_eq hU
  have hrk := rk_splitSub_dotPerp 5 (v1Space 5 U)
  refine ⟨hfA.trans hcA.symm, hcA.trans hfR.symm, hfR.trans hcR.symm, hcR.trans hZ, ?_⟩
  rw [← hZ]
  exact hrk

end CFSG.ASVolI.ChH
