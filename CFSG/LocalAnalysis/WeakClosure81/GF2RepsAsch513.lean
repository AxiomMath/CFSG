module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.Quasithin.Background.KG82CoverCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (W4Lem4_10 W4Lem4_11)
open CFSG.Blueprint (LieModel)

theorem relPPrimeCore_le_ambient (p : ℕ) {Q : Type} [Group Q] (H : Subgroup Q) :
    relPPrimeCore p H ≤ H :=
  sSup_le fun _ hN => hN.1

theorem normal_subgroupOf_relPPrimeCore (p : ℕ) {Q : Type} [Group Q] (H : Subgroup Q) :
    ((relPPrimeCore p H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (relPPrimeCore_le_ambient p H)]
  intro x k hx hk
  have key : relPPrimeCore p H ≤ (relPPrimeCore p H).comap (MulAut.conj k).toMonoidHom := by
    refine sSup_le fun N hN => ?_
    intro n hn
    have h1 : k * n * k⁻¹ ∈ N := (Subgroup.normal_subgroupOf_iff hN.1).mp hN.2.1 n k hn hk
    exact le_sSup hN h1
  simpa using key hx

end CFSG.LocalAnalysis.WeakClosure81
