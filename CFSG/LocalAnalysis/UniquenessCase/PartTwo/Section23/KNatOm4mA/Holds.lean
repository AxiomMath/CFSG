module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin.H13.H11M (SigInv NH LH VH)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (NatOmegaMinus)
open CFSG.Quasithin
open NatOm4mA

theorem kNatOm4mA_holds : KNatOm4mA := by
  intro W _ _ H X k _hΩ hN _hHX hXN
  have hk : 1 ≤ k := one_le_of_natOmegaMinus hN
  obtain ⟨F, hField, hFin, hChar, hF⟩ := exists_field_card hk
  letI : Field F := hField
  letI : Fintype F := hFin
  haveI : CharP F 2 := hChar
  have hσ : SigInv k F := CFSG.Quasithin.JonesParshall.sig_sig hF
  obtain ⟨E, hE⟩ := exists_equiv_vh hN hk hF hσ
  have hX' : X.map (CFSG.Quasithin.H.congrHom E) ≤ NH hσ := by
    have h := map_le_normalizer_map E hXN
    rw [hE] at h
    exact h
  have h1 : E3.aParam (X.map (CFSG.Quasithin.H.congrHom E)) ≤ k :=
    aParam_le_of_le_normalizer hσ hk hF hX'
  rw [← CFSG.Quasithin.H.aParam_map_congrHom E X]
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.UC22
