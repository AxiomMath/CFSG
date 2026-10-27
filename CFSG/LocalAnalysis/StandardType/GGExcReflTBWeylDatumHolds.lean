module

public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggExcReflTBInputQFourOn_of_weylDatum {S : ℕ → LargeEvenLabel → Prop}
    (hD : GGExcReflTBWeylDatumQFourOn S) (hJ : GGTBJNoncommReflOn S) :
    GGExcReflTBInputQFourOn S := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL _
  obtain ⟨T⟩ := hD G p B Bs x L D J hHyp hq hN hL
  obtain ⟨a, ha, b, hb, hra, hrb, hab⟩ := hJ G p B Bs x L D J hHyp hq hN hL
  have hJL : J ≤ L := hHyp.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  have hRC : GGReflConjSimple p (ggAutomizer L Bs) T.simple := by
    classical
    exact ggReflConjSimple_of_weylMatrix hp2 T.isWeyl T.three_le_card T.isCartan T.model
      T.simple T.coroot T.root T.pairing T.simple_apply T.automizer_eq
  obtain ⟨c, hcL, i, rfl⟩ := hRC a (ggAutomizer_mono Bs hJL ha) hra
  obtain ⟨c', hcL', j, rfl⟩ := hRC b (ggAutomizer_mono Bs hJL hb) hrb
  exact ⟨⟨T.Λ, T.coxeter, T.cartan, T.V, T.model, T.simple, T.coroot, T.root, T.isWeyl,
    T.isCartan, T.three_le_card, T.pairing, T.simple_apply, T.automizer_eq, T.tbHyp,
    ⟨i, j, c, c', hcL, hcL', ha, hb, hab⟩⟩⟩

end CFSG.StandardType

end
