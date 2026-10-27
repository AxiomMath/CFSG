module

public import CFSG.Quasithin.H13.GoldschmidtA6RowsG2
public import CFSG.Quasithin.H13.GoldschmidtA6RowsCentG2Core

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6.GR

namespace G2

open CFSG.Quasithin.JonesParshall

theorem centLeafG2
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (fr : Frame V L ↥subG2 6) (hfr : ∀ γ, fr.mat γ = matG2 γ) :
    CentLeaf (modelHypG2 fr hfr) :=
  fun w h1 h2 h3 K hK hKP => leafG2 w h1 h2 h3 K hK hKP

end G2

end CFSG.Quasithin.H13.A6.GR

namespace CFSG.Quasithin.H13.A6

theorem factCentG2 :
    FactCentG2 := by
  intro V _ _ hV G L hB4 hrow v hcond hrk h9
  obtain ⟨Pg, hPL, hPC, hP9⟩ := exists_sub_nine h9
  obtain ⟨S, hS, hSv⟩ := hcond.sylow
  obtain ⟨fr, hfr⟩ := GR.G2.exists_frame_g2 hB4 hrow
  exact GR.cent_core fr (GR.G2.modelHypG2 fr hfr) (GR.G2.centLeafG2 fr hfr) hcond.sq hrk hS hSv
    hPL hPC hP9

end CFSG.Quasithin.H13.A6
