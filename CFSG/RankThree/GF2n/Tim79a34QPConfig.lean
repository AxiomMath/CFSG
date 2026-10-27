module

public import CFSG.RankThree.GF2n.Tim79a34Hauptsatz
public import CFSG.RankThree.GF2n.Tim79a34SpOrder
public import CFSG.RankThree.GF2n.Tim79a34IW

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

theorem qPCfgExistsStatement_holds (hN : NaturalModuleStatement) (hI : Sec34IWStatement) :
    QPCfgExistsStatement := by
  intro G _ _ M V Q P H hH hZ hn hQP
  obtain ⟨n', hn3, ⟨e⟩⟩ := hn
  obtain ⟨n, Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTΦ⟩, hpoint⟩ := hN G M V Q P H hH hZ
  let e2 : Xbar V H ≃* XbarZ V H := MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hZ)
  have hnn : n = n' := statedSp_gf2_rank_eq (Φ.trans (e2.trans e.symm))
  refine ⟨n, Φ, ψ, a, T, ⟨?_⟩⟩
  exact
    { hyp := hH
      centre := hZ
      iw := hI G M V Q P H hH hZ
      qp := hQP
      three := by omega
      nat := ⟨hequiv, hpoint⟩
      ne := ha
      trans := hT
      point := hTΦ }

end CFSG.RankThree.GF2n.Tim79a
