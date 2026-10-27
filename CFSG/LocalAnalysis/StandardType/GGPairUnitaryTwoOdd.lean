module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuTwo
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPair
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggPairConcl_of_esu_two_odd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ X ∈ 𝒦) (hodd : Odd (Nat.card (Subgroup.center ↥X)))
    (h : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrA' : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hne : r ≠ r') :
    GGPairConcl Bs X r r' := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hBs : IsElemAbelian p Bs := ggRouteCfg_isElemAbelian hcfg
  have hX' : X = L ∨ ∃ y : G, GGNbr p B x D J y X :=
    hX.imp_right (hcfg.2.2.2.1.2 X)
  obtain ⟨lab, K, hKf, hKfin, hKchar, f, n, ψ, -, -, -, hcard, hn, hker, hrange, hdvd, hacts, -⟩ :=
    ggNSLie_cover_of_esu_odd (fun _ _ hl => hl.1) hodd h
  obtain ⟨ψ', hker', -, hpos'⟩ :=
    ggUnitaryCover_position_nbr hcfg hX' hcard hn hker hrange hdvd hacts
  exact ggPairConcl_of_unitary_position hp hp2 hBs hcard hn hker' hpos' hrA hrA' hr hr' hne

end CFSG.StandardType

end
