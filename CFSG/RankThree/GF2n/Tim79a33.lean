module

public import CFSG.RankThree.GF2n.Tim79aSUModelFacts
public import CFSG.RankThree.GF2n.Tim79aTIPairing
public import CFSG.RankThree.GF2n.Tim79aSec33TI
public import CFSG.RankThree.GF2n.Tim79aSec33Beta
public import CFSG.RankThree.GF2n.Tim79aSec33Count
public import CFSG.RankThree.GF2n.Tim79aSec24Tilde

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

theorem tim79a33TildeStatement_of_bricks (hU : UnitaryRootStatement) (hBeta : Sec3BetaStatement)
    : Tim79a33TildeStatement := by
  have hTI := CFSG.RankThree.GF2n.Tim79a.tiEndStatement_holds
  have hBase := sec3BaseStatement_holds
  have hTIb := sec3TIStatement_holds
  have hEx := sec3ExistsStatement_holds
  have hCount := sec33CountStatement_holds
  have hCen := sec3CenterStatement_holds
  intro G _ _ M V Q P H hs h4 hb hS
  have hs3 : Sec3Setup M V Q P H := ⟨hs, hb, hS⟩
  have hs' : Sec33Setup M V Q P H := ⟨hs, h4, hb, hS⟩
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hUR : UnitaryRoot (XbarZ V H) (VZ V H) := by
    obtain ⟨f, hf, -, hT⟩ := h4
    exact ⟨f, hf, rootClassZ V H, hT, VZ_mem_rootClassZ V H⟩
  have hF : UnitaryRootFacts (XbarZ V H) (VZ V H) := hU _ _ hUR
  have hRF : RootFacts (XbarZ V H) (VZ V H) := hF.toRootFacts
  have hPF : PairFacts (XbarZ V H) (VZ V H) := hRF.toPairFacts
  obtain ⟨b1, b2, b3, b4, b5⟩ := hBase G M V Q P H hs3
  have hQM : Q ≤ M := hc.hQ ▸ (inSubgroup_pCore_two M).2.1
  have hPM : P ≤ M := hc.P_le_Q.trans hQM
  have hdata : TIPairData M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H) :=
    { VleP := hc.V_le_P
      PleM := hPM
      normV := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.normalizer_eq ▸ hm)
      normP := fun m hm => mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hm)
      maxAb := hc.maxAb
      PcentV := fun x hx v hv => (hc.commute_of_mem_P hx hv).symm
      PcommV := fun x hx y hy => hc.commutator_mem_V_of_mem_P hx hy
      ti := hc.ti
      AleV := inf_le_left
      AjleV := fun y _ => inf_le_left
      AjleP := b1
      AjeqP := hTIb G M V Q P H hs3 hPF
      Ajcard := b2
      Ajcomm := b3
      EleP := inf_le_left
      AjleE := b5
      abelL := b4
      moves := hEx G M V Q P H hs3 hPF
      beta := hBeta G M V Q P H hs3 hPF }
  obtain ⟨b, hbP, hbL, hbc⟩ := hTI G M V P (V ⊓ wOf V H) (Eof V H P) (Ycomm V H) (Aof V H)
    hdata (hCount G M V Q P H hs' hF)
  exact hbL (hCen G M V Q P H hs3 hRF b hbP hbc)

end CFSG.RankThree.GF2n.Tim79a

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

theorem tim79a33TildeStatement_of_gen (hG : SUModelGen) : Tim79a33TildeStatement :=
  tim79a33TildeStatement_of_bricks
    (unitaryRootStatement_of_models suModelDisjoint_holds suModelMoves_holds suModelCenter_holds
      suModelCard_holds suModelCount_holds hG)
    sec3BetaStatement_holds

end CFSG.RankThree.GF2n.Tim79a
