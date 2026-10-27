module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSExclDDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapter
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiag
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransport
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransportAux
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxBlock
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxPair

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem nsJA2_of_esuLabel
    (hC : GGSecFiveNSCornerInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hlab : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) p Bs L) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 := by
  obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hcard, hn, hker, hrange, hdvd, hacts, -⟩ :=
    ggNSLie_cover_of_esu (X := L) hlab
  have h : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_routeCfg (X := L) hcfg (Or.inl rfl) hcard hn hker hrange hdvd hacts
  obtain ⟨c, hd⟩ := ggNSLocal_exists_diag hC h
  have h' : GGNSLocalHyp p B Bs K f n (ψ.comp (MulAut.conj c).toMonoidHom) := h.comp_conj c
  have hrange' : (ψ.comp (MulAut.conj c).toMonoidHom).range = L := by
    rw [ggNSPosPD_range_comp_conj, hrange]
  obtain ⟨a, b, c', hab, hbc, hac, h1, h2⟩ := nsJA2_exists_triple hcfg h' hd hrange'
  exact nsJA2_of_pairBlocks_le h' hd hab hbc hac h1 h2

theorem ggSecFiveJA2PhanDInput_of_exclD
    (hC : GGSecFiveNSCornerInput) (hEnD : GGSecFiveNSEnnolaDInput) (hQ2D : GGSecFiveNSQ2DInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) : GGSecFiveJA2PhanDInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hsix i j hij hMij hnotOrb
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD.le_three (Or.inr hD) i j hij
  have hE := ggX_ennola_of_nonSplit hcfg hpres hle3 (Or.inl rfl) hns
  have h' : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))) ∨
        ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨
          (ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab))) p Bs L :=
    hE.mono' fun lab hl => by
      by_cases hesu : ggRowP_ESU p lab
      · by_cases hq : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)
        · exact Or.inr (Or.inl ⟨hesu, hq⟩)
        · exact Or.inl ⟨hesu, hq⟩
      · exact Or.inr (Or.inr ⟨hl, hesu⟩)
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact nsJA2_of_esuLabel hC hcfg h
  · rcases GGInnerDiagOnLabel.elim_or h with h | h
    · exact absurd h (hQ2D hFix hWA hLB hSP G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hsix i j
        hij hMij hnotOrb)
    · exact absurd h (hEnD G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD i j hij hMij hnotOrb)

end CFSG.StandardType

end
