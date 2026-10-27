module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType
public import CFSG.LocalAnalysis.StandardType.GGNSJoinFrameA
public import CFSG.LocalAnalysis.StandardType.GGNSJoinToralA
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAssemble
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2A

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan Matrix

open scoped MatrixGroups

namespace NSJoin

theorem nsJA2InputOf_A5 (hC : GGSecFiveNSCornerInput) (hLie : GGSecFiveNSLieAInput) :
    NSJA2InputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg0
  obtain ⟨hcfg, hns, ι, M, e, hpres, hA, hbig⟩ := hcfg0
  obtain ⟨K, _, _, _, f, n, ψ, hcard, hn4, hker, hrange, hdvd, hacts⟩ :=
    hLie G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hA hbig L (Or.inl rfl) hns
  have h : GGNSLocalHyp p B Bs K f n ψ :=
    ggNSLocalHyp_of_routeCfg hcfg (Or.inl rfl) hcard hn4 hker hrange hdvd hacts.1
  obtain ⟨c, hc⟩ := ggNSLocal_exists_diag hC h
  refine nsJA2_of_diag hcfg (h.comp_conj c) hc ?_
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective, Subgroup.map_top, hrange]

end NSJoin

end CFSG.StandardType

end
