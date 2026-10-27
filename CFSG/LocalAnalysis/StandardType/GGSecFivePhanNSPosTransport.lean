module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTransportAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem GGNSLocalHyp.comp_conj (h : GGNSLocalHyp p B Bs K f n ψ) (c : Su K 2 f n) :
    GGNSLocalHyp p B Bs K f n (ψ.comp (MulAut.conj c).toMonoidHom) := by
  refine ⟨h.prime, h.odd, h.card, h.dvd, h.four_le, ?_, h.bstar, h.rank, h.bmax, ?_, h.noTr, ?_⟩
  · exact ggNSPosPD_ker_comp_conj h.ker c
  · rw [ggNSPosPD_range_comp_conj c]
    exact h.cent
  · exact ggNSPosPD_acts_conj h.card c h.acts

end CFSG.StandardType

end
