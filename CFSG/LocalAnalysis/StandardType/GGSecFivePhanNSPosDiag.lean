module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommon
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagOrthoAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSLocal_exists_diag (hC : GGSecFiveNSCornerInput) (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ c : Su K 2 f n, GGActsDiagonally (p := 2) (f := f) (ψ.comp (MulAut.conj c).toMonoidHom) Bs := by
  classical
  obtain ⟨g, hg, hpow, hcomm⟩ := ggNSPosPE_normalized_family hC h
  obtain ⟨c, hc⟩ := ggNSPosPE3_orthonormal_diag h g (fun b => (hg b).1) hpow hcomm
  refine ⟨c, ?_⟩
  intro b hb
  exact ⟨(c : GL (Fin n) K)⁻¹ * g ⟨b, hb⟩ * (c : GL (Fin n) K), hc ⟨b, hb⟩,
    ggNSPosPE_conj_induces (c := c) (hg ⟨b, hb⟩)⟩

end CFSG.StandardType

end
