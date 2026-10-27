module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
public import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPB_oTwoPrime_le_block {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹) :
    ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)) ≤
      (ggSuPairBlock K 2 f n a b).map ψ := by
  rw [ggOTwoPrime, Subgroup.closure_le]
  rintro y ⟨hy, k, hyk⟩
  exact ggNSPosPB2_twoElt_mem_map h hd a b hab r hr hy hyk

end CFSG.StandardType

end
