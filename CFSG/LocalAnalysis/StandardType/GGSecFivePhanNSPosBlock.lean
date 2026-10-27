module

import Lean
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f n : ℕ} {ψ : Su K 2 f n →* G}

theorem ggNSDiag_rankOne_block (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹) :
    ggRankOneIn ψ.range Bs r = (ggSuPairBlock K 2 f n a b).map ψ := by
  rw [ggRankOneIn]
  exact le_antisymm (ggNSPosPB_oTwoPrime_le_block h hd a b hab r hr)
    (ggNSPosPB_block_le_oTwoPrime h hd a b hab r hr)

end CFSG.StandardType

end
