module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxBlock
import CFSG.LocalAnalysis.StandardType.GGNSJoinJA2AAuxPair

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
open scoped MatrixGroups

theorem nsJA2_of_diag
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    (hrange : ψ.range = L) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 := by
  obtain ⟨a, b, c, hab, hbc, hac, h1, h2⟩ := nsJA2_exists_triple hcfg h hd hrange
  exact nsJA2_of_pairBlocks_le h hd hab hbc hac h1 h2

end CFSG.StandardType

end
