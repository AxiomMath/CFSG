module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vj
public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
import CFSG.LocalAnalysis.UniquenessCase.UC1S5Bridge
import CFSG.LocalAnalysis.RankThreeUC.Section5.ModuleRankBound
import CFSG.LocalAnalysis.RankThreeUC.Section5.AlphaPrimeSymmetry

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F05

open CFSG.LocalAnalysis.RankThreeUC

theorem k516_of_symmetry
    (hsym : ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
      [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}, Section5.BinaryActionRankCounterexample G p P T B e ρ →
      ∀ {q : ℕ}, q ∈ Section5.alphaSet G → ∃ P' : Subgroup G, Section5.BinaryActionRankCounterexample G q P' T B e ρ) :
    K516 :=
  k516_of_section5 fun _ _ _ _ _ _ _ _ _ _ _ _ _ hc => Section5.false_of_symmetry hc fun _ hq => hsym hc hq

theorem k516_holds : K516 :=
  k516_of_symmetry Section5.exists_binaryActionRankCounterexample_of_mem_alphaSet

theorem k516K_holds : K516K :=
  K516K_of_K516 k516_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.F05
