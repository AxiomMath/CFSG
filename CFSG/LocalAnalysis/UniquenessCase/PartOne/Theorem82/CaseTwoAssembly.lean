module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFusion
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoRankTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoEndgame

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] def CaseTwoResidual : Prop :=
  ∀ p : ℕ, p ∈ c.sig →
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p →
    t.PairNormalizerLe p →
    ¬ t.InducesAlternating → Subgroup.centralizer (t.Z : Set G) ≤ c.S.M →
    CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G)) ≤ 1 →
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M

theorem false_of_centralizer_Z_le_of_pairNormalizerLe (hOut : PerfectAutInner)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hR : t.CaseTwoResidual) {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : False := by
  by_cases hIIa : t.InducesAlternating
  · exact t.false_of_inducesAlternating hOut hp hN hZ hIIa
  have hy : Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M := by
    by_cases h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G))
    · exact t.centralizer_y_le_of_two_le_pRank hp hSE h2
    · exact hR p hp h76 hN hIIa hZ (by omega)
  exact t.false_of_centralizer_le hp hN
    (fun x hx hx1 => t.centralizer_le_of_mem_AA hN hZ hx hx1) hy

section Full

variable {c : Ctx812 G} (t : CaseTwoTransitive c.toCtx812E)

theorem false_of_centralizer_Z_le (hOut : PerfectAutInner)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (hR : t.CaseTwoResidual) {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : False :=
  t.false_of_centralizer_Z_le_of_pairNormalizerLe hOut hSE hR hp h76
    (t.pairNormalizerLe hp h76) hZ

end Full

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
