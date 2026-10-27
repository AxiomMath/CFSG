module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenNine
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartTwo.KFacts.KS116Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
public import CFSG.RankThree.PartTwo.Sec11.Transitivity
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem fifteen_thirteen (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h129 : R129_1 D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D) (h1217 : R1217 D)
    (h1110 : R1110G D) (h1111 : R1111 D) (h115 : F11.R115 D) (h77 : F07.R77Eq D)
    (h159 : R15_9 D) (h1511 : R15_11 D) (h1512 : R15_12 D) : R15_13 D := by
  intro V₀ V L h hL
  have hV := h.hyp151.isElemAbelian
  by_contra hcon
  have hcon' : ¬ (gamma15 D.M V₀ V hV L ≤ 3 ∧ s15 D.M V₀ V hV L = 2) := hcon
  have hpos : Hyp125 D V₀ V := h.hyp151.hyp125
  have hkc := s15_Thirteen_k_cases D
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    (E3.wClos_mono D.sylowM.le).trans (h159 V₀ V L h hL)
  have hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p D.M := fun p hp => by
    rw [UC6.groupPRank_eq_pRank]
    exact hSg.three_le p hp
  have hN := fifteen_thirteen_a D h129 h61 hSg.nonempty hrk hpos hW
  have h2' : gamma15 D.M V₀ V hV L = 2 →
      D.k = 1 ∨ (5 ∈ D.sig ∧ (s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6)) :=
    fun hγ => s15_Thirteen_gamma_two D hSg h1219 h1217 h1110 h1111 h127 h hV hL hγ
  have h2 : gamma15 D.M V₀ V hV L = 2 → D.k = 1 ∨ s15 D.M V₀ V hV L = 5 ∨ s15 D.M V₀ V hV L = 6 :=
    fun hγ => (h2' hγ).imp_right fun h5 => h5.2
  have hγ2 := two_le_gamma15 D h.hyp151 hV hL
  have hs2 := fifteen_five D h129 h1217 h hV hL
  have hkm := s15_Thirteen_k_lt_m hγ2 (by omega) hkc hcon' h2
  have hC : centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
    by_contra hnC
    obtain ⟨-, hcase⟩ := h1511 V₀ V L h hL D.k (by omega) hnC
    rcases hcase with ⟨hγ, hs4, hk2⟩ | ⟨hs, hγ3⟩
    · rcases h2 hγ with h1 | h5 | h6 <;> omega
    · exact hcon' ⟨hγ3, hs⟩
  have hr := s15_Thirteen_lt_rParam D h hV hL hkm
  have hbeta : (D.k : ℕ∞) < betaN 0 D.M V :=
    lt_of_lt_of_le (by exact_mod_cast hkm) (s15_Thirteen_beta D h1217 h hV hL)
  obtain ⟨H, A, K, hS, hA, hK, hne⟩ := s15_Thirteen_exists_A_K D h126 hpos hN hC
  obtain ⟨X, g, hX, hg⟩ := s15_Thirteen_six_nine D hpos hS hA hK hr hbeta hne
  have hO : (calO D.k D.M V₀ V).Nonempty := ⟨X, g, hX, hg.1⟩
  have hkγ : D.k < gamma15 D.M V₀ V hV L := by
    by_contra hnk
    have hγ : gamma15 D.M V₀ V hV L = 2 := by omega
    rcases h2' hγ with h1 | ⟨h5, hs5⟩
    · omega
    · exact s15_Thirteen_gap1 D hSg h1219 h1217 h127 h1111 h115 h1110 h77 h hV hL hγ (by omega)
        h5 hs5
  exact hcon (h1512 V₀ V L h hL D.k (by omega) hkγ hO)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
