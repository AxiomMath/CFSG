module

public import CFSG.RankThree.PartTwo.Sec18.Item189ListBridge
public import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO3
public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census424Rest.TypeL3Two
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldFixed

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

section OddRank

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}


theorem pRank_kAlpha_le_two189 (h1812 : Item181_2) (h184 : Item184_1) (h187 : Item187)
    (hset : Setting189 G A M H c) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(kAlpha189 M H c)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hset.toSec18H.toSec18Std
  obtain ⟨T, hT1, hT2, hMT⟩ := hstd.mem_scriptM.1.1
  have hpM : CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤ 2 := by
    have h1 := Sec17.HeadProof.open_pRank_top_le_localRank hT1 hT2 hp
    have h2 := hstd.localRank_lt p hp hp3
    rw [← hMT] at h1
    omega
  set K := normalClosureIn M c with hK
  have hKM : K ≤ M := le_of_mem_thetaComponentsIn hset.mem_thetaComponentsIn
  have hθ := aschbacherSolvableCore_eq_pCore189
    (inSubgroup_pPrimeCore_normalClosureIn_eq_pCoreOf h1812 h184 h187 hset.toSec18H hset.hyp187)
  let e1 : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(kAlpha189 M H c) :=
    (QuotientGroup.quotientMulEquivOfEq hθ.symm).trans (kThetaEquiv189 M H c)
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1
  have h2 := Sec20.Res11.pRank_quotient_le K hp (by omega)
  have h3 : CFSG.Open.pRank p K ≤ CFSG.Open.pRank p M :=
    CFSG.SectionRank.pRank_mono hp.one_lt hKM
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  have h4 : CFSG.Open.pRank p M = CFSG.Open.pRank p (⊤ : Subgroup ↥M) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

theorem list189L3Odd_of (h1812 : Item181_2) (h184 : Item184_1) (h187 : Item187) :
    List189L3Odd := by
  intro G _ _ A M H c hset p f _ hp2 hf hq ⟨e⟩
  by_contra hf1
  have hp : p.Prime := Fact.out
  have h3 : p ≠ 3 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (show f ≠ 0 by omega))
    omega
  have hp3 : 3 < p := by
    have := hp.two_le
    omega
  have h1 := pRank_kAlpha_le_two189 h1812 h184 h187 hset hp hp3
  have := Sec17.HeadProof.finite_projGenLinGroup_three (GaloisField p f)
  have h2 := Sec17.HeadProof.two_mul_le_pRank_projSL_three (GaloisField p f) (p := p)
    (GaloisField.card p f (by omega))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at h2
  omega

theorem list189U3Odd_of (h1812 : Item181_2) (h184 : Item184_1) (h187 : Item187) :
    List189U3Odd := by
  intro G _ _ A M H c hset p f _ hp2 hf hq ⟨e⟩
  by_contra hf1
  have hp : p.Prime := Fact.out
  have h3 : p ≠ 3 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (show f ≠ 0 by omega))
    omega
  have hp3 : 3 < p := by
    have := hp.two_le
    omega
  have h1 := pRank_kAlpha_le_two189 h1812 h184 h187 hset hp hp3
  have h2 : 2 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(projSU 3 p f)) :=
    Sec17.HeadProof.two_mul_le_pRank_projSU_three (p := p) (e := f) hp2
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at h2
  omega

end OddRank

theorem nonempty_projSL_two_five_equiv_two_two [Fact (Nat.Prime 5)] :
    Nonempty (projSL 2 (GaloisField 5 1) ≃* projSL 2 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
  exact ⟨((Sec4.projSLEquivPSL (GaloisField 5 1)).trans e).trans
    (Sec4.projSLEquivPSL (GaloisField 2 2)).symm⟩

theorem list189L2Odd_of (hL2e : List189L2Even)
    (hL3e : List189L3Even) : List189L2Odd := by
  intro Y _ _ X Q Γ x p f _ h hp2 hp3 hf ⟨e⟩
  by_cases hq : 9 < p ^ f
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, ‹_›, hp2, hq, ⟨e⟩⟩))))
  · have hp : p.Prime := Fact.out
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      push Not at hlt
      interval_cases p
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by decide)
    have hf1 : f = 1 := by
      by_contra hf1
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos (by omega)
      nlinarith
    subst hf1
    rw [pow_one] at hq
    have h57 : p = 5 ∨ p = 7 := by
      interval_cases p <;> simp_all (config := {decide := true})
    rcases h57 with rfl | rfl
    · obtain ⟨e'⟩ := nonempty_projSL_two_five_equiv_two_two
      exact hL2e Y X Q Γ x 2 h le_rfl ⟨e.trans e'⟩
    · haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      obtain ⟨e'⟩ :=
        CFSG.AGLEmbeddingD2.Wilson.Census424Rest.nonempty_projSL_two_seven_equiv_three_two
      exact hL3e Y X Q Γ x 1 h odd_one ⟨e.trans e'⟩

end CFSG.RankThree.PartTwo.Sec18
