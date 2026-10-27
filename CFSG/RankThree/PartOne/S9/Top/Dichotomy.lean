module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Top.ThetaLocal
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

namespace Sec9Top

variable {G : Type} [Group G] [Finite G]

theorem prime_and_three_lt_of_mem_sigmaA (he : evenRank G = 3) (hsig : sigmaA G ≠ {3})
    {p : ℕ} (hp : p ∈ sigmaA G) : p.Prime ∧ 3 < p := by
  classical
  obtain ⟨q, hq, hq3, hqr⟩ := (rank_three_selector_ne_three_iff he).1 hsig
  rw [sigmaA_eq_of_evenRank_eq_three he] at hp
  split_ifs at hp with h5 h3
  · exact ⟨hp.1, lt_trans (by norm_num) hp.2.1⟩
  · exact ⟨hp.1, hp.2.1⟩
  · exact absurd ⟨q, hq, hq3, hqr⟩ h3

theorem not_exists_twoLocal_aschCore_of_pRank_gt_three (he : evenRank G = 3) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hrank : 3 < CFSG.pRank q G) (Q : Sylow q G) :
    ¬ ∃ H : Subgroup G, IsTwoLocal H ∧ aschCore 2 q (Q : Subgroup G) ≤ H := by
  rintro ⟨H, hH, hle⟩
  have hq1 : 1 < q := hq.one_lt
  have htop : CFSG.pRank q G = CFSG.Open.pRank q (⊤ : Subgroup G) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top q G
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq1 (⊤ : Subgroup G)
  have hEq : IsPGroup q E := by
    obtain ⟨k, hk⟩ : ∃ k, Nat.card E = q ^ k := ⟨_, hEcard⟩
    exact IsPGroup.of_card hk
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q', hEQ'⟩ := hEq.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' Q
  have hQ : (Q : Subgroup G) = (Q' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  have hrQ' : CFSG.Open.pRank q (⊤ : Subgroup G) ≤ CFSG.Open.pRank q (Q' : Subgroup G) :=
    CFSG.SectionRank.le_pRank hq1 hEQ' hE hEcard
  have hQrank : CFSG.Open.pRank q (Q : Subgroup G) = CFSG.Open.pRank q (Q' : Subgroup G) := by
    rw [hQ]
    exact SteinbergBY.assembly_pRank_map_mulEquiv hq1 (MulAut.conj g) _
  have h4 : 4 ≤ CFSG.Assembly.pRank q (Q : Subgroup G) := by
    change 4 ≤ CFSG.Open.pRank q (Q : Subgroup G)
    rw [hQrank]
    omega
  have hcore : Subgroup.normalizer (Q : Set G) ≤ aschCore 2 q (Q : Subgroup G) := by
    refine le_sSup ⟨(Q : Subgroup G), le_rfl, by omega, ?_, rfl⟩
    rw [sup_eq_left.mpr inf_le_left]
    omega
  have hQH : (Q : Subgroup G) ≤ H :=
    Subgroup.le_normalizer.trans (hcore.trans hle)
  have hHrank : 4 ≤ CFSG.Open.pRank q H :=
    h4.trans (CFSG.SectionRank.pRank_mono hq1 hQH)
  have hloc : CFSG.Open.pRank q H ≤ CFSG.RankThreeEvenClassification.Helpers.twoLocalRank q G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank q hq H hH
  have hev : CFSG.RankThreeEvenClassification.Helpers.twoLocalRank q G ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank q hq hq2 G
  have : CFSG.Open.evenRank G = 3 := he
  omega

theorem forall_sylow_not_exists_twoLocal {p : ℕ} (hp : p.Prime) {P : Sylow p G}
    (hP : ∀ H : Subgroup G, IsTwoLocal H → ¬ aschCore 2 p (P : Subgroup G) ≤ H)
    (P' : Sylow p G) : ∀ H : Subgroup G, IsTwoLocal H → ¬ aschCore 2 p (P' : Subgroup G) ≤ H := by
  intro H hH hle
  have hiff := (SteinbergBY.aschbacher_core_conjugacy hp 2 (P' : Subgroup G)).2.2 P' rfl
  obtain ⟨H', hH', hle'⟩ := hiff.1 ⟨H, hH, hle⟩ P
  exact hP H' hH' hle'

end Sec9Top

open Sec9Top in
theorem selectedPrimeDichotomy_of_coreVanishing (hCVD : CoreVanishingDichotomy) :
    SelectedPrimeDichotomy := by
  intro G _ _ _ hnonab hK hchar he hsig
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnot, hvan⟩ := hcon
  obtain ⟨p, hpσ, P, hP⟩ : ∃ p ∈ sigmaA G, ∃ P : Sylow p G,
      ∀ H : Subgroup G, IsTwoLocal H → ¬ aschCore 2 p (P : Subgroup G) ≤ H := by
    unfold AschCoreLocal at hnot
    push Not at hnot
    exact hnot
  obtain ⟨hpp, hp3⟩ := prime_and_three_lt_of_mem_sigmaA he hsig hpσ
  obtain ⟨p₀, hp₀σ, hp₀p, hp₀3, hgood, hstar⟩ : ∃ p₀ ∈ sigmaA G, p₀.Prime ∧ 3 < p₀ ∧
      GoodGlobalRank G p₀ ∧ ∀ P' : Sylow p₀ G, ∀ H : Subgroup G, IsTwoLocal H →
        ¬ aschCore 2 p₀ (P' : Subgroup G) ≤ H := by
    by_cases hgood : GoodGlobalRank G p
    · exact ⟨p, hpσ, hpp, hp3, hgood, forall_sylow_not_exists_twoLocal hpp hP⟩
    · have hgood' : p = 7 ∧ ∃ q ∈ sigmaA G, 7 < q ∧ 3 < CFSG.pRank q G := by
        unfold GoodGlobalRank at hgood
        push Not at hgood
        exact hgood
      obtain ⟨-, q, hqσ, hq7, hqrank⟩ := hgood'
      obtain ⟨hqp, hq3⟩ := prime_and_three_lt_of_mem_sigmaA he hsig hqσ
      refine ⟨q, hqσ, hqp, hq3, fun h => absurd h (by omega), fun Q => ?_⟩
      exact fun H hH hle =>
        not_exists_twoLocal_aschCore_of_pRank_gt_three he hqp (by omega) hqrank Q ⟨H, hH, hle⟩
  have hsec : Sec9Hyp G p₀ :=
    { simple := inferInstance, nonabelian := hnonab, kProper := hK, charTwo := hchar,
      evenRank_eq := he, prime := hp₀p, three_lt := hp₀3, mem_sigma := hp₀σ }
  refine hvan ⟨p₀, hp₀σ, hp₀3, ?_⟩
  intro A hA hAcard B hBA hBcard c hcA hc1
  have hApg : IsPGroup p₀ A := hA.isPGroup p₀ A
  obtain ⟨P', hAP'⟩ := hApg.exists_le_sylow
  rcases hCVD G p₀ hsec hgood A hA hAcard P' hAP' B hBA hBcard c hcA hc1 with
    ⟨-, H₀, hH₀, hle⟩ | ⟨hα, ⟨T, hT, hTA⟩, hodd⟩
  · exact absurd hle (hstar P' H₀ hH₀)
  · refine ⟨hα, ?_, hodd⟩
    have hcp : c ^ p₀ = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
    rw [Sec9Top.inSubgroup_theta_normalizer_zpowers_eq hp₀p hcp] at hT
    obtain ⟨S, hS⟩ := Sec9Top.exists_sylow_map_eq Nat.prime_two hT
    exact ⟨S, hS ▸ hTA⟩

end CFSG.RankThree.PartOne
