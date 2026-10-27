module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc7d
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
public import CFSG.LocalAnalysis.GL83PartI.I713.Orthogonal
import CFSG.LocalAnalysis.GL83PartI.I713.ExceptionalThree
import CFSG.RankThree.PartOne.MB3.OddOutLinear
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.RankThree.PartOne.AUTSL.OddOutRee
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.PSL2Odd
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.OrthOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.OutStructure
open CFSG.Blueprint
open CFSG.Open

private theorem outPNice_lie_of_pRank_le_one
    {K : Type} [Group K] [Finite K]
    {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : LieModel K t n ℓ f) (ht : t ≠ .Tits)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) :
    CFSG.HasNormalPComplement p (Outer K) := by
  have : Fact p.Prime := ⟨hp⟩
  have nice : OutPNice p K → CFSG.HasNormalPComplement p (Outer K) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7d.hasNormalPComplement_outer_of_outPNice hp
  rcases hmodel with ⟨-, hcl⟩ | ⟨-, -, hch⟩ | ⟨-, -, hree⟩ | ⟨-, rfl, hsz⟩
  · cases t
    case PSL =>
      by_cases hn : n = 2
      · subst hn
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSL_two hp hcl)
        · exact nice
            (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_PSL_two_odd_all hp hp2 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        refine nice (outPNice_PSL_ge_three_odd hp hp2 hn3 hcl fun hd => ?_)
        have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
          obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hcl
          have e' : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n F :=
            (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n F).symm).trans
              (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n F)
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e']
          exact GL83.I713.two_le_pRank_projectiveSL_of_dvd hn3 hp hp2 (by rwa [hF])
        omega
    case PSU =>
      have hn3 : 3 ≤ n := hcl.1.2.2.1
      refine nice (outPNice_PSU_odd hp hcl fun hd => ?_)
      have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
        obtain ⟨⟨hℓ, hm, hn3', hne⟩, F, _, _, hF, ⟨e⟩⟩ := hcl
        have hpn : p ∣ n := hd.trans (Nat.gcd_dvd_left _ _)
        have hpq : p ∣ ℓ ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
        exact GL83.I713.two_le_pRank_statedPSU_of_dvd hF hp hp2 hn3 hpn hpq
      omega
    case PSp =>
      by_cases hn : n = 2
      · subst hn
        by_cases hℓ : ℓ = 2
        · subst hℓ
          exact nice (outPNice_PSp_two hp hcl)
        · exact nice (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd hp hp2 hℓ hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact nice (outPNice_PSp_ge_three_odd hp hp2 hn3 hcl)
    case POmegaOdd =>
      exact nice (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all hp hp2 hcl)
    case POmegaPlus =>
      by_cases hn : n = 4
      · subst hn
        by_cases hp3 : p = 3
        · subst hp3
          exact absurd (GL83.I713.two_le_pRank_three_classical_POmegaPlus hcl) (by omega)
        · exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7d.hasNormalPComplement_outer_POmegaPlus_four hp
            (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hcl
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact nice
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaPlus_all_ge_five hp hp2 hn5 hcl)
    case POmegaMinus =>
      exact nice (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all hp hp2 hcl)
    all_goals exact hcl.2.elim
  · cases t
    case G2 =>
      by_cases h2 : ℓ = 2
      · subst h2
        exact nice (outPNice_G2 hp hch)
      · by_cases h3 : ℓ = 3
        · subst h3
          exact nice (outPNice_G2_three hp hch)
        · exact nice (outPNice_G2_odd hp h2 h3 hch)
    case F4 =>
      by_cases h2 : ℓ = 2
      · subst h2
        exact nice (outPNice_F4 hp hch)
      · exact nice (outPNice_F4_odd hp h2 hch)
    case E6 =>
      by_cases hp3 : p = 3
      · subst hp3
        exact absurd (GL83.I713.four_le_pRank_three_of_untwistedModel_E6 hch.2) (by omega)
      · exact nice (outPNice_E6_gen hp hp3 hp2 hch)
    case E7 => exact nice (outPNice_E7_gen hp hp2 hch)
    case E8 => exact nice (outPNice_E8_gen hp hch)
    case twistedE6 =>
      by_cases hp3 : p = 3
      · subst hp3
        exact absurd (GL83.I713.two_le_pRank_three_of_twistedE6Model (p := ℓ) hadm.1 hadm.2.1 hch.2)
          (by omega)
      · exact nice (outPNice_twistedE6_gen hp hp3 hch)
    case trialityD4 =>
      exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.hasNormalPComplement_of_isMulCommutative
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.isMulCommutative_outer_trialityD4 hch)
    all_goals exact hch.2.elim
  · cases t
    case twistedG2 =>
      have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact nice (CFSG.RankThree.PartOne.AUTSL.outPNice_twistedG2 hp hree)
    case twistedF4 =>
      have h2 : ℓ = 2 := hree.1.2.2.2.1
      subst h2
      exact nice (outPNice_twistedF4 hp hree)
    case Tits => exact absurd rfl ht
    all_goals
      obtain ⟨-, a, -, hm⟩ := hree
      exact hm.elim
  · have h2 : ℓ = 2 := hsz.1
    subst h2
    exact nice (outPNice_Suzuki hp hsz)

theorem hasNormalPComplement_outer_of_pRank_le_one
    {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) :
    CFSG.HasNormalPComplement p (Outer K) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup K := hs
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · apply CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.hasNormalPComplement_of_not_dvd_card
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [classicalTags] at h
      · simp [chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.hasNormalPComplement_of_not_dvd_card fun hd => ?_
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · exact outPNice_lie_of_pRank_le_one hadm hmodel ht hp hp2 hrank
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    apply CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc7.hasNormalPComplement_of_not_dvd_card
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem hasNormalPComplement_outer_of_quasisimple_of_pRank_le_one
    {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hcat : CFSG.Open.IsCatalogGroup (K ⧸ Subgroup.center K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) :
    CFSG.HasNormalPComplement p (Outer K) := by
  have : Group.IsPerfect K := ⟨hq.1⟩
  let e : (↥(⊤ : Subgroup K) ⧸ Subgroup.center ↥(⊤ : Subgroup K)) ≃*
      (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center (⊤ : Subgroup K)) (Subgroup.center K) Subgroup.topEquiv
      (Subgroup.map_center_eq Subgroup.topEquiv)
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 1 := by
    have h2 := CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.pRank_quotient_center_le_one hp hp2
      (⊤ : Subgroup K) hrank
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e] at h2
  exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsMisc5.hasNormalPComplement_of_injective
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom K)
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective K)
    (hasNormalPComplement_outer_of_pRank_le_one hq.2
      (CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof.quotient_center_nonabelian hq)
      hcat hp hp2 hrank')

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
