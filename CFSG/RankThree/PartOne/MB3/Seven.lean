module

public import CFSG.RankThree.PartOne.MB3.Defs
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingScalarKernelHyperplane
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.FiveSuccessorMaximal
import CFSG.RankThree.PartOne.S9.Top.Dichotomy
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

structure SevenData {G : Type} [Group G] [Finite G] (A L : Subgroup G) (q : ℕ)
    (D R : Subgroup G) : Prop where
  q_prime : q.Prime
  q_ne_two : q ≠ 2
  q_ne_seven : q ≠ 7
  D_ne_bot : D ≠ ⊥
  D_le : D ≤ L
  D_char : (D.subgroupOf L).Characteristic
  D_le_O : D ≤ oddThetaCore 7 L
  D_exp : ∀ x ∈ D, x ^ q = 1
  D_class : ⁅⁅D, D⁆, D⁆ = ⊥
  R_two : IsPGroup 2 R
  R_le : R ≤ L
  R_inv : A ≤ Subgroup.normalizer (R : Set G)
  R_comm : ⁅R, A⁆ = R
  R_ne_bot : R ≠ ⊥
  R_act : ⁅R, D⁆ ≠ ⊥
  kernel : A ⊓ Subgroup.centralizer (R : Set G) = thetaQuotientCentralizer 7 A L
  relIndex : (thetaQuotientCentralizer 7 A L).relIndex A = 7
  R_min : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
    ⁅U, D⁆ = ⊥
  fixed_rank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3
  scalar : ∀ e ∈ thetaQuotientCentralizer 7 A L,
    ∃ k : ℕ, ∀ d ∈ D, (e * d * e⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D

@[expose] def SevenSmallPrimeCase : Prop :=
  SchreierFor InCatalog → TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 7 A →
    ∀ L ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple L →
      (∀ Y ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple Y → sectionTenRel 7 L Y →
        sectionTenRel 7 Y L) →
      ∀ (q : ℕ) (D R : Subgroup G), (q = 3 ∨ q = 5) → SevenData A L q D R → False

theorem exists_seven_maximal_nonquasisimple (hS : SchreierFor InCatalog) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hS10 : SteinbergBM.SectionTenSetup G 7 A)
    (hne : ∃ L ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple L) :
    ∃ L ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple L ∧
      ∀ Y ∈ sectionTenZero 7 A, ¬ CFSG.IsQuasisimple Y → sectionTenRel 7 L Y →
        sectionTenRel 7 Y L := by
  obtain ⟨hsimple, hnonab, hK, -, -, -, hAe, -, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have hp : (7 : ℕ).Prime := by norm_num
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hAe' : IsElementaryAbelian 7 A := hAe
  obtain ⟨L₀, hL₀, hL₀q⟩ := hne
  obtain ⟨L, ⟨hLZ, hLq⟩, hmax⟩ := exists_forall_rel_symm_of_refl_trans (sectionTenRel 7)
    (B := {Y | Y ∈ sectionTenZero 7 A ∧ ¬ CFSG.IsQuasisimple Y})
    (fun x _ => sectionTenRel_refl 7 x)
    (fun x hx y hy z hz hxy hyz => section_ten_component_supplement_transitivity hS G hnonab hK
      he 7 hp (by norm_num) A hAe' x hx.1.1 y hy.1.1 z hz.1.1 hxy hyz) ⟨L₀, hL₀, hL₀q⟩
  exact ⟨L, hLZ, hLq, fun Y hY hYq => hmax Y ⟨hY, hYq⟩⟩

theorem seven_lifting {G : Type} [Group G] [Finite G] {A L : Subgroup G} {q : ℕ}
    {D R : Subgroup G} (hTwo : TwoActionInputs) (h : SteinbergBM.SectionTenSetup G 7 A)
    (hd : SevenData A L q D R) (hRAD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) :
    IsElementaryAbelian q D ∧ Nat.card D = q ^ 7 ∧
      ∃ r ∈ R, orderOf r = 2 ∧ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3 := by
  have hp : Nat.Prime 7 := by norm_num
  have hq := hd.q_prime
  have hq2 := hd.q_ne_two
  have hqp : q ≠ 7 := hd.q_ne_seven
  have hAe : IsElementaryAbelian 7 A := h.2.2.2.2.2.2.1
  have hAcard : Nat.card A = 7 ^ 3 := h.2.2.2.2.2.2.2.1
  have hBA : A ⊓ Subgroup.centralizer (R : Set G) ≤ A := inf_le_left
  have hrel : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = 7 := by
    rw [hd.kernel]
    exact hd.relIndex
  have hDq : IsPGroup q D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hd.D_exp x x.2)⟩
  obtain ⟨a, b₀, haA, haB, hb₀B, hb₀1, hA₀A, hA₀elem, hA₀card, hfac, hker⟩ :=
    exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
  set A₀ := zpowers a ⊔ zpowers b₀ with hA₀
  have hset : MinTwoActionSetting 7 q A₀ D R :=
    minTwoActionSetting_of_plane hp hq (by norm_num) hq2 hqp hA₀elem hA₀card hA₀A hfac hRAD
      hd.D_exp hd.D_class hd.R_two hd.R_inv hd.R_comm hd.R_ne_bot hd.R_act hd.R_min
  have hA₀R : A₀ ≤ Subgroup.normalizer (R : Set G) := hA₀A.trans hd.R_inv
  have hA₀D : A₀ ≤ Subgroup.normalizer (D : Set G) := hA₀A.trans (le_sup_right.trans hRAD)
  have hRD' : R ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hRAD
  obtain ⟨hAlt, -, hlift⟩ := hTwo
  rcases hAlt G 7 q A₀ D R hset hd.fixed_rank with
    ⟨hRcase, ⟨r, hrR, hr1, hr3⟩, -⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
  · obtain ⟨hRe, hRcard⟩ : IsElementaryAbelian 2 R ∧ Nat.card R = 8 := by
      rcases hRcase with ⟨h5, -⟩ | ⟨-, hRe, hRcard⟩
      · omega
      · exact ⟨hRe, hRcard⟩
    have hkerA₀ : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (R : Set G)) = 7 := by
      rw [← hker, ← inf_assoc, inf_eq_left.mpr hA₀A]
    have hfrR : inSubgroup frattini R = ⊥ := by
      have : Fact (IsPGroup 2 ↥R) := ⟨hRe.isPGroup 2 ↥R⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]
    have hodd : ¬ 2 ∣ Nat.card A₀ := by
      rw [hA₀card]
      decide
    have hmin₀ : ∀ U : Subgroup G, U < R → A₀ ≤ Subgroup.normalizer (U : Set G) →
        ⁅U, A₀⁆ = U → ⁅U, D⁆ = ⊥ := fun U hU hA₀U hUA₀ =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hset.R_min U hU hA₀U hUA₀)
    have hirrR : ∀ Y : Subgroup G, Y ≤ R → A₀ ≤ Subgroup.normalizer (Y : Set G) →
        Y = ⊥ ∨ Y = R := by
      intro Y hYR hA₀Y
      by_cases hYe : Y = R
      · exact Or.inr hYe
      refine Or.inl ?_
      have h' := le_inSubgroup_frattini_of_proper_invariant hd.R_two hd.R_ne_bot hodd hA₀R hA₀D
        hset.R_comm hd.R_act hmin₀ Y (lt_of_le_of_ne hYR hYe) hA₀Y
      rw [hfrR] at h'
      exact le_bot_iff.mp h'
    have hRA₀D : R ⊔ A₀ ≤ Subgroup.normalizer (D : Set G) := sup_le hRD' hA₀D
    obtain ⟨-, hDe, hDcard, -⟩ := hlift G 7 q 3 A₀ D R hp hq hq2 hqp (Or.inl ⟨rfl, rfl⟩) hA₀elem
      hA₀card hA₀R hRe (by rw [hRcard]; norm_num) hkerA₀ hirrR hRA₀D hDq hd.D_exp hd.D_class
      hd.R_act hd.fixed_rank
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hr2 : orderOf r = 2 := orderOf_eq_prime (by
      have := elemPow_eq_one_of_isElementaryAbelian (p := 2) r hrR
      exact this) hr1
    exact ⟨hDe, hDcard, r, hrR, hr2, hr3⟩
  · omega
  · omega

theorem false_of_large_prime (hCVD : CoreVanishingDichotomy) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (h : SteinbergBM.SectionTenSetup G 7 A) {q : ℕ} (hq : q.Prime) (hq7 : 7 < q)
    {D : Subgroup G} (hDe : IsElementaryAbelian q D) (hDcard : Nat.card D = q ^ 7) {r : G}
    (hr2 : orderOf r = 2)
    (hrank : CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) : False := by
  have hq1 : 1 < q := hq.one_lt
  have hq2 : q ≠ 2 := by omega
  have he : evenRank G = 3 := sectionTenSetup_evenRank_eq h
  have hrk7 : 7 ≤ CFSG.pRank q G := by
    have h1 := CFSG.SectionRank.le_pRank hq1 (le_top : D ≤ ⊤)
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q D).mp hDe) hDcard
    have h2 : CFSG.pRank q G = CFSG.Open.pRank q (⊤ : Subgroup G) :=
      CFSG.SectionRank.pRank_eq_open_pRank_top q G
    omega
  have hr1 : r ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hr2
    omega
  obtain ⟨E', hE'le, hE', hE'card⟩ :=
    CFSG.SectionRank.exists_pRank hq1 (D ⊓ Subgroup.centralizer ({r} : Set G))
  have h3 : CFSG.Open.pRank q (D ⊓ Subgroup.centralizer ({r} : Set G)) = 3 := by
    have := assembly_pRank_eq hq (D ⊓ Subgroup.centralizer ({r} : Set G))
    rw [hrank] at this
    exact this
  rw [h3] at hE'card
  have hU : Subgroup.zpowers r ≠ ⊥ := fun h1 => hr1 (by
    rw [Subgroup.zpowers_eq_bot] at h1
    exact h1)
  have hU2 : IsPGroup 2 (Subgroup.zpowers r) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hr2]
    simp)
  have hE'N : E' ≤ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({r} : Set G) := (hE'le hx).2
    rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at *
    exact hxC
  have h3le : 3 ≤ localRank q G :=
    Sec9Excl.le_localRank_of_normalizes hq1 hU hU2 hE'.1 hE'.2 hE'card
      (fun x hx => hE'N hx)
  have hlr : localRank q G = 3 :=
    le_antisymm ((CFSG.RankThree.OddKernel.localRank_le_evenRank hq hq2).trans he.le) h3le
  have hσ : q ∈ sigmaA G := by
    rw [rank_three_selector_of_large he ⟨q, hq, by omega, hlr⟩]
    exact ⟨hq, by omega, hlr⟩
  have hsec : Sec9Hyp G q :=
    { simple := h.1, nonabelian := h.2.1, kProper := sectionTenSetup_kProper h,
      charTwo := sectionTenSetup_charTwo h, evenRank_eq := he, prime := hq,
      three_lt := by omega, mem_sigma := hσ }
  have hgood : GoodGlobalRank G q := fun h7 => absurd h7 (by omega)
  have hstar : ∀ P' : Sylow q G, ∀ H : Subgroup G, IsTwoLocal H →
      ¬ aschCore 2 q (P' : Subgroup G) ≤ H := fun Q H hH hle =>
    Sec9Top.not_exists_twoLocal_aschCore_of_pRank_gt_three he hq hq2 (by omega) Q ⟨H, hH, hle⟩
  have hvan : SteinbergBY.AschVanishing G q := by
    intro A' hA' hAcard B hBA hBcard c hcA hc1
    have hApg : IsPGroup q A' := hA'.isPGroup q A'
    obtain ⟨P', hAP'⟩ := hApg.exists_le_sylow
    rcases hCVD G q hsec hgood A' hA' hAcard P' hAP' B hBA hBcard c hcA hc1 with
      ⟨-, H₀, hH₀, hle⟩ | ⟨hα, ⟨T, hT, hTA⟩, hodd⟩
    · exact absurd hle (hstar P' H₀ hH₀)
    · refine ⟨hα, ?_, hodd⟩
      have hcp : c ^ q = 1 := elemPow_eq_one_of_isElementaryAbelian c hcA
      rw [Sec9Top.inSubgroup_theta_normalizer_zpowers_eq hq hcp] at hT
      obtain ⟨S, hS⟩ := Sec9Top.exists_sylow_map_eq Nat.prime_two hT
      exact ⟨S, hS ▸ hTA⟩
  have hQ10 : q ∈ SteinbergBM.sectionTenPrimeSet G :=
    ⟨hq, by omega, hσ, hvan, E', (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian q E').mpr
      hE', hE'card, Subgroup.zpowers r, hU, hU2, hE'N⟩
  have := h.2.2.2.2.2.2.2.2.2 ⟨q, hQ10, hq7⟩
  omega

theorem movingQuasisimpleSeven_of (hCVD : CoreVanishingDichotomy) (hSmall : SevenSmallPrimeCase) :
    MovingQuasisimpleSeven := by
  intro hS hTwo G _ _ A h K hK
  by_contra hnq0
  obtain ⟨L, hL, hnq, hmax⟩ := exists_seven_maximal_nonquasisimple hS h ⟨K, hK, hnq0⟩
  have hAe : IsElementaryAbelian 7 A := h.2.2.2.2.2.2.1
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq h).le
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he 7 (by norm_num) (by norm_num) A hAe
      L hL.1
  obtain ⟨-, hrel, q, hq, hq2, hqp, D, R, hD1, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA,
    hR1, hRD, hker, hmin, hrank, hscal⟩ :=
    nonquasisimple_moving_theta_component_scalar_kernel_hyperplane_of
      selected_prime_elements_normalize_theta_components hTwo G 7 A h L hL hnq
  have hd : SevenData A L q D R :=
    { q_prime := hq, q_ne_two := hq2, q_ne_seven := hqp, D_ne_bot := hD1, D_le := hDL,
      D_char := hDchar, D_le_O := hDO, D_exp := hDexp, D_class := hDcl, R_two := hR2,
      R_le := hRL, R_inv := hAR, R_comm := hRA, R_ne_bot := hR1, R_act := hRD, kernel := hker,
      relIndex := hrel, R_min := hmin, fixed_rank := hrank, scalar := hscal }
  by_cases hq7 : q < 7
  · have hq35 : q = 3 ∨ q = 5 := by
      have h3 : 3 ≤ q := by
        have := hq.two_le
        omega
      interval_cases q
      · exact Or.inl rfl
      · exact absurd hq (by norm_num)
      · exact Or.inr rfl
      · exact absurd hq (by norm_num)
    exact hSmall hS hTwo G A h L hL hnq hmax q D R hq35 hd
  · have hq7' : 7 < q := by
      have : q ≠ 7 := hqp
      omega
    have hLD : L ≤ Subgroup.normalizer (D : Set G) :=
      le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hDL hDchar
    have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
      le_normalizer_of_characteristic_subgroupOf hAL hDL hDchar
    have hRAD : R ⊔ A ≤ Subgroup.normalizer (D : Set G) := sup_le (hRL.trans hLD) hAD
    obtain ⟨hDe, hDcard, r, -, hr2, hr3⟩ := seven_lifting hTwo h hd hRAD
    exact false_of_large_prime hCVD h hq hq7' hDe hDcard hr2 hr3

end CFSG.RankThree.PartOne.MB3
