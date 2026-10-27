module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwoK
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNOut
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L34
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z9
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z8
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer
import CFSG.LieType.SeitzGeneration.OuterQuotient
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Small
import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
import CFSG.Quasithin.Vol2.KGFact838
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3ThinNNTwo (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ¬ (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
    ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q → ∀ p ∈ D.sig,
      (p = 3 → (conjSetOf D.M Y).ncard = 2) → normalizer (X : Set G) ≤ D.M

theorem R847E3.exists_B₀_of_not_dvd_card {M Y : Subgroup G}
    (hO : IsCyclic (Outer (Bar2 Y)) ∨ IsPGroup 2 (Outer (Bar2 Y))) (hY : IsSubnormal Y M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpY : ¬ p ∣ Nat.card (Bar2 Y)) {E : Subgroup G}
    (hEN : E ≤ normalizer (Y : Set G)) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) :
    ∃ B₀ : Subgroup G, B₀ ≤ E ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut (Bar2 Y)) :=
    Finite.of_injective (fun α : MulAut (Bar2 Y) => (α : Bar2 Y → Bar2 Y)) DFunLike.coe_injective
  set R : Subgroup (MulAut (Bar2 Y)) :=
    (E.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y) with hRdef
  have hRel : IsElemAbelian p R := (hEel.subgroupOf _).map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hRel.isPGroup
  obtain ⟨f, hf⟩ := CFSG.LieType.SeitzGeneration.injective_outer_of_coprime_card (E := R)
    (by rw [hk]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpY))
  have hA : IsElemAbelian p ((R.subgroupOf R).map f) := (hRel.subgroupOf R).map f
  have hR : Nat.card R ≤ p := by
    rw [← Subgroup.card_top (G := ↥R), ← Subgroup.subgroupOf_self R,
      ← Subgroup.card_map_of_injective hf]
    rcases hO with hc | h2
    · exact UCK.card_le_of_isCyclic_of_pow hp.pos hA.2
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (h2.to_subgroup ((R.subgroupOf R).map f))
      rcases hA.isPGroup.card_eq_or_dvd with h1 | hdvd
      · rw [h1]
        exact hp.one_lt.le
      · rw [hj] at hdvd
        exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
          hp2
  exact R847E3.exists_kernel (k := 1) hY hp hEN hEel hEc (by rw [pow_one]; exact hR)

theorem R847E3.normalizer_le_of_thin_three_of_not_normal
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hYN : ¬ (Y.subgroupOf S.M).Normal) (hthin : F08.Thin8 Y) {B₀ : Subgroup G}
    (hB₀M : B₀ ≤ S.M) (hB₀ : IsElemAbelian 3 B₀) (hB₀c : Nat.card B₀ = 3 ^ 2)
    (hB₀Y : ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 S.M) {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three
    (by norm_num) hsp (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hp3 : k.p = 3 := rfl
  have hYM : Y ≤ S.M := hY.1.le
  have h75 : Sec7Core4.Step75 k := k.step75_of_stronglyEmbeddedThree hp3 hK3
  have h76C : Sec7Core4.Step76C k := k.step76C_of_stronglyEmbeddedThree hp3 hK3
  suffices h : ∀ q : ℕ, ∀ X : Subgroup G, X ≤ Y → q.Prime → 5 ≤ q → Nat.card X = q →
      normalizer (X : Set G) ≤ S.M from h q X hXY hq hq5 hXc
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro X hXY hq hq5 hXc
  have hq2 : q ≠ 2 := by omega
  have hqp : q ≠ 3 := by omega
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := uc22ine229_exists_copy hYM Nat.prime_three
    (by norm_num) hq hq2 hB₀M hB₀ hB₀c hB₀Y hXY hXq
  rcases uc22ine229_normalizer_le_or_card_le_two k hp3 hK3 hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have hW := uc22ine229_le_centralizer3 hB₁M hQ hB₁ hB₁X hB₁Y
  obtain ⟨w, ⟨hwY, hwN⟩, hwC⟩ :=
    uc22ine229_exists_not_mem_centralizer_of_thin hY hthin hq hq2 hXY hXc
  rcases uc22ine229_trichotomy hq hXc hwY hwN hwC 3 with
    ⟨t, ht, ht2⟩ | ⟨y, hy, hyP, hy2, hyp, hyq⟩ | ⟨-, u, hu, hup, huC⟩
  ·
    rcases R847E3.normalizer_le_or_l34 hG3 hRee hK3 k hp3 hY hq hXY hXc hB₁M hB₁ hB₁c hB₁X
      hB₁Y ht ht2 with h | ⟨hH', hF⟩
    · exact hnot h
    · exact hYN ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2
        (uc22ine229_l34_decomp hG3 hRee k hp3 hY hXY hq hq5 hXc (hthin q hq hq2) hH' hF).1)
  ·
    obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B₁, x ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one B₁ with h | h
      · rw [h, Subgroup.card_bot] at hB₁c
        exact absurd hB₁c (Nat.one_lt_pow (by norm_num) k.prime.one_lt).ne
      · exact h
    obtain ⟨j, hjM, hjy⟩ := k.exists_not_mem_commute_of_prime h75 k.step72L h76C hH
      ⟨hB₁N hxB, hB₁M hxB⟩ ⟨hy.2, hYM hy.1⟩ (hB₁.isPGroup.to_le (Subgroup.zpowers_le.2 hxB))
      hx1 hyP hy2 hyp ((Subgroup.mem_centralizer_iff.mp (hW hy)) x hxB)
    have hyN := ih (orderOf y) hyq (Subgroup.zpowers y) (Subgroup.zpowers_le.2 hy.1) hyP
      (hyP.five_le_of_ne_two_of_ne_three hy2 hyp) (Nat.card_zpowers y)
    have hjC : j ∈ centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact hjy
    exact hjM (hyN (Subgroup.centralizer_le_normalizer _ hjC))
  ·
    exact huC (k.mem_centralizer_of_commute h75 hH (k.goodZ3_of_config hG3 hRee hp3 hH).1
      (uc22ine229_le_pPrimeCore_normalizer k.prime hq hqp hXc) (le_inf hB₁N hB₁M) hB₁ hB₁c hB₁X
      ⟨hu.2, hYM hu.1⟩ hup fun a ha => (Subgroup.mem_centralizer_iff.mp (hW hu)) a ha)

theorem r8100Step_of_r847E3ThinNNTwo {D : Data G} (h847 : R847E3ThinNNTwo D) :
    ∀ (L : Subgroup G) (n r p : ℕ), L ∈ calC D.M → (conjSetOf D.M L).ncard = 2 →
      (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) → r.Prime → r ≠ 2 → p ∈ D.sig →
        ∀ A : Subgroup G, A ≤ L → Nat.card A = r → normalizer (A : Set G) ≤ D.M := by
  intro L n r p hL h2 hLS hr hr2 hp A hAL hAc
  have hLN : ¬ (L.subgroupOf D.M).Normal := by
    intro hn
    have hle : D.M ≤ normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hn
    have h1 : (conjSetOf D.M L).ncard = 1 := by
      rw [Set.ncard_eq_one]
      refine ⟨L, Set.eq_singleton_iff_unique_mem.2 ⟨PartOne.Section8.mem_conjSetOf_self D.M L,
        fun K hK => ?_⟩⟩
      obtain ⟨g, hg, rfl⟩ := hK
      exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (hle hg)
    omega
  refine h847 L hL hLN (fun s hs hs2 => ?_) A hAL r hr hr2 hAc p hp fun _ => h2
  rw [← pRank_bar2_eq_of_odd (Y := L) hs hs2]
  exact pRank_le_one_of_isL2_or_isSz hLS hs hs2

theorem r847E3ThinNNTwo_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) : R847E3ThinNNTwo (dataOfSetup hS S) := by
  intro Y hY hYN hthin X hXY q hq hq2 hXc p hp hp3
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  have : Fact p.Prime := ⟨hpP⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hrank : CFSG.Open.pRank q S.M ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 S.M
      (dataOfSetup hS S).maxLocal.1).trans (le_of_eq hS.rank)
  have hYM : Y ≤ S.M := hY.1.le
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  by_cases hqs : q ∈ (dataOfSetup hS S).sig
  · exact uc22ine229_normalizer_le_of_mem_sig hSg hY hqs hXY hX1
      (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))
  have hqp : q ≠ p := fun h => hqs (h ▸ hp)
  have hKY : CFSG.IsKGroup (Bar2 Y) :=
    uc22br4_isKGroup_catalog_of_open ((hK.of_le hYM).quotient (CFSG.pCore 2 ↥Y))
  obtain ⟨hs, ht⟩ := hThin (Bar2 Y) hKY hY.2.2 (PartTwo.s13_pCore_bar_eq_bot Y)
    fun r hr hr2 => PartTwo.s13_pRank_bar_le_one hthin hr hr2
  have := hs
  have hZ : center (Bar2 Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Bar2 Y)) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := PartTwo.s13_nonabelian_bar hY
      exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm hab
  obtain ⟨E, hEM, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpP (hSg.three_le p hp)
  have hEN : E ≤ normalizer (Y : Set G) := by
    by_cases h3 : p = 3
    · intro x hx
      refine PartOne.Section8.mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order
        (hp3 h3).le (hEM hx) (Odd.of_dvd_nat (n := p) ?_ (orderOf_dvd_of_pow_eq_one (hEel.2 x hx)))
      rw [h3]
      decide
    · exact uc22ine229_le_normalizer hY hpP (hpP.five_le_of_ne_two_of_ne_three hp2 h3) hq hq2 hXY
        hXc (by rw [hZ, Subgroup.card_bot]; exact hq.not_dvd_one) hrank hEM hEel
  by_cases hpY : p ∣ Nat.card (Bar2 Y)
  ·
    by_contra hN
    have h2 := R847E3.two_le_pRank_normalizer_inf hpP hp2 hq hYM hEM hEN hEel hEc
      (hthin p hpP hp2) (hthin q hq hq2) hXY hXc
    have hH := uc22s13xm_sec7Hyp hpP hp2 hsp hX1 (hXY.trans hYM) hN h2
    obtain ⟨W, hW, π, hπ⟩ := R847E3.exists_le_normalizer_inf_surjective hY hYN hq hq2 hXY hXc
    have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY.2.1
    obtain ⟨rfl, ⟨e⟩⟩ :=
      R847E3.isAlt_of_kf7Use (kf7Use_dataOfSetup hSQ hSE hK3 hS S) hp hH hW π hπ hpY
    have h5 : Nat.card (Outer (Bar2 Y)) = 2 :=
      CFSG.ProperTwoGeneratedCore.BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_five e
    exact hN (r847E3ThinNNOut_dataOfSetup hSE hSEZ hThin hS S Y hY hYN hthin X hXY q hq hq2 hXc 5
      hp le_rfl (by rw [h5]; norm_num))
  have hO : IsCyclic (Outer (Bar2 Y)) ∨ IsPGroup 2 (Outer (Bar2 Y)) := by
    rcases ht with ⟨a, h⟩ | ⟨r, -, -, h⟩ | ⟨a, h⟩ | hJ
    · exact Or.inl (P22y.isCyclic_outer_of_isL2Ev (P22fin.isL2Ev_of_isL2 h).1)
    · exact Or.inr (CFSG.Quasithin.H13.KG838.isPGroup_outer_psl_two_prime
        (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)))
    · obtain ⟨-, -, b, hb, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel h
      exact Or.inl ((CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).isCyclic.mpr
        (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd hb hK).1)
    · obtain ⟨e⟩ : Nonempty (Bar2 Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ
      obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
      have := CFSG.ComponentClassification.BMCase.subsingleton_outer_of_inner
        (CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.forall_inner_of_j1 (e.trans f))
      exact Or.inl inferInstance
  obtain ⟨B₀, hB₀E, hB₀, hB₀c, hB₀Y⟩ :=
    R847E3.exists_B₀_of_not_dvd_card hO hY.1 hpP hp2 hpY hEN hEel hEc
  by_cases h3 : p = 3
  · subst h3
    exact R847E3.normalizer_le_of_thin_three_of_not_normal hG3 hRee hK3 hS S hp hY hYN hthin
      (hB₀E.trans hEM) hB₀ hB₀c hB₀Y hq (hq.five_le_of_ne_two_of_ne_three hq2 hqp) hXY hXc
  · exact R847E3.normalizer_le_of_thin_five_of_cent hSE hSEZ hS S hp
      (hpP.five_le_of_ne_two_of_ne_three hp2 h3) hY hthin (hB₀E.trans hEM) hB₀ hB₀c hB₀Y hq hq2
      hXY hXc

end CFSG.LocalAnalysis.UniquenessCase.UC22
