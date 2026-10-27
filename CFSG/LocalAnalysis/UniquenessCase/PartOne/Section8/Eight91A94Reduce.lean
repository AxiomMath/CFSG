module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Aut
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStrongEmb
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.H13.NQTermAmbientQuotient
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.RankThree.GF2n.Parrott.A1LocalData
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.GroupTheory.PCoreSurjective
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
import CFSG.Quasithin.EmptyFaithful.R3c3Lie
import CFSG.Quasithin.EmptyFaithful.R3c3Rank
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderSplit
import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
import CFSG.LieType.Chevalley.E6GraphInvolutionForms
import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

private theorem k891a94reduce_find_g {G : Type} [Group G] [Finite G] {D : Data G}
    {A : Subgroup G} (hA_le : A ≤ D.M) (hnot : A ∉ uniqueSet D.M) :
    ∃ g : G, A ≤ D.M.map (MulAut.conj g).toMonoidHom ∧
      D.M.map (MulAut.conj g).toMonoidHom ≠ D.M := by
  by_contra h
  apply hnot
  refine ⟨hA_le, fun g hg => ?_⟩
  by_contra hne
  exact h ⟨g, hg, hne⟩

private theorem k891a94reduce_not_dvd_C {G : Type} [Group G] [Finite G] {D : Data G}
    {A : Subgroup G} {p : ℕ} (hsp : IsStronglyPEmbedded p D.M)
    (hNA : normalizer (A : Set G) ≤ D.M)
    {g : G} (hg_ne : D.M.map (MulAut.conj g).toMonoidHom ≠ D.M) :
    ¬ p ∣ Nat.card (↥(D.M.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G))) := by
  have h_g_not_mem : g ∉ D.M := by
    intro hg
    have hg' : g ∈ normalizer (D.M : Set G) := by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
      exact hg
    exact hg_ne (UC6S846.mem_normalizer_iff_map_conj.1 hg')
  have hnd := IsStronglyPEmbedded.not_dvd_card_inf_conj hsp h_g_not_mem
  have hle : D.M.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G) ≤
      D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := by
    refine le_inf ?_ inf_le_left
    exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNA)
  exact fun hd => hnd (hd.trans (Subgroup.card_dvd_of_le hle))

private theorem k891a94reduce_map_normal {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} {g : G} (h : M ≤ normalizer (L : Set G)) :
    M.map (MulAut.conj g).toMonoidHom ≤
      normalizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  rintro x ⟨m, hm, rfl⟩
  rw [UC6S846.mem_normalizer_iff_map_conj]
  rw [Subgroup.map_map]
  have h2 : (MulAut.conj ((MulEquiv.toMonoidHom (MulAut.conj g)) m)).toMonoidHom.comp
      (MulAut.conj g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj m).toMonoidHom := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [h2, ← Subgroup.map_map]
  rw [UC6S846.mem_normalizer_iff_map_conj.mp (h hm)]

private theorem k891a94reduce_is3D4_bar2_map {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} {g : G} (hd4 : Is3D4 (Bar2 L) n) :
    Is3D4 (Bar2 (L.map (MulAut.conj g).toMonoidHom)) n := by
  have e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact CFSG.Blueprint.LieModel.of_mulEquiv (UC6S846.bar2Equiv e) hd4

private theorem k891a94reduce_exists_order_three {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hcard : Nat.card A = 3) : ∃ a ∈ A, orderOf a = 3 := by
  have hdvd : 3 ∣ Nat.card ↥A := by rw [hcard]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 3 (hp := ⟨Nat.prime_three⟩) hdvd
  exact ⟨(a : G), a.2, by rw [Subgroup.orderOf_coe, ha]⟩

private theorem k891a94reduce_dvd_bar2 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {p : ℕ} {g : G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p L = 2) :
    p ∣ Nat.card (Bar2 (L.map (MulAut.conj g).toMonoidHom)) := by
  have hrank' : CFSG.Open.pRank p (L.map (MulAut.conj g).toMonoidHom) = 2 := by
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective L]
    exact hrank
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (L.map (MulAut.conj g).toMonoidHom)
  have hp2dvd : p ^ 2 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rw [show p ^ 2 = Nat.card E by rw [hEcard, hrank']]
    exact Subgroup.card_dvd_of_le hE
  have hp_dvd_L' : p ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hp2dvd
  have hnot : ¬ p ∣ Nat.card ↥(CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom)) :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne
      (K := ↥(L.map (MulAut.conj g).toMonoidHom)) hp hp2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.pCore 2 ↥(L.map (MulAut.conj g).toMonoidHom))
  rw [hcard] at hp_dvd_L'
  rcases (Nat.Prime.dvd_mul hp).mp hp_dvd_L' with h | h
  · exact h
  · exact absurd h hnot

private theorem k891a94reduce_eq_zpowers {G : Type} [Group G] [Finite G] {A : Subgroup G} {a : G}
    (hcard : Nat.card A = 3) (haA : a ∈ A) (haord : orderOf a = 3) :
    A = Subgroup.zpowers a := by
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) (by
    rw [Nat.card_zpowers, haord]
    exact le_of_eq hcard)).symm

private theorem k891a94reduce_alpha_exists {G : Type} [Group G] [Finite G]
    {L' A : Subgroup G} {p : ℕ} {a : G}
    (haA : a ∈ A) (haord : orderOf a = 3) (hA_card : Nat.card A = 3)
    (hA_normalizes : A ≤ normalizer (L' : Set G))
    (hnotp : ¬ p ∣ Nat.card (↥(L' ⊓ centralizer (A : Set G))))
    (hp_dvd : p ∣ Nat.card (Bar2 L')) :
    ∃ α : MulAut (Bar2 L'),
      orderOf α = 3 ∧
      R891Fix α = barImage L' (L' ⊓ centralizer (A : Set G)) ∧
      ¬ p ∣ Nat.card (↥(R891Fix α)) := by
  classical
  have hA_eq : A = Subgroup.zpowers a := k891a94reduce_eq_zpowers hA_card haA haord
  have haL' : a ∈ normalizer (L' : Set G) :=
    hA_normalizes (by rw [hA_eq]; exact Subgroup.mem_zpowers a)
  let φ : MulAut ↥L' := Subgroup.normalizerMonoidHom (H := L') ⟨a, haL'⟩
  let N : Subgroup ↥L' := CFSG.pCore 2 ↥L'
  have hNn : N.Normal := CFSG.pCore_normal
  have hN : ∀ n ∈ N, φ n ∈ N := by
    intro n hn
    have hmap : N.map φ.toMonoidHom = N :=
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : N.Characteristic) φ
    exact hmap ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hn
  have hr : ¬ 3 ∣ Nat.card N :=
    CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥L')
      Nat.prime_three (by norm_num)
  let α : MulAut (Bar2 L') :=
    CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism N φ
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨a, haL'⟩ : normalizer (L' : Set G)) ^ 3 = 1 := by
      ext
      show a ^ 3 = (1 : G)
      rw [← haord]
      exact pow_orderOf_eq_one a
    change (Subgroup.normalizerMonoidHom (H := L') ⟨a, haL'⟩) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hα3 : α ^ 3 = 1 := by
    change (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism N φ) ^ 3 = 1
    rw [← map_pow, hφ3, map_one]
  have hα_eq : ∀ z : Bar2 L',
      α z = CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap
        φ N hN z := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      change CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence N φ
        (QuotientGroup.mk' N x) = _
      rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientEquivalence_apply,
        CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.quotientMap_mk]
      rfl
  have hA_set : (A : Set G) = (Subgroup.zpowers a : Set G) := congrArg _ hA_eq
  have hfix : R891Fix α = barImage L' (L' ⊓ centralizer (A : Set G)) := by
    ext z
    rw [R891Fix]
    change α z = z ↔ z ∈ barImage L' (L' ⊓ centralizer (A : Set G))
    rw [hα_eq z]
    rw [@CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_quotient_iff
      (↥L') _ _ 3 ⟨Nat.prime_three⟩ φ hφ3 N hNn hN hr z]
    constructor
    · rintro ⟨y, hyz, hyfix⟩
      refine Subgroup.mem_map.2 ⟨y, ?_, hyz⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨y.2, ?_⟩
      rw [hA_set, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      have h1 : a * (y : G) * a⁻¹ = (y : G) := by
        have := congrArg (fun w : ↥L' => (w : G)) hyfix
        simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
      have h2 : a * (y : G) = (y : G) * a := by
        calc a * (y : G) = (a * (y : G) * a⁻¹) * a := by group
          _ = (y : G) * a := by rw [h1]
      exact h2.symm
    · rintro ⟨y, hy, hyz⟩
      refine ⟨y, hyz, ?_⟩
      have hy_cen : (y : G) ∈ centralizer (A : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
      rw [hA_set, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff] at hy_cen
      apply Subtype.ext
      simp only [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [← hy_cen]; group
  have hnotp_fix : ¬ p ∣ Nat.card (↥(R891Fix α)) := by
    rw [hfix]
    have hdvd : Nat.card (↥(barImage L' (L' ⊓ centralizer (A : Set G)))) ∣
        Nat.card (↥(L' ⊓ centralizer (A : Set G))) := by
      rw [barImage]
      refine (Subgroup.card_map_dvd (H := (L' ⊓ centralizer (A : Set G)).subgroupOf L')
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L'))).trans ?_
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).dvd
    exact fun h => hnotp (h.trans hdvd)
  have hα_ne : α ≠ 1 := by
    intro hα1
    have htop : R891Fix α = ⊤ := by
      ext z
      simp [R891Fix, hα1]
    have hcard : Nat.card (↥(R891Fix α)) = Nat.card (Bar2 L') := by rw [htop]; simp
    exact hnotp_fix (hcard ▸ hp_dvd)
  refine ⟨α, ?_, hfix, hnotp_fix⟩
  exact orderOf_eq_prime hα3 hα_ne

private theorem k891a94reduce_quot_pCore_equiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hY : CFSG.pCore 2 Y = ⊥) : Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* Y) := by
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2) f hf hker
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hY).trans QuotientGroup.quotientBot)⟩

private theorem k891a94reduce_not_isPGroup_two_of_le_pRank_three {X : Type} [Group X]
    [Finite X] (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : ¬ IsPGroup 2 X := by
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup X)
  have hEcard' : 9 ≤ Nat.card E := by
    rw [hEcard]
    simpa using pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 3) h
  have hE_ne_bot : E ≠ ⊥ := by
    intro hbot
    rw [hbot] at hEcard'
    simp at hEcard'
  obtain ⟨y, hyE, hy_ne_one⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one E).mp ((Subgroup.nontrivial_iff_ne_bot E).mpr hE_ne_bot)
  have hnot_top : ¬ IsPGroup 2 (⊤ : Subgroup X) :=
    CFSG.LieType.Chevalley.E6GraphInvolution.not_isPGroup_two_of_mem
      (Subgroup.mem_top y) (hEel.2 y hyE) hy_ne_one
  exact fun hp => hnot_top (hp.of_equiv Subgroup.topEquiv.symm)

private theorem k891a94reduce_pCore_bot_of_shape
    {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (h : IsG2 X n ∨ R891SL3Two X n ∨ R891L3Pi X n) :
    CFSG.pCore 2 X = ⊥ := by
  rcases h with h | h | h
  · have hm : CFSG.Blueprint.LieModel X .G2 0 2 n := h
    have hcheb : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 n :=
      hm.chevalleyExceptionalModel (by decide)
    let hsimple : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_g2_simplicity X 2 n hcheb).2
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.Quasithin.R3c3.two_le_pRank_three_isG2 (f := n) hcheb
    exact @CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple X _ hsimple
      (k891a94reduce_not_isPGroup_two_of_le_pRank_three hrank)
  · unfold R891SL3Two at h
    rcases h with ⟨rfl, -⟩ | ⟨-, hEven, hcov⟩ | ⟨-, hOdd, hcov⟩
    · omega
    · exact CFSG.LocalAnalysis.RankThreeUC.S15.pCore_two_eq_bot_of_quasisimple
        hcov.1.1 hcov.1.2 (fun z hz => by
          have h3 : Nat.card ↥(Subgroup.center X) = 3 := hcov.2.1
          have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.center X) :=
            Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz
          rw [h3] at hdvd
          exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
    · exact CFSG.LocalAnalysis.RankThreeUC.S15.pCore_two_eq_bot_of_quasisimple
        hcov.1.1 hcov.1.2 (fun z hz => by
          have h3 : Nat.card ↥(Subgroup.center X) = 3 := hcov.2.1
          have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.center X) :=
            Subgroup.orderOf_dvd_natCard (Subgroup.center X) hz
          rw [h3] at hdvd
          exact orderOf_dvd_iff_pow_eq_one.mp hdvd)
  · unfold R891L3Pi at h
    rcases h with ⟨hEven, hL⟩ | ⟨hOdd, hL⟩
    · have hsimple : IsSimpleGroup X :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
        CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_two_even hEven
          (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))
      exact @CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple X _ hsimple
        (k891a94reduce_not_isPGroup_two_of_le_pRank_three hrank)
    · have hsimple : IsSimpleGroup X :=
        CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
      have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
        CFSG.Quasithin.R3c3.two_le_pRank_three_isPSU_two_odd hOdd
          (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))
      exact @CFSG.CGT.PushingUpLit.CGT6.pCore_eq_bot_of_simple X _ hsimple
        (k891a94reduce_not_isPGroup_two_of_le_pRank_three hrank)

private theorem k891a94reduce_threeCover_lieModel_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (e : X ≃* Y)
    (h : ThreeCover (fun Z _ => CFSG.Blueprint.LieModel Z t n p f) X) :
    ThreeCover (fun Z _ => CFSG.Blueprint.LieModel Z t n p f) Y := by
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv e.symm h.1
  · exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans h.2.1
  · exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e h.2.2

private theorem k891a94reduce_shape_transport {X Y : Type} [Group X] [Group Y] {n : ℕ}
    (hn : 2 ≤ n) (e : X ≃* Y) (h : IsG2 X n ∨ R891SL3Two X n ∨ R891L3Pi X n) :
    IsG2 Y n ∨ R891SL3Two Y n ∨ R891L3Pi Y n := by
  rcases h with h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e h)
  · refine Or.inr (Or.inl ?_)
    unfold R891SL3Two at h ⊢
    rcases h with ⟨rfl, -⟩ | ⟨hn2, hEven, hcov⟩ | ⟨hn2, hOdd, hcov⟩
    · omega
    · exact Or.inr (Or.inl ⟨hn2, hEven, k891a94reduce_threeCover_lieModel_of_mulEquiv e hcov⟩)
    · exact Or.inr (Or.inr ⟨hn2, hOdd, k891a94reduce_threeCover_lieModel_of_mulEquiv e hcov⟩)
  · refine Or.inr (Or.inr ?_)
    unfold R891L3Pi at h ⊢
    rcases h with ⟨hEven, hL⟩ | ⟨hOdd, hL⟩
    · exact Or.inl ⟨hEven, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩
    · exact Or.inr ⟨hOdd, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩

private theorem k891a94reduce_cfg_nge2
    {G : Type} [Group G] [Finite G] {D : Data G}
    {A : Subgroup G} {n : ℕ} {L' : Subgroup G} {α : MulAut (Bar2 L')}
    (hn : 2 ≤ n)
    (hC_le_M : L' ⊓ centralizer (A : Set G) ≤ D.M)
    (hC_le_cen : L' ⊓ centralizer (A : Set G) ≤ centralizer (A : Set G))
    (hC_le_L' : L' ⊓ centralizer (A : Set G) ≤ L')
    (hfix : R891Fix α = barImage L' (L' ⊓ centralizer (A : Set G)))
    (_hperf : ⁅DerInf8 (R891Fix α), DerInf8 (R891Fix α)⁆ = DerInf8 (R891Fix α))
    (hshape : IsG2 ↥(DerInf8 (R891Fix α)) n ∨ R891SL3Two ↥(DerInf8 (R891Fix α)) n ∨
      R891L3Pi ↥(DerInf8 (R891Fix α)) n) :
    ∃ K K₀ : Subgroup G, R891Cfg894 D A K K₀ n := by
  let C : Subgroup G := L' ⊓ centralizer (A : Set G)
  let K : Subgroup G := DerInf8 C
  have hK_le_C : K ≤ C := by
    show DerInf8 C ≤ C
    rw [show F08.DerInf8 C = (CFSG.perfectResidual C).map C.subtype from rfl]
    exact Subgroup.map_subtype_le _
  have hK_le_L' : K ≤ L' := hK_le_C.trans hC_le_L'
  have hK_le_M : K ≤ D.M := hK_le_C.trans hC_le_M
  have hK_le_cen : K ≤ centralizer (A : Set G) := hK_le_C.trans hC_le_cen
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (isPerfect_derInf8 C)
  have hbar : barImage L' K = DerInf8 (R891Fix α) := by
    have h1 : barImage L' C = R891Fix α := hfix.symm
    have h2 := barImage_derInf8_eq (L := L') hC_le_L' h1
    simpa [K] using h2
  have hDbot : CFSG.pCore 2 ↥(DerInf8 (R891Fix α)) = ⊥ :=
    k891a94reduce_pCore_bot_of_shape hn hshape
  have hbar2 : Nonempty (Bar2 K ≃* ↥(DerInf8 (R891Fix α))) := by
    let q : ↥K →* Bar2 L' :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L')).comp (Subgroup.inclusion hK_le_L')
    have hqrange : q.range = DerInf8 (R891Fix α) := by
      have h1 : q.range = barImage L' K := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
        · intro hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
          refine ⟨⟨z.1, Subgroup.mem_subgroupOf.1 hz⟩, ?_⟩
          simpa [q, Subgroup.inclusion] using hzy
      rw [h1, hbar]
    let qc : ↥K →* ↥q.range := q.codRestrict q.range (fun x => ⟨x, rfl⟩)
    let e0 : ↥q.range ≃* ↥(DerInf8 (R891Fix α)) := MulEquiv.subgroupCongr hqrange
    let f : ↥K →* ↥(DerInf8 (R891Fix α)) := e0.toMonoidHom.comp qc
    have hqcsurj : Function.Surjective qc := by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 y.2
      exact ⟨x, Subtype.ext hx⟩
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := e0.surjective y
      obtain ⟨z, hz⟩ := hqcsurj x
      exact ⟨z, by
        change e0 (qc z) = y
        rw [hz, hx]⟩
    have hfker : IsPGroup 2 f.ker := by
      have h1 : f.ker = qc.ker := by
        ext x
        simp [f, e0, MonoidHom.mem_ker]
      rw [h1]
      have h2 : qc.ker = q.ker := MonoidHom.ker_codRestrict q q.range _
      rw [h2]
      have h3 : q.ker = (CFSG.pCore 2 ↥L').comap (Subgroup.inclusion hK_le_L') := by
        ext x
        simp [q, MonoidHom.mem_ker, Subgroup.mem_comap]
      rw [h3]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L')).comap_of_injective
        (Subgroup.inclusion hK_le_L') (Subgroup.inclusion_injective hK_le_L')
    exact k891a94reduce_quot_pCore_equiv f hfsurj hfker hDbot
  obtain ⟨e⟩ := hbar2
  refine ⟨K, K, hK_le_M, hK_le_cen, ?_, le_rfl, ?_, ?_, ?_⟩
  · intro h1; omega
  · rw [Subgroup.subgroupOf_self]; infer_instance
  · intro h1; omega
  · exact Or.inl ⟨hn, rfl, hKperf, k891a94reduce_shape_transport hn e.symm hshape⟩

private theorem k891a94reduce_opp_idem {G : Type} [Group G] (X : Subgroup G) :
    Opp 2 (Opp 2 X) = Opp 2 X := by
  apply le_antisymm
  · rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, -⟩
    exact hx
  · rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, hxord⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hxX, hxord⟩, hxord⟩

private theorem k891a94reduce_r891Odd_normal {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ((R891Odd K).subgroupOf K).Normal := by
  have hle : R891Odd K ≤ K := by
    rw [R891Odd]
    exact (Subgroup.closure_le _).mpr (fun x hx => hx.1)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro k hk
  rw [UC6S846.mem_normalizer_iff_map_conj]
  rw [R891Odd, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨hyK, hyodd⟩, rfl⟩
    refine ⟨K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk), ?_⟩
    have h : orderOf ((MulAut.conj k) y) = orderOf y :=
      MulEquiv.orderOf_eq (MulAut.conj k) y
    exact h ▸ hyodd
  · rintro ⟨hxK, hxodd⟩
    refine ⟨(MulAut.conj k)⁻¹ x, ⟨K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk, ?_⟩, ?_⟩
    · have h : orderOf ((MulAut.conj k)⁻¹ x) = orderOf x :=
        MulEquiv.orderOf_eq (MulAut.conj k)⁻¹ x
      exact h ▸ hxodd
    · simpa using MulEquiv.apply_symm_apply (MulAut.conj k) x

private theorem k891a94reduce_closure_subgroupOf {G : Type} [Group G] {L : Subgroup G}
    (S : Set G) (hS : S ⊆ L) :
    (Subgroup.closure S).subgroupOf L = Subgroup.closure (L.subtype ⁻¹' S) := by
  have himg : L.subtype '' (L.subtype ⁻¹' S) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le L).mpr hS),
    MonoidHom.map_closure, himg]

private theorem k891a94reduce_orderOf_two_pow_of_mk {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {y : ↥L} {k : ℕ}
    (h : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y) = 2 ^ k) :
    ∃ i : ℕ, orderOf (y : G) = 2 ^ i := by
  have hmem : y ^ (2 ^ k) ∈ (CFSG.pCore 2 ↥L : Subgroup ↥L) := by
    have hker : y ^ (2 ^ k) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rw [MonoidHom.mem_ker, map_pow, ← h, pow_orderOf_eq_one]
    rwa [QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)] at hker
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    (⟨y ^ (2 ^ k), hmem⟩ : ↥(CFSG.pCore 2 ↥L))
  have hj' : orderOf (y ^ (2 ^ k) : ↥L) = 2 ^ j := by
    change orderOf ((⟨y ^ (2 ^ k), hmem⟩ : ↥(CFSG.pCore 2 ↥L)) : ↥L) = 2 ^ j
    rw [Subgroup.orderOf_coe]
    exact hj
  have h1 : y ^ (2 ^ k * 2 ^ j) = 1 := by
    rw [pow_mul, ← hj']
    exact pow_orderOf_eq_one (y ^ (2 ^ k) : ↥L)
  have hdvd : orderOf y ∣ 2 ^ (k + j) := by
    apply orderOf_dvd_of_pow_eq_one
    simpa [pow_add, pow_mul] using h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨i, by rw [Subgroup.orderOf_coe y, hi]⟩

private theorem k891a94reduce_barImage_opp {G : Type} [Group G] [Finite G]
    {L X : Subgroup G} (hXL : X ≤ L) :
    barImage L (Opp 2 X) = Opp 2 (barImage L X) := by
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let S : Set G := {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = 2 ^ k}
  have hS : S ⊆ L := fun x hx => hXL hx.1
  have hOpp : Opp 2 X = Subgroup.closure S := rfl
  have hbar : barImage L (Opp 2 X) = Subgroup.closure (π '' (L.subtype ⁻¹' S)) := by
    rw [hOpp, barImage, k891a94reduce_closure_subgroupOf S hS, MonoidHom.map_closure]
  rw [hbar, Opp, CFSG.RankThree.PartOne.pElementSubgroup]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [barImage, Subgroup.mem_map]
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    · obtain ⟨k, hk⟩ := hx.2
      have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe x).symm.trans hk
      have hd : orderOf (π x) ∣ 2 ^ k := by
        have := orderOf_map_dvd π x
        rwa [hk'] at this
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
      exact ⟨j, hj⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨hzX, k, hk⟩
    rw [barImage, Subgroup.mem_map] at hzX
    obtain ⟨y, hy, hyz⟩ := hzX
    rw [← hyz]
    refine Subgroup.subset_closure ⟨y, ?_, rfl⟩
    have hz : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y) = 2 ^ k := by
      rw [hyz]; exact hk
    obtain ⟨i, hi⟩ := k891a94reduce_orderOf_two_pow_of_mk hz
    exact ⟨Subgroup.mem_subgroupOf.mp hy, ⟨i, hi⟩⟩

private theorem k891a94reduce_barImage_r891Odd {G : Type} [Group G] [Finite G]
    {L X : Subgroup G} (hXL : X ≤ L) :
    barImage L (R891Odd X) = R891Odd (barImage L X) := by
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let S : Set G := {x : G | x ∈ X ∧ Odd (orderOf x)}
  have hS : S ⊆ L := fun x hx => hXL hx.1
  have hOdd : R891Odd X = Subgroup.closure S := rfl
  have hbar : barImage L (R891Odd X) = Subgroup.closure (π '' (L.subtype ⁻¹' S)) := by
    rw [hOdd, barImage, k891a94reduce_closure_subgroupOf S hS, MonoidHom.map_closure]
  rw [hbar, R891Odd]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [barImage, Subgroup.mem_map]
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    · have hxodd : Odd (orderOf x) := by
        rw [← Subgroup.orderOf_coe x]
        exact hx.2
      exact Odd.of_dvd_nat hxodd (orderOf_map_dvd π x)
  · refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨hzX, hzodd⟩
    rw [barImage, Subgroup.mem_map] at hzX
    obtain ⟨y, hy, hyz⟩ := hzX
    rw [← hyz]
    by_cases hm1 : orderOf (π y) = 1
    · rw [orderOf_eq_one_iff.mp hm1]
      exact Subgroup.one_mem _
    · have hm_odd : Odd (orderOf (π y)) := by rw [hyz]; exact hzodd
      have hm_gt : 1 < orderOf (π y) :=
        lt_of_le_of_ne (Nat.succ_le_of_lt (orderOf_pos _)) (Ne.symm hm1)
      obtain ⟨n, hn1, hn2⟩ :=
        CFSG.RankThree.GF2n.Parrott.exists_pow_lift_orderOf_eq π
          (by rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
              exact CFSG.pCore_isPGroup) hm_odd hm_gt rfl
      rw [← hn1]
      refine Subgroup.subset_closure ⟨y ^ n, ?_, rfl⟩
      refine ⟨X.pow_mem (Subgroup.mem_subgroupOf.mp hy) n, ?_⟩
      rw [show orderOf (L.subtype (y ^ n)) = orderOf (y ^ n : ↥L) from
        Subgroup.orderOf_coe (y ^ n), hn2]
      exact hm_odd

private theorem k891a94reduce_extra_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {p n : ℕ} (h : IsExtraspecialExpP p n A) : IsExtraspecialExpP p n B := by
  unfold IsExtraspecialExpP at h ⊢
  obtain ⟨hcard, hexp, hcomm, hcenter⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hcard
  · rw [← Monoid.exponent_eq_of_mulEquiv e]; exact hexp
  · have h1 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    have h2 : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
    rw [← h1, hcomm, h2]
  · have hcard : Nat.card (center B) = Nat.card (center A) := by
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective (center A) e.toMonoidHom e.injective).toEquiv).symm
    rw [hcard]; exact hcenter

private theorem k891a94reduce_e9_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : R891E9 A) : R891E9 B := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

private theorem k891a94reduce_isPGroup_three_of_shape {X : Type} [Group X] [Finite X]
    (h : IsExtraspecialExpP 3 1 X ∨ R891E9 X) : IsPGroup 3 X := by
  rcases h with h | h
  · obtain ⟨hcard, -⟩ := h
    exact IsPGroup.of_card (n := 3) (by simpa using hcard)
  · obtain ⟨e⟩ := h
    exact IsPGroup.of_card (n := 2) (by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      decide)

private theorem k891a94reduce_pCore_two_eq_bot_of_isPGroup_three {X : Type} [Group X] [Finite X]
    (h3 : IsPGroup 3 X) : CFSG.pCore 2 X = ⊥ := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  obtain ⟨m, hm⟩ := h3.exists_card_eq
  have hdvd : 2 ^ k ∣ 3 ^ m := by
    rw [← hk, ← hm]
    simpa using Subgroup.card_dvd_of_le (show CFSG.pCore 2 X ≤ (⊤ : Subgroup X) from le_top)
  have hk0 : k = 0 := by
    by_contra hk'
    have h2 : 2 ∣ 3 ^ m := dvd_trans (dvd_pow_self 2 hk') hdvd
    exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) (by norm_num)
  have hcard : Nat.card (CFSG.pCore 2 X) = 1 := by rw [hk, hk0, pow_zero]
  exact Subgroup.card_eq_one.mp hcard

private theorem k891a94reduce_eq_of_map_eq {P Q : Type} [Group P] [Group Q]
    (f : P →* Q) {U V W : Subgroup P} (hU : U ≤ W) (hV : V ≤ W)
    (hdisj : Disjoint W f.ker) (h : U.map f = V.map f) : U = V := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : f x ∈ V.map f := h ▸ Subgroup.mem_map_of_mem f hx
    obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.1 hx'
    have hker : v⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hvx]
      simp
    have hbot : v⁻¹ * x ∈ (⊥ : Subgroup P) :=
      hdisj.le_bot ⟨W.mul_mem (W.inv_mem (hV hv)) (hU hx), hker⟩
    rw [Subgroup.mem_bot] at hbot
    rw [(inv_mul_eq_one.mp hbot).symm]
    exact hv
  · intro x hx
    have hx' : f x ∈ U.map f := h.symm ▸ Subgroup.mem_map_of_mem f hx
    obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 hx'
    have hker : u⁻¹ * x ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hux]
      simp
    have hbot : u⁻¹ * x ∈ (⊥ : Subgroup P) :=
      hdisj.le_bot ⟨W.mul_mem (W.inv_mem (hU hu)) (hV hx), hker⟩
    rw [Subgroup.mem_bot] at hbot
    rw [(inv_mul_eq_one.mp hbot).symm]
    exact hu

private theorem k891a94reduce_commutator_subgroupOf {G : Type} [Group G]
    {A B L' : Subgroup G} (hA : A ≤ L') (hB : B ≤ L') :
    ⁅A, B⁆.subgroupOf L' = ⁅A.subgroupOf L', B.subgroupOf L'⁆ := by
  have hcomm : ⁅A, B⁆ ≤ L' := Subgroup.commutator_le.mpr fun a ha b hb =>
    L'.mul_mem (L'.mul_mem (L'.mul_mem (hA ha) (hB hb)) (L'.inv_mem (hA ha))) (L'.inv_mem (hB hb))
  apply Subgroup.map_injective (Subgroup.subtype_injective L')
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_commutator,
    Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left hcomm, inf_of_le_left hA, inf_of_le_left hB]

private theorem k891a94reduce_mem_pCoreOf {G : Type} [Group G] [Finite G]
    {L' K₀ : Subgroup G} (hK0 : K₀ ≤ L') {x : ↥L'} (hx : (x : G) ∈ K₀)
    (h2 : x ∈ CFSG.pCore 2 ↥L') : (x : G) ∈ pCoreOf 2 K₀ := by
  let N : Subgroup ↥K₀ := (CFSG.pCore 2 ↥L').comap (Subgroup.inclusion hK0)
  have hNn : N.Normal :=
    Subgroup.Normal.comap (CFSG.pCore_normal (p := 2) (G := ↥L')) (Subgroup.inclusion hK0)
  have hNp : IsPGroup 2 N :=
    IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2) (G := ↥L'))
      (Subgroup.inclusion hK0) (Subgroup.inclusion_injective hK0)
  have hxN : (⟨(x : G), hx⟩ : ↥K₀) ∈ N := by
    show (⟨(x : G), hK0 hx⟩ : ↥L') ∈ CFSG.pCore 2 ↥L'
    simpa using h2
  exact Subgroup.mem_map_of_mem K₀.subtype
    (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hNp hxN)

private theorem k891a94reduce_relIndex_map_of_ker {G Q : Type} [Group G] [Group Q]
    {L' K₀ W : Subgroup G} (f : ↥L' →* Q) (hW : W ≤ K₀) (hK0 : K₀ ≤ L')
    (hker : ∀ x : ↥L', (x : G) ∈ K₀ → f x = 1 → (x : G) ∈ W) :
    ((W.subgroupOf L').map f).relIndex ((K₀.subgroupOf L').map f) = W.relIndex K₀ := by
  let K' : Subgroup ↥L' := K₀.subgroupOf L'
  let W' : Subgroup ↥L' := W.subgroupOf L'
  have hW'K' : W' ≤ K' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hW (Subgroup.mem_subgroupOf.mp hx))
  let g : ↥K' →* Q := f.comp K'.subtype
  let H : Subgroup ↥K' := W'.subgroupOf K'
  have hkerH : g.ker ≤ H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hker x.1 x.2 hx
  have hmapH : H.map g = (W.subgroupOf L').map f := by
    change (W'.subgroupOf K').map (f.comp K'.subtype) = (W.subgroupOf L').map f
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hW'K']
  have hmapTop : (⊤ : Subgroup ↥K').map g = (K₀.subgroupOf L').map f := by
    change (⊤ : Subgroup ↥K').map (f.comp K'.subtype) = (K₀.subgroupOf L').map f
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  have hmain := Subgroup.relIndex_map_map g H ⊤
  rw [sup_eq_left.mpr hkerH, top_sup_eq, Subgroup.relIndex_top_right] at hmain
  rw [hmapH, hmapTop] at hmain
  rw [hmain]
  have h1 : W'.relIndex K' = W.relIndex K₀ := by
    change (W.comap L'.subtype).relIndex (K₀.subgroupOf L') = W.relIndex K₀
    rw [Subgroup.relIndex_comap (H := W) L'.subtype (K₀.subgroupOf L'),
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hK0]
  rw [← h1]
  rfl

private theorem k891a94reduce_barImage_conj {G : Type} [Group G] [Finite G]
    {L' W : Subgroup G} {k : G} (hk : k ∈ L') (hW : W ≤ L') :
    barImage L' (W.map (MulAut.conj k).toMonoidHom) =
      (barImage L' W).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨k, hk⟩)).toMonoidHom := by
  ext y
  constructor
  · intro hy
    rw [barImage, Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.mem_map]
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨w, hW hw⟩, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
    · have ha : (⟨k, hk⟩ * ⟨w, hW hw⟩ * ⟨k, hk⟩⁻¹ : ↥L') = x := by
        ext
        simpa [MulAut.conj_apply] using hwv
      rw [← hxy, ← ha]
      show (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨k, hk⟩))
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨w, hW hw⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L') (⟨k, hk⟩ * ⟨w, hW hw⟩ * ⟨k, hk⟩⁻¹)
      simp only [MulAut.conj_apply, map_mul, map_inv]
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [barImage, Subgroup.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    rw [Subgroup.mem_subgroupOf] at hw
    rw [barImage, Subgroup.mem_map]
    refine ⟨⟨k, hk⟩ * ⟨w, hW hw⟩ * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem _ hw
    · rw [← hzy, ← hwz]
      show QuotientGroup.mk' (CFSG.pCore 2 ↥L') (⟨k, hk⟩ * ⟨w, hW hw⟩ * ⟨k, hk⟩⁻¹) =
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨k, hk⟩))
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨w, hW hw⟩)
      simp [MulAut.conj_apply]

private theorem k891a94reduce_r891Odd_le_of_map {G : Type} [Group G] [Finite G]
    {L' K N : Subgroup G} (hKL : K ≤ L') (hNK : N ≤ R891Odd K)
    (hnorm : ∀ k ∈ K, N.map (MulAut.conj k).toMonoidHom = N)
    (hmap : barImage L' N = barImage L' (R891Odd K)) : R891Odd K ≤ N := by
  have hOK : R891Odd K ≤ K := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hN' : (N.subgroupOf (R891Odd K)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hnorm (g : G) (hOK g.2)
    rw [← h]
    exact ⟨(n : G), hn, by simp [MulAut.conj_apply]⟩⟩
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  obtain ⟨hxK, hodd⟩ := hx
  have hxO : x ∈ R891Odd K := Subgroup.subset_closure ⟨hxK, hodd⟩
  have hxL : x ∈ L' := hKL hxK
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L') ⟨x, hxL⟩ ∈ barImage L' N := by
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ (by simpa [Subgroup.mem_subgroupOf] using hxO)
  obtain ⟨c, hcN, hcx⟩ := Subgroup.mem_map.mp hmem
  rw [Subgroup.mem_subgroupOf] at hcN
  have ht2 : c⁻¹ * ⟨x, hxL⟩ ∈ CFSG.pCore 2 ↥L' := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L')]
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L') (c⁻¹ * ⟨x, hxL⟩) = 1
    rw [map_mul, map_inv, hcx, inv_mul_cancel]
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L')).exists_orderOf_eq_pow
    (⟨c⁻¹ * ⟨x, hxL⟩, ht2⟩ : ↥(CFSG.pCore 2 ↥L'))
  have hj' : orderOf ((c : G)⁻¹ * x) = 2 ^ j := by
    have h1 : orderOf (c⁻¹ * ⟨x, hxL⟩ : ↥L') = 2 ^ j :=
      (Subgroup.orderOf_coe (⟨c⁻¹ * ⟨x, hxL⟩, ht2⟩ : ↥(CFSG.pCore 2 ↥L'))).trans hj
    have h2 : ((c⁻¹ * ⟨x, hxL⟩ : ↥L') : G) = (c : G)⁻¹ * x := rfl
    rw [← h2, Subgroup.orderOf_coe]
    exact h1
  let φ : ↥(R891Odd K) →* (↥(R891Odd K) ⧸ N.subgroupOf (R891Odd K)) :=
    QuotientGroup.mk' (N.subgroupOf (R891Odd K))
  let xx : ↥(R891Odd K) := ⟨x, hxO⟩
  let cc : ↥(R891Odd K) := ⟨(c : G), hNK hcN⟩
  have hφc : φ cc = 1 :=
    (QuotientGroup.eq_one_iff cc).mpr (by simpa [Subgroup.mem_subgroupOf] using hcN)
  have hφ : φ xx = φ (cc⁻¹ * xx) := by rw [map_mul, map_inv, hφc, inv_one, one_mul]
  have h1 : orderOf (φ xx) ∣ orderOf x := by
    have h2 : orderOf xx = orderOf x := by
      rw [← Subgroup.orderOf_coe xx]
    rw [← h2]
    exact orderOf_map_dvd φ xx
  have h2 : orderOf (φ xx) ∣ 2 ^ j := by
    rw [hφ]
    refine (orderOf_map_dvd φ (cc⁻¹ * xx)).trans ?_
    rw [← Subgroup.orderOf_coe (cc⁻¹ * xx),
      show ((cc⁻¹ * xx : ↥(R891Odd K)) : G) = (c : G)⁻¹ * x from rfl]
    exact dvd_of_eq hj'
  have hcop : Nat.Coprime (orderOf x) (2 ^ j) :=
    (Nat.coprime_two_right.mpr hodd).pow_right j
  have h11 : orderOf (φ xx) = 1 :=
    (hcop.coprime_dvd_left h1).eq_one_of_dvd h2
  have : xx ∈ N.subgroupOf (R891Odd K) :=
    (QuotientGroup.eq_one_iff xx).mp (orderOf_eq_one_iff.mp h11)
  simpa [Subgroup.mem_subgroupOf] using this

private theorem k891a94reduce_cfg_none {G : Type} [Group G] [Finite G] {D : Data G}
    {A : Subgroup G} {n : ℕ} {L' : Subgroup G} {α : MulAut (Bar2 L')}
    (hn : n = 1)
    (hC_le_M : L' ⊓ centralizer (A : Set G) ≤ D.M)
    (hC_le_cen : L' ⊓ centralizer (A : Set G) ≤ centralizer (A : Set G))
    (hC_le_L' : L' ⊓ centralizer (A : Set G) ≤ L')
    (hfix : R891Fix α = barImage L' (L' ⊓ centralizer (A : Set G)))
    (hcomm : ⁅R891Odd (Opp 2 (R891Fix α)), Opp 2 (R891Fix α)⁆ =
      R891Odd (Opp 2 (R891Fix α)))
    (hshape : IsExtraspecialExpP 3 1 ↥(R891Odd (Opp 2 (R891Fix α))) ∨
      R891E9 ↥(R891Odd (Opp 2 (R891Fix α))))
    (hnorm : ∀ W : Subgroup (Bar2 L'), W ≤ R891Odd (Opp 2 (R891Fix α)) →
      W.relIndex (R891Odd (Opp 2 (R891Fix α))) = 3 →
        ¬ ∀ k ∈ Opp 2 (R891Fix α), W.map (MulAut.conj k).toMonoidHom = W) :
    ∃ K K₀ : Subgroup G, R891Cfg894 D A K K₀ n := by
  let C : Subgroup G := L' ⊓ centralizer (A : Set G)
  let K : Subgroup G := Opp 2 C
  let K₀ : Subgroup G := R891Odd K
  have hK_le_C : K ≤ C := by
    rw [show K = Opp 2 C from rfl, Opp, CFSG.RankThree.PartOne.pElementSubgroup]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hK_le_L' : K ≤ L' := hK_le_C.trans hC_le_L'
  have hK0_le_K : K₀ ≤ K := by
    rw [show K₀ = R891Odd K from rfl, R891Odd]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hK0_le_L' : K₀ ≤ L' := hK0_le_K.trans hK_le_L'
  have hbarK : barImage L' K = Opp 2 (R891Fix α) := by
    rw [show K = Opp 2 C from rfl, k891a94reduce_barImage_opp hC_le_L', ← hfix]
  have hbarK0 : barImage L' K₀ = R891Odd (Opp 2 (R891Fix α)) := by
    rw [show K₀ = R891Odd K from rfl, k891a94reduce_barImage_r891Odd hK_le_L', hbarK]
  have hK0N : (K₀.subgroupOf K).Normal := k891a94reduce_r891Odd_normal K
  have hK0_conj : ∀ k ∈ K, K₀.map (MulAut.conj k).toMonoidHom = K₀ := fun k hk =>
    (UC6S846.mem_normalizer_iff_map_conj).mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hK0_le_K).mp hK0N hk)
  have hK_conj : ∀ k ∈ K, K.map (MulAut.conj k).toMonoidHom = K := fun k hk =>
    (UC6S846.mem_normalizer_iff_map_conj).mp (K.le_normalizer hk)
  have hmapComm : barImage L' ⁅K₀, K⁆ = barImage L' K₀ := by
    rw [barImage, k891a94reduce_commutator_subgroupOf hK0_le_L' hK_le_L',
      Subgroup.map_commutator]
    rw [show (K₀.subgroupOf L').map (QuotientGroup.mk' (CFSG.pCore 2 ↥L')) = barImage L' K₀
        from rfl,
      show (K.subgroupOf L').map (QuotientGroup.mk' (CFSG.pCore 2 ↥L')) = barImage L' K from rfl,
      hbarK0, hbarK, hcomm]
  have hcomm' : ⁅K₀, K⁆ = K₀ := by
    have hle : ⁅K₀, K⁆ ≤ K₀ := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hconj : b * a⁻¹ * b⁻¹ ∈ K₀ := by
        rw [← hK0_conj b hb]
        exact Subgroup.mem_map_of_mem _ (K₀.inv_mem ha)
      rw [commutatorElement_def]
      have heq : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [heq]
      exact K₀.mul_mem ha hconj
    refine le_antisymm hle ?_
    refine k891a94reduce_r891Odd_le_of_map hK_le_L' ?_ ?_ hmapComm
    · rw [show R891Odd K = K₀ from rfl]
      exact hle
    · intro k hk
      rw [Subgroup.map_commutator, hK0_conj k hk, hK_conj k hk]
  have hY : CFSG.pCore 2 ↥(R891Odd (Opp 2 (R891Fix α))) = ⊥ :=
    k891a94reduce_pCore_two_eq_bot_of_isPGroup_three
      (k891a94reduce_isPGroup_three_of_shape hshape)
  have hbar2 : Nonempty (Bar2 K₀ ≃* ↥(R891Odd (Opp 2 (R891Fix α)))) := by
    let π : ↥K₀ →* Bar2 L' :=
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L')).comp (Subgroup.inclusion hK0_le_L')
    have hqrange : π.range = R891Odd (Opp 2 (R891Fix α)) := by
      have h1 : π.range = barImage L' K₀ := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 x.2)
        · intro hy
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
          refine ⟨⟨z.1, Subgroup.mem_subgroupOf.1 hz⟩, ?_⟩
          simp only [π, MonoidHom.comp_apply]
          exact hzy
      rw [h1, hbarK0]
    let qc : ↥K₀ →* ↥π.range := π.codRestrict π.range (fun x => ⟨x, rfl⟩)
    let e0 : ↥π.range ≃* ↥(R891Odd (Opp 2 (R891Fix α))) := MulEquiv.subgroupCongr hqrange
    let f : ↥K₀ →* ↥(R891Odd (Opp 2 (R891Fix α))) := e0.toMonoidHom.comp qc
    have hqcsurj : Function.Surjective qc := by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 y.2
      exact ⟨x, Subtype.ext hx⟩
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := e0.surjective y
      obtain ⟨z, hz⟩ := hqcsurj x
      exact ⟨z, by change e0 (qc z) = y; rw [hz, hx]⟩
    have hfker : IsPGroup 2 f.ker := by
      have h1 : f.ker = qc.ker := by ext x; simp [f, e0, MonoidHom.mem_ker]
      rw [h1]
      change IsPGroup 2 ↥(π.codRestrict π.range (fun x => MonoidHom.mem_range.2 ⟨x, rfl⟩)).ker
      rw [MonoidHom.ker_codRestrict]
      have h2 : π.ker = (CFSG.pCore 2 ↥L').comap (Subgroup.inclusion hK0_le_L') := by
        ext x; simp [π, MonoidHom.mem_ker, Subgroup.mem_comap]
      rw [h2]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L')).comap_of_injective
        (Subgroup.inclusion hK0_le_L') (Subgroup.inclusion_injective hK0_le_L')
    exact k891a94reduce_quot_pCore_equiv f hfsurj hfker hY
  obtain ⟨e⟩ := hbar2
  refine ⟨K, K₀, hK_le_C.trans hC_le_M, hK_le_C.trans hC_le_cen, ?_, hK0_le_K, hK0N, ?_, ?_⟩
  · intro _
    rw [show K = Opp 2 C from rfl, k891a94reduce_opp_idem]
  · intro _
    rfl
  · refine Or.inr ⟨hn, hcomm', ?_, ?_⟩
    · exact hshape.imp (k891a94reduce_extra_of_mulEquiv e.symm)
        (k891a94reduce_e9_of_mulEquiv e.symm)
    · intro W hO hW h3 hall
      apply hnorm (barImage L' W)
      · rw [← hbarK0]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono L' hW)
      · rw [← hbarK0]
        exact k891a94reduce_relIndex_map_of_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L'))
          hW hK0_le_L' (fun x hx hfx => hO (k891a94reduce_mem_pCoreOf hK0_le_L' hx ((QuotientGroup.eq_one_iff x).mp hfx))) |>.trans h3
      · intro k' hk'
        rw [← hbarK] at hk'
        obtain ⟨k, hk, hkk⟩ := Subgroup.mem_map.1 hk'
        have hkG : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
        have hkL : (k : G) ∈ L' := hK_le_L' hkG
        rw [← hkk]
        have hk_eq : k = (⟨(k : G), hkL⟩ : ↥L') := Subtype.ext rfl
        rw [hk_eq, ← k891a94reduce_barImage_conj hkL (hW.trans hK0_le_L')]
        rw [hall (k : G) hkG]

theorem s891_a94_reduce
    {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D)
    (L S A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hA : R891Classes L S A) (h893 : R891Facts893 D L S A n) (hnot : A ∉ uniqueSet D.M) :
    ∃ K K₀ : Subgroup G, R891Cfg894 D A K K₀ n := by
  classical
  obtain ⟨p, hp_sig⟩ := hSg.nonempty
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hset.mem
  have hsp : IsStronglyPEmbedded p D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp_sig
  have hp_prime : p.Prime := (D.sig_prime p hp_sig).1
  have hp_ne2 : p ≠ 2 := (D.sig_prime p hp_sig).2
  have hp_ge5 : 5 ≤ p := by
    by_contra h
    have : p = 3 := by interval_cases p <;> tauto
    subst this
    exact hset.notStrong hsp
  have hA_le_M : A ≤ D.M := hA.aLe.trans hset.mem.1.le
  obtain ⟨g, hAg, hMg_ne⟩ := k891a94reduce_find_g hA_le_M hnot
  let L' : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  let C : Subgroup G := L' ⊓ centralizer (A : Set G)
  have hC_le_L' : C ≤ L' := inf_le_left
  have hC_le_cen : C ≤ centralizer (A : Set G) := inf_le_right
  have hC_le_M : C ≤ D.M :=
    hC_le_cen.trans ((Subgroup.centralizer_le_normalizer (A : Set G)).trans h893.normA.1)
  have hL'_le_Mg : L' ≤ D.M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hset.mem.1.le
  have hd4' : Is3D4 (Bar2 L') n := k891a94reduce_is3D4_bar2_map hset.d4
  have hnotp_C : ¬ p ∣ Nat.card (↥C) := by
    have hle : C ≤ D.M.map (MulAut.conj g).toMonoidHom ⊓ centralizer (A : Set G) := by
      refine le_inf ?_ inf_le_right
      exact inf_le_left.trans hL'_le_Mg
    exact fun hd =>
      k891a94reduce_not_dvd_C hsp h893.normA.1 hMg_ne (hd.trans (Subgroup.card_dvd_of_le hle))
  have hA_normalizes : A ≤ normalizer (L' : Set G) :=
    hAg.trans (k891a94reduce_map_normal hbasic.normal)
  obtain ⟨a, ha_mem, ha_order⟩ := k891a94reduce_exists_order_three hA.aOrder
  have hp_dvd_bar2 : p ∣ Nat.card (Bar2 L') :=
    k891a94reduce_dvd_bar2 hp_prime hp_ne2 (h893.rank p hp_sig).1
  obtain ⟨α, hα_order, hα_fix, hα_notp⟩ :=
    k891a94reduce_alpha_exists ha_mem ha_order hA.aOrder hA_normalizes hnotp_C hp_dvd_bar2
  have hc1 : ((2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) := (h893.normZ.1 p hp_sig).1
  have hc2 : ¬ ((2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p]) := (h893.normZ.1 p hp_sig).2
  have hAut_res := r891AutCore_holds (Bar2 L') n hd4' p hp_prime hp_ge5 hc1 hc2 α hα_order hα_notp
  by_cases hn : n = 1
  · subst hn
    obtain ⟨hcomm, hshape, hnorm⟩ := hAut_res.2 rfl
    exact k891a94reduce_cfg_none rfl hC_le_M hC_le_cen hC_le_L' hα_fix hcomm hshape hnorm
  · have hn2 : 2 ≤ n := by
      have h1 : 1 ≤ n := (hset.d4.admissible).2.1
      omega
    obtain ⟨hperf, hshape⟩ := hAut_res.1 hn2
    exact k891a94reduce_cfg_nge2 hn2 hC_le_M hC_le_cen hC_le_L' hα_fix hperf hshape

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
