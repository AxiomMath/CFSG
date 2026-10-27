module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRowR3Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6BigLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourLabelsAd
public import CFSG.LieType.Seitz.Defs
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.StandardType.SCFourCover CFSG.StandardType.NoOffTwE6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private def ggTwE6BigT_SettingAd {R : Type} [Group R] (I : Set (MulAut R))
    (A : Subgroup (MulAut R)) (a₀ : MulAut R) (J₁ : Subgroup R) : Prop :=
  IsElemAbelian 3 A ∧ (∀ a ∈ A, a ∈ I) ∧ 3 ^ 5 ≤ Nat.card A ∧ a₀ ∈ A ∧ a₀ ≠ 1 ∧
    IsComponentOf J₁ (ggFix a₀)

private theorem ggTwE6BigT_setting_descend {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hL : commutator L' = ⊤)
    {I : Set (MulAut R)} {A : Subgroup (MulAut L')} {a₀ : MulAut L'} {J₁ : Subgroup L'}
    (h : GGTwE6BigSetting I ψ A a₀ J₁) {φ₀ : MulAut R} (hφ₀ : ∀ l, φ₀ (ψ l) = ψ (a₀ l)) :
    ggTwE6BigT_SettingAd I (TypeA.inducedSub ψ A) φ₀ (J₁.map ψ) := by
  obtain ⟨hE, hI, hcard, ha₀, hne, hcomp⟩ := h
  have hJ := commutator_eq_self_of_isComponentOf hcomp
  refine ⟨TypeA.isElemAbelian_inducedSub hψ hE, inducedSub_subset hψ hI, ?_,
    TypeA.mem_inducedSub.2 ⟨a₀, ha₀, hφ₀⟩, fun h1 => hne ((induced_eq_one_iff hψ hker hL hφ₀).1 h1),
    (isComponentOf_map_iff hψ hker hφ₀ hJ).1 hcomp⟩
  · rw [TypeA.card_inducedSub hψ hker hL fun a ha => (hI a ha).imp fun _ hφ => hφ.2]
    exact hcard

private theorem ggTwE6BigT_congr_symm_apply_symm {C R : Type*} [Group C] [Group R]
    (ε : C ≃* R) (b : MulAut R) (m : R) :
    (MulAut.congr ε).symm b (ε.symm m) = ε.symm (b m) := by
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

private theorem ggTwE6BigT_map_ggFix_symm {C R : Type*} [Group C] [Group R] (ε : C ≃* R)
    (b : MulAut R) :
    (ggFix b).map ε.symm.toMonoidHom = ggFix ((MulAut.congr ε).symm b) := by
  ext c
  obtain ⟨m, rfl⟩ := ε.symm.surjective c
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply, mem_ggFix, mem_ggFix,
    ggTwE6BigT_congr_symm_apply_symm, ε.symm.injective.eq_iff]

private theorem ggTwE6BigT_ggFix_eq_fixedPoints {C : Type*} [Group C] (a : MulAut C) :
    ggFix a = CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers a) := by
  ext c
  rw [mem_ggFix, CFSG.LieType.Seitz.mem_fixedPoints]
  refine ⟨fun hc φ hφ => ?_, fun hc => hc a (Subgroup.mem_zpowers a)⟩
  have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut C) c :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hc)
  exact MulAction.mem_stabilizer_iff.1 (hle hφ)

private theorem ggTwE6BigT_twConj_mem_range
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (w : RecipeExcLang.twInndiagGroup K σ) :
    RecipeExcLang.twConj K σ w ∈ (twistedE6InndiagConj K σ).range :=
  ⟨⟨w.1, twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, MulEquiv.ext fun _ => Subtype.ext rfl⟩

private theorem ggTwE6BigT_e6AdToral_baseChange
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = 4)
    (hinj : Function.Injective (twistedE6InndiagConj K σ))
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : 3 ^ 5 ≤ Nat.card E)
    (hErange : E ≤ (twistedE6InndiagConj K σ).range) :
    E6AdToral (((E.comap (twistedE6InndiagConj K σ)).map
      (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)))) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hnot3 : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  set X := ((E.comap (twistedE6InndiagConj K σ)).map
      (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))) with hX
  have hEL : CFSG.Open.IsElemAbelian 3 X := isElemAbelian_baseChange_comap hinj hE
  have hXcard : 3 ^ 5 ≤ Nat.card X := by
    have hXcardeq : Nat.card X = Nat.card E := by
      have h1 : Nat.card X = Nat.card ((E.comap (twistedE6InndiagConj K σ)).map
          (twistedE6InndiagGL K σ).subtype) :=
        Subgroup.card_map_of_injective (baseChangeGL_injective _)
      have h2 : Nat.card ((E.comap (twistedE6InndiagConj K σ)).map
          (twistedE6InndiagGL K σ).subtype) = Nat.card (E.comap (twistedE6InndiagConj K σ)) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      have h3 : (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = E :=
        Subgroup.map_comap_eq_self hErange
      have h4 : Nat.card (E.comap (twistedE6InndiagConj K σ)) = Nat.card E := by
        rw [← Subgroup.card_map_of_injective hinj, h3]
      rw [h1, h2, h4]
    rw [hXcardeq]
    exact hcard
  obtain ⟨g, hg, hgtor⟩ := ExcFramesHalf.bigElemAbelianToralBar_E6_three (K := K) hnot3 X
    (baseChange_comap_le_adjointGroup E)
    (fun x hx y hy => congrArg Subtype.val (hEL.1.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)) hEL.2 hXcard
  exact ⟨g⁻¹, inv_mem hg, fun x hx => by simpa only [inv_inv] using hgtor x hx⟩

private def ggTwE6BigT_LabelsAd :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ 2) →
    ∀ (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K 1),
    (∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K 1 ↔ x ∈ (RecipeExcLang.twConj K σ).range) →
    IsSimpleGroup (TwE6Delta.RecipeR K 1) → Finite (TwE6Delta.RecipeR K 1) →
    ∀ (A : Subgroup (MulAut (TwE6Delta.RecipeR K 1))) (a₀ : MulAut (TwE6Delta.RecipeR K 1))
      (J₁ : Subgroup (TwE6Delta.RecipeR K 1)),
      ggTwE6BigT_SettingAd (TwE6Delta.RecipeI K 1) A a₀ J₁ →
      LargeEvenMarking ↥J₁ fun lab' _ _ _ _ _ => GGTwE6BigLabel lab'

private theorem ggTwE6BigT_labelsKnown_of_ad
    (h : ggTwE6BigT_LabelsAd) : GGTwE6BigLabelsKnown := by
  intro lab hlab ht h1
  refine TwE6Delta.labelAll ht fun K _ _ hK => ?_
  rw [h1] at hK ⊢
  intro hs _ L' _ _ ψ hψ hker hL A a₀ J₁ hset
  have hset' := hset
  obtain ⟨hE, hI, hcard, ha₀, hne, hcomp⟩ := hset'
  obtain ⟨φ₀, -, hφ₀⟩ := hI a₀ ha₀
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 1) :=
    (iterateFrobenius K 2 1).injective
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K 2 1)
      ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => by
        have h2 := iterateFrobenius_def 2 1 c
        rw [pow_one] at h2
        exact h2⟩
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv (n := 1) (hn := le_rfl) (K := K) hK σ hσ
  exact (largeEvenMarking_map_iff hker (commutator_eq_self_of_isComponentOf hcomp) _).2
    (h K hK4 σ hσ ε hε hs (Finite.of_surjective ψ hψ) (TypeA.inducedSub ψ A) φ₀ (J₁.map ψ)
      (ggTwE6BigT_setting_descend hψ hker hL hset hφ₀))

private theorem ggTwE6BigT_labelsAd_of_line
    (hline : GGTwE6BigLineLabels) : ggTwE6BigT_LabelsAd := by
  intro K _ _ hK4 σ hσ ε hε _ _ A a₀ J₁ hset
  obtain ⟨hA, hAI, hcard, ha₀, ha₁, hcomp⟩ := hset
  have hK : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK4]; norm_num
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ 2 hσ hK (by norm_num)
  have hEI : A.map (MulAut.congr ε).symm.toMonoidHom ≤ (twistedE6InndiagConj K σ).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨w, hw⟩ := (hε ((MulAut.congr ε).symm a)).1 (by
      rw [MulEquiv.apply_symm_apply]
      exact hAI a ha)
    rw [MulEquiv.coe_toMonoidHom, ← hw]
    exact ggTwE6BigT_twConj_mem_range σ w
  obtain ⟨h, hh⟩ := hEI ⟨a₀, ha₀, rfl⟩
  replace hh : twistedE6InndiagConj K σ h = (MulAut.congr ε).symm a₀ := hh
  have hh1 : h ≠ 1 := by
    rintro rfl
    apply ha₁
    apply (MulAut.congr ε).symm.injective
    rw [← hh, map_one, map_one]
  have hh3 : h ^ 3 = 1 := hinj (by rw [map_pow, hh, ← map_pow, hA.2 a₀ ha₀, map_one, map_one])
  have hJ : CFSG.Open.IsComponentOf (J₁.map ε.symm.toMonoidHom)
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) := by
    rw [hh, ← ggTwE6BigT_ggFix_eq_fixedPoints, ← ggTwE6BigT_map_ggFix_symm]
    exact isComponentOf_iff_open.1 (isComponentOf_map_mulEquiv ε.symm hcomp)
  have hfE : twistedE6InndiagConj K σ h ∈ A.map (MulAut.congr ε).symm.toMonoidHom := by
    rw [hh]
    exact ⟨a₀, ha₀, rfl⟩
  have hEab : CFSG.Open.IsElemAbelian 3 (A.map (MulAut.congr ε).symm.toMonoidHom) :=
    TableB.isElemAbelian_map hA (MulAut.congr ε).symm.toMonoidHom
  have hEcard : 3 ^ 4 ≤ Nat.card (A.map (MulAut.congr ε).symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr ε).symm.injective]
    exact le_trans (by norm_num : 3 ^ 4 ≤ 3 ^ 5) hcard
  have hEcard5 : 3 ^ 5 ≤ Nat.card (A.map (MulAut.congr ε).symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr ε).symm.injective]
    exact hcard
  refine largeEvenMarking_of_mulEquiv
    (J₁.equivMapOfInjective ε.symm.toMonoidHom ε.symm.injective) ?_
  exact hline K σ hK4 hσ h hh1 hh3 _ hEab hEcard hfE hEI
    (ggTwE6BigT_e6AdToral_baseChange σ hK4 hinj hEab hEcard5 hEI) _ hJ

theorem ggTwE6BigLabelsKnown_of_line
    (hline : GGTwE6BigLineLabels) : GGTwE6BigLabelsKnown :=
  ggTwE6BigT_labelsKnown_of_ad (ggTwE6BigT_labelsAd_of_line hline)

end CFSG.StandardType

end