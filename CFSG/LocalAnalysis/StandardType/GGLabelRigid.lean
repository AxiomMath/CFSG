module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.Adapters.LieModelSmallOrders
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.Milestones.CL_LIT_SQTK_simple_list
import CFSG.Quasithin.Background.A1cA133Three
import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.EmptyFaithful.S146zYFacts
import CFSG.Quasithin.EmptyFaithful.S146zYRes
import CFSG.Quasithin.H13.NQCoreP134Main
import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.GLTheoremA (IsClsLab IsExcLab IsChar3Lab partition_lab cls_det
  markChar_two_of_cls markChar_two_of_exc lieModel_of_mark_two evenLieOrder_of_excLab
  excOK_of_excLab excOrd_inj)
open CFSG.LocalAnalysis.GLTheoremA.MI (derived_labelUniq)

private theorem labelRigid_centerQuot_nonabelian {H : Type*} [Group H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) : ∃ a b : H ⧸ Subgroup.center H, a * b ≠ b * a :=
  nonabelian_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple_nonabelian hna)).trans
      QuotientGroup.quotientBot).symm hna

private theorem labelRigid_sz_nonabelian {a : ℕ} (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenSzGroup a K), x * y ≠ y * x := by
  have hsimple := CFSG.LieType.Ree.suzuki_simple (a := a) (K := K) ha hK
  have hperfect := CFSG.LieType.Ree.suzuki_perfect (a := a) (K := K) ha hK
  have hna : ∃ g h : suzukiGroup a K, g * h ≠ h * g := by
    by_contra h
    push Not at h
    haveI : Nontrivial (suzukiGroup a K) := hsimple.2.1
    haveI : Group.IsPerfect (suzukiGroup a K) := hperfect.2
    haveI : IsMulCommutative (suzukiGroup a K) := ⟨Std.Commutative.mk h⟩
    exact not_subsingleton (suzukiGroup a K) Group.IsPerfect.subsingleton_of_isMulCommutative
  haveI : IsSimpleGroup (suzukiGroup a K) := hsimple.2.2
  have hq : ∃ x y : LargeEvenCenterQuot (suzukiGroup a K), x * y ≠ y * x :=
    labelRigid_centerQuot_nonabelian hna
  obtain ⟨e⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  exact nonabelian_of_mulEquiv e.symm hq

private theorem labelRigid_g2der_nonabelian
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x := by
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv K .G2
  have hna : ∃ a b : DerivedCentralQuotient (adjointGroup .G2 K), a * b ≠ b * a := by
    have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK
    have hC : StatedClassicalModel ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ .PSU 3 3 1 := by
      rcases hL with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact h
      · simp [chevalleyExceptionalTags] at ht
      · simp [reeTitsTags] at ht
      · cases ht
    have hsimple : IsSimpleGroup ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC).2
    have hcard : Nat.card ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ = 6048 :=
      CFSG.Blueprint.LieModel.card_psu_three_three hL
    have hneq : ∃ a b : ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆, a * b ≠ b * a := by
      by_contra hnab
      have hcomm : ∀ a b : ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆, a * b = b * a := by
        intro a b
        by_contra h
        exact hnab ⟨a, b, h⟩
      haveI : IsMulCommutative ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
        IsMulCommutative.of_comm hcomm
      have hp : (Nat.card ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆).Prime :=
        Group.is_simple_iff_prime_card.mp hsimple
      rw [hcard] at hp
      norm_num at hp
    exact labelRigid_centerQuot_nonabelian hneq
  exact nonabelian_of_mulEquiv e₁.symm hna

private theorem labelRigid_rawDatum_imp
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → MarkedModel lab R →
      Q' R I F)
    (h : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg]
    at hn hl h hQQ' ⊢
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  case B =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case G2 =>
    obtain ⟨-, hn2⟩ := hl
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, by
      have := four_le_two_pow hn2; omega⟩, untwistedChevalleyModel_largeEven .G2 hK⟩)
  case F4 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  case E6 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)
  case E7 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E7 hK⟩)
  case E8 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E8 hK⟩)
  case twE6 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .E6 hK⟩)
  case triD4 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeSuzuki_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    have hSz := suzukiModel_largeEvenSz (a := (n - 1) / 2) (by omega) K hK
      (labelRigid_sz_nonabelian (a := (n - 1) / 2) (by omega) K hK)
    rwa [← hn'] at hSz
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  case B2der =>
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inl ⟨by decide, statedClassicalModel_b2der hK⟩
  case G2der =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact lieModel_g2der K hK (labelRigid_g2der_nonabelian K hK)
  case twF4der =>
    obtain ⟨-, rfl⟩ := hl
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      0, rfl, reeTitsRelationModel_largeEven 0 hK⟩))

private theorem labelRigid_markedModel_of_hasLabel
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {R : Type} [Group R] (h : GGHasLabel lab R) :
    MarkedModel lab R := by
  obtain ⟨R', _, I, F, hm⟩ := largeEvenRawDatum_exists
    (labelRigid_rawDatum_imp hlab (Q' := fun _ _ _ _ => MarkedModel lab R)
      (fun R' _ I F hq hm => hq.elim fun e => hm.of_mulEquiv e.symm) h)
  exact hm

private theorem labelRigid_b2der_eq {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hb : lab.tag = .B2der) : lab = ⟨.B2der, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hb
  subst hb
  simp only [LargeEvenInLambda2] at hl
  obtain ⟨-, hr, hn⟩ := hl
  subst hr hn
  rfl

private theorem labelRigid_g2der_eq {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hg : lab.tag = .G2der) : lab = ⟨.G2der, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hg
  subst hg
  simp only [LargeEvenInLambda2] at hl
  obtain ⟨-, hr, hn⟩ := hl
  subst hr hn
  rfl

section Cert


private theorem labelRigid_cls_exc {X : Type} [Group X] {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hc : IsClsLab lab) (hE : IsExcLab lab')
    (hM : MarkedModel lab X) (hM' : MarkedModel lab' X) : False := by
  have hM'' := lieModel_of_mark_two hM' (markChar_two_of_exc hE)
  obtain ⟨hs, -, -⟩ := cls_det hl hc hM hM''
  obtain ⟨t₁, r₁, n₁⟩ := lab
  obtain ⟨t₂, r₂, n₂⟩ := lab'
  unfold IsClsLab at hc
  unfold IsExcLab at hE
  dsimp only at hc hE hs
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (first
      | (simp [CFSG.StandardType.markTag] at hs; done)
      | (by_cases h2 : r₁ = 2 <;> by_cases h3 : r₁ = 3 <;>
          simp [CFSG.StandardType.markTag, h2, h3] at hs <;> done))

private theorem labelRigid_exc_exc {X : Type} [Group X] {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hl' : LargeEvenInLambda2 lab') (hE : IsExcLab lab)
    (hE' : IsExcLab lab') (hM : MarkedModel lab X) (hM' : MarkedModel lab' X) : lab = lab' := by
  have hc₁ : CFSG.StandardType.markChar lab = 2 := markChar_two_of_exc hE
  have hc₂ : CFSG.StandardType.markChar lab' = 2 := markChar_two_of_exc hE'
  unfold CFSG.StandardType.MarkedModel at hM hM'
  rw [hc₁] at hM
  rw [hc₂] at hM'
  have e₁ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM
  have e₂ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM'
  rw [evenLieOrder_of_excLab hl hE] at e₁
  rw [evenLieOrder_of_excLab hl' hE'] at e₂
  obtain ⟨ht, hn⟩ := excOrd_inj (excOK_of_excLab hl hE) (excOK_of_excLab hl' hE') (e₁.symm.trans e₂)
  obtain ⟨t₁, r₁, n₁⟩ := lab
  obtain ⟨t₂, r₂, n₂⟩ := lab'
  have hr₁ : r₁ = 0 := by
    unfold IsExcLab at hE
    dsimp only at hE hl
    simp only [LargeEvenInLambda2] at hl
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hr₂ : r₂ = 0 := by
    unfold IsExcLab at hE'
    dsimp only at hE' hl'
    simp only [LargeEvenInLambda2] at hl'
    rcases hE' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  dsimp only at ht hn
  subst ht hn hr₁ hr₂
  rfl

private theorem labelRigid_iso_of_params {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hl' : LargeEvenInLambda2 lab') (hc : IsClsLab lab)
    (hc' : IsClsLab lab') (hs : markTag lab = markTag lab') (hr : markRank lab = markRank lab')
    (hd : markDeg lab = markDeg lab') : GGLabelIso lab lab' := by
  obtain ⟨t₁, r₁, n₁⟩ := lab
  obtain ⟨t₂, r₂, n₂⟩ := lab'
  unfold IsClsLab at hc hc'
  dsimp only at hl hl' hc hc' hs hr hd ⊢
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [markTag, markRank, markDeg, LargeEvenInLambda2, GGLabelIso,
      LargeEvenLabel.mk.injEq] at hs hr hd hl hl' ⊢ <;>
    (try split_ifs at hs hr hd ⊢) <;> simp_all <;> omega

private theorem labelRigid_iso_of_cls {X : Type} [Group X] {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hl' : LargeEvenInLambda2 lab') (hc : IsClsLab lab)
    (hc' : IsClsLab lab') (hM : MarkedModel lab X) (hM' : MarkedModel lab' X) :
    GGLabelIso lab lab' := by
  obtain ⟨hs, hr, hd⟩ := cls_det hl hc hM (lieModel_of_mark_two hM' (markChar_two_of_cls hc'))
  exact labelRigid_iso_of_params hl hl' hc hc' hs.symm hr.symm hd.symm

private theorem labelRigid_char3 {X : Type} [Group X] {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hl' : LargeEvenInLambda2 lab') (hk : IsChar3Lab lab)
    (hM : MarkedModel lab X) (hM' : MarkedModel lab' X) : lab = lab' := by
  unfold IsChar3Lab at hk
  rcases hk with hb | hg
  · by_cases hb' : lab'.tag = .B2der
    · rw [labelRigid_b2der_eq hl hb, labelRigid_b2der_eq hl' hb']
    · exact absurd (ggMarkedModel_card_b2der hb hM)
        (ggMarkedModel_card_ne_three_sixty hb' hM')
  · by_cases hg' : lab'.tag = .G2der
    · rw [labelRigid_g2der_eq hl hg, labelRigid_g2der_eq hl' hg']
    · have hd : CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab := Or.inl hg
      have hne : lab.tag ≠ lab'.tag := by
        rw [hg]
        exact fun h => hg' h.symm
      exact ((derived_labelUniq hd hne hM hM').false (MulEquiv.refl X)).elim

private theorem labelRigid_iso_of_markedModel {X : Type} [Group X] {lab lab' : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hl' : LargeEvenInLambda2 lab') (hM : MarkedModel lab X)
    (hM' : MarkedModel lab' X) : GGLabelIso lab lab' := by
  rcases partition_lab lab with c | e | k <;> rcases partition_lab lab' with c' | e' | k'
  · exact labelRigid_iso_of_cls hl hl' c c' hM hM'
  · exact (labelRigid_cls_exc hl c e' hM hM').elim
  · exact Or.inl (labelRigid_char3 hl' hl k' hM' hM).symm
  · exact (labelRigid_cls_exc hl' c' e hM' hM).elim
  · exact Or.inl (labelRigid_exc_exc hl hl' e e' hM hM')
  · exact Or.inl (labelRigid_char3 hl' hl k' hM' hM).symm
  · exact Or.inl (labelRigid_char3 hl hl' k hM hM')
  · exact Or.inl (labelRigid_char3 hl hl' k hM hM')
  · exact Or.inl (labelRigid_char3 hl hl' k hM hM')

end Cert

theorem ggLabelRigidInput_holds :
    GGLabelRigidInput := by
  intro lab lab' R _ hl hl' h h'
  exact labelRigid_iso_of_markedModel hl hl' (labelRigid_markedModel_of_hasLabel hl h)
    (labelRigid_markedModel_of_hasLabel hl' h')

end CFSG.StandardType

end
