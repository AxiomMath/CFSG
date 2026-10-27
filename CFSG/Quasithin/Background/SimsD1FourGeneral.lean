module

public import CFSG.Quasithin.Background.SimsD1FourBlocksGen
public import CFSG.LocalAnalysis.AGLEmbedding.LocalCGTBridge
import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof
import CFSG.Quasithin.Vol2.Ch3Sec1D12
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.SimsD1Four
public import CFSG.Quasithin.Background.SimsD1FourBlocks

public section

namespace CFSG.Quasithin.SimsD1.FourGeneral

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem isKGroup_of_isSolvable (X : Type) [Group X] [Group.IsSolvable X] :
    CFSG.Open.IsKGroup X := by
  intro K L _ _ _ hnab
  obtain ⟨a, b, hab⟩ := hnab
  exact (hab ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance a b)).elim

section Finite

variable {G : Type} [Group G] [Finite G] {G₂ T M₂ R : Subgroup G}

theorem isAltType_three_of_inClassXBlock {L : Subgroup G}
    (hL : CFSG.AGLEmbedding.InClassXBlock L) (hsolv : Group.IsSolvable ↥L) : IsAltType L 3 := by
  have hcard := C1Pack.natCard_pCore_quotient_eq_three_of_isShort2 hL.1 hsolv
  rcases hL.2 with ⟨n, hn, F, hFf, hFfin, hcardF, α, hα, hker, -⟩ | ⟨n, hn, halt⟩
  · exfalso
    let _ := hFf
    let _ := hFfin
    have hchar : (2 : F) = 0 := by
      have h2 : ringChar F = 2 := by
        refine FiniteField.even_card_iff_char_two.mpr ?_
        rw [hcardF]
        exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      have : CharP F 2 := ringChar.eq_iff.mp h2
      simpa using CharP.cast_eq_zero F 2
    let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hg1 : g ≠ 1 := by
      intro h
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
        (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [g] at this
    have hgg : g * g = 1 := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two]
      rw [one_add_one_eq_two]
      exact hchar
    exact C1Pack.false_of_surjective_of_involution α hα hker hcard hg1 hgg
  · by_cases hn1 : n = 1
    · subst hn1
      exact halt
    · exfalso
      have hm4 : 4 ≤ 2 * n + 1 := by omega
      obtain ⟨α, hα, hker, -⟩ := halt
      have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin (2 * n + 1)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      have : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have h1 : Nat.card (alternatingGroup (Fin (2 * n + 1))) = 3 := by
        rw [← Nat.card_congr e.toEquiv]
        exact hcard
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at h1
      have h2 : Nat.factorial 4 ≤ Nat.factorial (2 * n + 1) := Nat.factorial_le hm4
      have h3 : Nat.factorial 4 = 24 := by decide
      omega

theorem prodA3Blocks_of_factorization (hF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hmp : MinParabolic G₂ T M₂) (hRT : R ≤ T) (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hsyl : IsSylowTwoOf R (twoResidual G₂ ⊔ R))
    (hno : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      ¬ G₂ ≤ Subgroup.normalizer (C : Set G))
    (hsolv : Group.IsSolvable ↥G₂) (hchar : CharTwo G₂) :
    ∃ S : Finset (Subgroup G), (∀ L ∈ S, IsBlock2 G₂ L ∧ IsAltType L 3) ∧
      twoResidual G₂ = ⨆ L ∈ S, L := by
  have hXG₂ : twoResidual G₂ ⊔ R ≤ G₂ := sup_le (twoResidual_le G₂) (hRT.trans hmp.isSylow.1)
  have hXnor : ((twoResidual G₂ ⊔ R).subgroupOf G₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXG₂).mpr
      (FourBlocks.le_normalizer_twoResidual_sup hmp.isSylow hTR)
  have hXsolv : Group.IsSolvable ↥(twoResidual G₂ ⊔ R) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXG₂)
  have hXchar : CharTwo (twoResidual G₂ ⊔ R) := hchar.of_normal hXG₂ hXnor
  have hPM : ¬ twoResidual G₂ ≤ M₂ := fun h => lt_irrefl _ (lt_of_le_of_lt
    ((sup_twoResidual_eq hmp.isSylow).ge.trans (sup_le hmp.le h)) hmp.maximal.1)
  have hXM : ¬ twoResidual G₂ ⊔ R ≤ M₂ ⊓ (twoResidual G₂ ⊔ R) := fun h =>
    hPM (le_sup_left.trans (h.trans inf_le_left))
  have hX0 : twoResidual G₂ ⊔ R ≠ ⊥ := fun h => hXM (h ▸ bot_le)
  have hR1 : R ≠ ⊥ := CFSG.AGLEmbedding.LocalCGT.ne_bot_of_isSylowTwoOf hXchar hsyl hX0
  have hcgs : cgsIn (twoResidual G₂ ⊔ R) R ≤ M₂ ⊓ (twoResidual G₂ ⊔ R) :=
    FourBlocks.cgsIn_le_inf hmp hXG₂ hTR hno
  haveI := hXsolv
  obtain ⟨Y, ⟨hYX, hYs, hYx⟩, hYM⟩ := hF.relative
    (CFSG.AGLEmbedding.LocalCGT.kProper_of_isKGroup (isKGroup_of_isSolvable _))
    (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hXchar)
    (CFSG.AGLEmbedding.LocalCGT.isSylowOf_of_isSylowTwoOf hsyl)
    ((CFSG.AGLEmbedding.LocalCGT.centralizer_inf_le_cgsIn hsyl.2.1 hR1).trans hcgs)
    (fun B hB hBS hBc =>
      (CFSG.AGLEmbedding.LocalCGT.normalizer_inf_le_cgsIn B hB hBS hBc).trans hcgs)
    hXM
  have hYb := CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hYx
  have hi : ¬ Y ≤ M₂ := fun h => hYM (le_inf h hYX)
  have hA3 : IsAltType Y 3 := isAltType_three_of_inClassXBlock hYb
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYX))
  have hbG : IsBlock2 G₂ Y := ⟨hYb.1, hYX.trans hXG₂,
    (isSubnormal_iff_subgroupOf (hYX.trans hXG₂)).mp
      (A4.subnormal_trans (IsBlock2.isSubnormal ⟨hYb.1, hYX, hYs⟩)
        (A4.subnormal_of_normal hXG₂ hXnor))⟩
  have hfin : {L : Subgroup G | IsBlock2 G₂ L ∧ IsAltType L 3}.Finite := Set.toFinite _
  refine ⟨hfin.toFinset, fun L hL => hfin.mem_toFinset.mp hL, le_antisymm ?_ ?_⟩
  ·
    have hYG : ⨆ L ∈ hfin.toFinset, L ≤ G₂ :=
      iSup₂_le fun L hL => (hfin.mem_toFinset.mp hL).1.2.1
    have hLY : Y ≤ ⨆ L ∈ hfin.toFinset, L :=
      le_iSup₂ (f := fun L (_ : L ∈ hfin.toFinset) => L) Y (hfin.mem_toFinset.mpr ⟨hbG, hA3⟩)
    exact (hmp.le_kerIn_or_twoResidual_le hYG
      (FourBlocks.le_normalizer_iSup_a3Blocks hfin)).resolve_left
      fun hle => hi (hLY.trans (hle.trans kerIn_le))
  ·
    exact iSup₂_le fun L hL => FourBlocks.le_twoResidual_of_isShort2
      (hfin.mem_toFinset.mp hL).1.1 (hfin.mem_toFinset.mp hL).1.2.1

end Finite

open CFSG.Quasithin.SimsD1.Transport

variable {G : Type} [Group G] {G₁ G₂ T V M₂ : Subgroup G}

theorem prodA3Blocks_general_of_factorization
    (hF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization) [Finite G₁] [Finite G₂]
    (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) (hsolv : Group.IsSolvable ↥G₂)
    (hchar : CharTwo G₂) :
    ∃ S : Finset (Subgroup G), (∀ L ∈ S, IsBlock2 G₂ L ∧ IsAltType L 3) ∧
      twoResidual G₂ = ⨆ L ∈ S, L := by
  obtain ⟨F, _, _, ⟨e⟩⟩ := exists_emb (T := T) h.sylow₁.1 h.sylow₂.1
  have h' := d11Hyp_img e h
  have hV₁ : V ≤ G₁ := h.reduced.1
  have hVT : V ≤ T := h.V_le_T
  have hV₂ : V ≤ G₂ := hVT.trans e.le₂
  have hU₂ : conjClosure V G₂ ≤ G₂ := conjClosure_le_of_le hV₂ le_rfl
  have hVeq : img e.ι₁ V = img e.ι₂ V := e.img_eq hVT
  have hRF₂ : pCoreOf 2 (img e.ι₂ G₂) = img e.ι₂ (pCoreOf 2 G₂) :=
    (img_pCoreOf e.inj₂ 2 le_rfl).symm
  have hU : conjClosure (img e.ι₁ V) (img e.ι₂ G₂) = img e.ι₂ (conjClosure V G₂) := by
    rw [hVeq, img_conjClosure hV₂ le_rfl]
  have hVR₂' : img e.ι₁ V ≤ pCoreOf 2 (img e.ι₂ G₂) := by
    rw [hVeq, hRF₂]
    exact img_mono hVR₂
  have hchief' : IsChiefSeriesFrom (img e.ι₂ G₂) (conjClosure (img e.ι₁ V) (img e.ι₂ G₂))
      (conjClosure (img e.ι₁ V) (img e.ι₂ G₂)) 1 := by
    rw [hU]
    exact (isChiefSeriesFrom_img_iff e.inj₂ le_rfl hU₂ hU₂ 1).2 hchief
  have hdual' : ¬ IsDualFFInt (img e.ι₁ G₁) (img e.ι₁ V) h'.reduced.2.2.1 := fun hd =>
    hdual ((isDualFFInt_img_iff e.inj₁ le_rfl hV₁ h.reduced.2.2.1 h'.reduced.2.2.1).1 hd)
  have hsolv' : Group.IsSolvable ↥(img e.ι₂ G₂) := (isSolvable_img_iff e.inj₂ le_rfl).2 hsolv
  have hchar' : CharTwo (img e.ι₂ G₂) := (charTwo_img_iff e.inj₂ le_rfl).2 hchar
  have hmp := Four.minParabolic h' hVR₂' hchief' hdual'
  have hRT' : pCoreOf 2 (img e.ι₁ G₁) ≤ img e.ι₁ T := h'.pCoreOf_le_T
  have hTR' : img e.ι₁ T ≤ Subgroup.normalizer ((pCoreOf 2 (img e.ι₁ G₁) : Subgroup F) : Set F) :=
    h'.sylow₁.1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hsyl' : IsSylowTwoOf (pCoreOf 2 (img e.ι₁ G₁))
      (twoResidual (img e.ι₂ G₂) ⊔ pCoreOf 2 (img e.ι₁ G₁)) := by
    rw [F6.twoResidual_eq_oTwoUpper]
    exact EmptyFaithfulMultiple.inputD14Solvable_holds F _ _ _ _ _ h' hVR₂' hchief' hdual'
      hsolv' hchar'
  have hno' : ∀ C : Subgroup F, C ≤ pCoreOf 2 (img e.ι₁ G₁) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (img e.ι₁ G₁))).Characteristic →
      ¬ img e.ι₂ G₂ ≤ Subgroup.normalizer (C : Set F) := by
    intro C hCR hC0 hCchar hn
    have hR1 : img e.ι₁ G₁ ≤ Subgroup.normalizer (C : Set F) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
        (normalizer_le_normalizer_of_characteristic_subgroupOf hCR hCchar)
    have hCG : C ≤ img e.ι₁ G₁ ⊔ img e.ι₂ G₂ :=
      (hCR.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).trans le_sup_left
    exact hC0 (h'.no_normal C hCR
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCG).2 (sup_le hR1 hn)))
  have hFin := prodA3Blocks_of_factorization hF hmp hRT' hTR' hsyl' hno' hsolv' hchar'
  rw [← img_twoResidual e.inj₂ le_rfl] at hFin
  exact (FourBlocksGen.prodA3_img_iff e.inj₂ le_rfl (twoResidual_le G₂)).1 hFin

end CFSG.Quasithin.SimsD1.FourGeneral
