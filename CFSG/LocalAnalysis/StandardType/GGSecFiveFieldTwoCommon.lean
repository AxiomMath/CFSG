module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixAD
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLinear
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac
import all CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynOrders
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac
import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Config

variable {G : Type} [Group G] [Finite G]

theorem GGConfig.isComponentOf_ggG0_inf {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) :
    IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
  CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hC.1.2.2.2.2.2.2.1.2.2.2.1
    (le_inf (le_ggG0_left p B x L D J) hC.1.2.2.2.2.2.2.1.2.2.2.1.1) inf_le_right

theorem mem_normalizer_of_ggPsiInnerDiag {U : Type*} [Group U] {Δ : UniversalRootDatum U}
    {ψ : U →* G} (hgen : ⨆ γ ∈ Δ.roots, Δ.rootGroup γ = ⊤) {c : G}
    (hc : GGPsiInnerDiag Δ ψ c) : c ∈ Subgroup.normalizer (ψ.range : Set G) := by
  obtain ⟨g, hg, hroot⟩ := hc
  set d : G := c * g with hd
  have hle : (ψ.range).map (MulAut.conj d⁻¹).toMonoidHom ≤ ψ.range := by
    calc (ψ.range).map (MulAut.conj d⁻¹).toMonoidHom
        = ((⨆ γ ∈ Δ.roots, Δ.rootGroup γ).map ψ).map
            (MulAut.conj d⁻¹).toMonoidHom := by
          rw [MonoidHom.range_eq_map, ← hgen]
      _ = (⨆ γ ∈ Δ.roots, (Δ.rootGroup γ).map ψ).map
            (MulAut.conj d⁻¹).toMonoidHom := by
          simp only [Subgroup.map_iSup]
      _ = ⨆ γ ∈ Δ.roots, ((Δ.rootGroup γ).map ψ).map
            (MulAut.conj d⁻¹).toMonoidHom := by
          simp only [Subgroup.map_iSup]
      _ ≤ ψ.range := by
          refine iSup_le fun γ => iSup_le fun hγ => ?_
          rintro x ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          obtain ⟨h, hh, hconj⟩ := hroot γ hγ
          refine ⟨h * w * h⁻¹, ?_⟩
          change ψ (h * w * h⁻¹) = (MulAut.conj d⁻¹) (ψ w)
          rw [MulAut.conj_apply]
          simpa [hd] using (hconj w hw).symm
  have hcard : Nat.card ((ψ.range).map (MulAut.conj d⁻¹).toMonoidHom) = Nat.card ψ.range :=
    Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective
  have heq : (ψ.range).map (MulAut.conj d⁻¹).toMonoidHom = ψ.range :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hdN : d⁻¹ ∈ Subgroup.normalizer (ψ.range : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hdN' : d ∈ Subgroup.normalizer (ψ.range : Set G) := by
    simpa using Subgroup.inv_mem _ hdN
  have hgN : g ∈ Subgroup.normalizer (ψ.range : Set G) := Subgroup.le_normalizer hg
  have hc_eq : c = d * g⁻¹ := by rw [hd]; group
  rw [hc_eq]
  exact Subgroup.mul_mem _ hdN' (Subgroup.inv_mem _ hgN)

end Config

private theorem markDeg_eq_one_of_not_char3 {lab : LargeEvenLabel}
    (hl : LargeEvenInLambda2 lab) (hn : lab.n = 1) (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (hnc : ¬ CFSG.LocalAnalysis.GLTheoremA.IsChar3Lab lab) : markDeg lab = 1 := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hn hne hnc ⊢
  cases t
  case twD =>
    simp only [markDeg]
    split_ifs with h2
    · exfalso
      exact hne (by rw [h2, hn])
    · exact hn
  case B2der =>
    unfold CFSG.LocalAnalysis.GLTheoremA.IsChar3Lab at hnc
    exact absurd (Or.inl rfl) hnc
  case G2der =>
    unfold CFSG.LocalAnalysis.GLTheoremA.IsChar3Lab at hnc
    exact absurd (Or.inr rfl) hnc
  all_goals
    simp only [markDeg]
    exact hn

section Label

theorem GGConfig.exists_markedModel_and_hasLabel_of_qTwo {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧
      lab.tag ≠ .B2der ∧ MarkedModel lab (↥L ⧸ Subgroup.center ↥L) ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hq
  have hrawM : LargeEvenRawDatum lab (fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
          GGLabQTwo 3 lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab (fun R _ I F hq => hq.2.1) hraw
  obtain ⟨R, _, I, F, hQ, hMark⟩ := largeEvenRawDatum_exists hrawM
  obtain ⟨-, -, θ, hQTwo, -, -⟩ := hQ
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hQTwo
    omega
  have hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R' _ I' F' ⟨-, -, θ', -⟩
    exact ⟨θ'⟩
  have hex : ¬ (lab = ⟨.twD, 2, 1⟩ ∨ lab.tag = .B2der) := by
    intro hS
    have hrawST : LargeEvenRawDatum lab
        (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
            GGLabQTwo 3 lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
      (largeEvenRawDatum_legacy _ _).mpr hraw
    have hsplit : LargeEvenSplit 3 lab := Or.inr (Or.inr (Or.inr ⟨hn, rfl⟩))
    have hM : LargeEvenMarking L (fun lab' _ _ I' _ θ' =>
        (3 = 3 ∧ (lab' = (⟨.twD, 2, 1⟩ : LargeEvenLabel) ∨ lab'.tag = .B2der)) ∧
        LargeEvenSplit 3 lab' ∧ B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I', LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
      refine ⟨hperf, ⟨lab, hlab, ?_⟩⟩
      refine largeEvenRawDatum_mono (lab := lab) ?_ hrawST
      rintro R _ I F ⟨hs, hna, θ0, hQ0, hBsN, h3⟩
      exact ⟨hs, hna, θ0, ⟨⟨rfl, hS⟩, hsplit, hC.2.1.1.trans hBsN,
        fun b hb => h3 b (hC.2.1.1 hb)⟩⟩
    exact ggThmIHyp_false_of_labelAll
      (S := fun p lab' => p = 3 ∧ (lab' = (⟨.twD, 2, 1⟩ : LargeEvenLabel) ∨ lab'.tag = .B2der))
      (fun p lab' _ hlab' hS' _ => by
        obtain ⟨rfl, hS'⟩ := hS'
        rcases hS' with rfl | htag
        · exact largeEvenLabelAll_card_lt_linearTwo (p := 3) (by norm_num) (by norm_num)
            hlab' (Or.inr ⟨rfl, rfl⟩)
        · exact largeEvenLabelAll_card_lt_b2derThree ⟨rfl, htag⟩) hC.1 hM
  exact ⟨lab, hlab, hn, fun h => hex (Or.inl h), fun h => hex (Or.inr h),
    MarkedModel.of_mulEquiv θ.symm hMark, hhas⟩

theorem GGConfig.exists_markedModel_of_qTwo {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧
      lab.tag ≠ .B2der ∧ MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨lab, hlab, hn, hne, hB2, hmodel, -⟩ :=
    hC.exists_markedModel_and_hasLabel_of_qTwo hq
  exact ⟨lab, hlab, hn, hne, hB2, hmodel⟩

end Label

private theorem exists_clsLab_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {m f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : LieModel X t m 2 f) :
    ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
      CFSG.LocalAnalysis.GLTheoremA.IsClsLab lab' ∧ MarkedModel lab' X := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨.A, m - 1, f⟩, ?_, Or.inl rfl, ?_⟩
    · change 1 ≤ f ∧ 1 ≤ m - 1 ∧ (m - 1 = 1 → 2 ≤ f)
      obtain ⟨-, hf, hm, hne2, -⟩ := h.admissible
      refine ⟨hf, by omega, fun hm1 => ?_⟩
      have hm2 : m = 2 := by omega
      subst hm2
      have hf1 : f ≠ 1 := by
        intro hf1
        exact hne2 (by rw [hf1]; norm_num)
      omega
    · obtain ⟨-, -, hm, -⟩ := h.admissible
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      rw [Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) hm)]
      exact h
  · refine ⟨⟨.twA, m - 1, f⟩, ?_, Or.inr (Or.inl rfl), ?_⟩
    · change 1 ≤ f ∧ 2 ≤ m - 1 ∧ (m - 1 = 2 → 2 ≤ f)
      obtain ⟨-, hf, hm, hne3⟩ := h.admissible
      refine ⟨hf, by omega, fun hm2 => ?_⟩
      have hm3 : m = 3 := by omega
      subst hm3
      have hf1 : f ≠ 1 := by
        intro hf1
        exact hne3 (by rw [hf1]; norm_num)
      omega
    · obtain ⟨-, -, hm, -⟩ := h.admissible
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
      rw [Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 3) hm)]
      exact h
  · refine ⟨⟨.C, m, f⟩, ?_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
    change 1 ≤ f ∧ 2 ≤ m ∧ (m = 2 → 2 ≤ f)
    obtain ⟨-, hf, hm, hne2⟩ := h.admissible
    refine ⟨hf, hm, fun hm2 => ?_⟩
    subst hm2
    have hf1 : f ≠ 1 := by
      intro hf1
      exact hne2 (by rw [hf1]; norm_num)
    omega
  · obtain ⟨-, hf, hm⟩ := h.admissible
    have hm3 : m ≠ 3 := by omega
    refine ⟨⟨.D, m, f⟩, ⟨hf, show 3 ≤ m by omega⟩,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_⟩
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
    rw [if_neg hm3, if_neg hm3]
    exact h
  · obtain ⟨-, hf, hm⟩ := h.admissible
    have hm2 : m ≠ 2 := by omega
    have hm3 : m ≠ 3 := by omega
    refine ⟨⟨.twD, m, f⟩, ⟨hf, show 2 ≤ m by omega⟩,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_⟩
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg]
    rw [if_neg hm2, if_neg hm3, if_neg hm2, if_neg hm3, if_neg hm2]
    exact h

section TypeDet

theorem cls_typeDet {X : Type} [Group X] {lab : LargeEvenLabel} (h2 : markChar lab = 2)
    (hM : MarkedModel lab X) {t : StatedLieTag} {m f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : LieModel X t m 2 f) :
    t = markTag lab ∧ m = markRank lab ∧ f = markDeg lab := by
  have hM2 : LieModel X (markTag lab) (markRank lab) 2 (markDeg lab) :=
    CFSG.LocalAnalysis.GLTheoremA.lieModel_of_mark_two hM h2
  obtain ⟨lab', hlab', hc', hM'⟩ := exists_clsLab_of_lieModel ht h
  have hdet2 := CFSG.LocalAnalysis.GLTheoremA.cls_det hlab' hc' hM' hM2
  have hdet := CFSG.LocalAnalysis.GLTheoremA.cls_det hlab' hc' hM' h
  exact ⟨hdet.1.trans hdet2.1.symm, hdet.2.1.trans hdet2.2.1.symm,
    hdet.2.2.trans hdet2.2.2.symm⟩

theorem fieldTwo_typeDet {X : Type} [Group X] {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hn : lab.n = 1) (hne : lab ≠ ⟨.twD, 2, 1⟩) (hM : MarkedModel lab X) {t : StatedLieTag}
    {m f : ℕ} (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : LieModel X t m 2 f) :
    f = 1 ∧ t = markTag lab ∧ m = markRank lab := by
  by_cases hnc : CFSG.LocalAnalysis.GLTheoremA.IsChar3Lab lab
  · unfold CFSG.LocalAnalysis.GLTheoremA.IsChar3Lab at hnc
    rcases hnc with htag | htag
    · have h360 : Nat.card X = 360 := ggMarkedModel_card_b2der htag hM
      have hord := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h
      exact absurd (hord.symm.trans h360)
        (ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible h.admissible)
    · have h6048 : Nat.card X = 6048 :=
        CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der htag hM
      exact absurd h6048
        (CFSG.LocalAnalysis.GLTheoremA.I141F.Ord.card_ne_6048_of_lieModel h)
  · obtain ⟨ht', hm', hf'⟩ :=
      cls_typeDet (CFSG.LocalAnalysis.GLTheoremA.markChar_two_of_not_char3 hnc) hM ht h
    exact ⟨hf'.trans (markDeg_eq_one_of_not_char3 hl hn hne hnc), ht', hm'⟩

end TypeDet

theorem ClassicalPosition.IsGLLift.zpow_of_injective {U X ι K : Type} [Group U] [Finite U]
    [Group X] [Fintype ι] [DecidableEq ι] [Field K] {j : U →* GL ι K} (hj : Function.Injective j)
    {ψ : U →* X} {s : GL ι K} {b : X} (hs : ClassicalPosition.IsGLLift j ψ s b) (k : ℤ) :
    ClassicalPosition.IsGLLift j ψ (s ^ k) (b ^ k) := by
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg k
  · rw [h]
    simpa only [zpow_natCast] using hs.pow n
  · rw [h]
    have h1 : ClassicalPosition.IsGLLift j ψ ((s⁻¹) ^ n) ((b⁻¹) ^ n) :=
      (hs.inv_of_injective hj).pow n
    have hs' : s ^ (-(n : ℤ)) = (s⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast]
      group
    have hb' : b ^ (-(n : ℤ)) = (b⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast]
      group
    rw [hs', hb']
    exact h1

end CFSG.StandardType

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.StandardType.PsiDiagChar
  CFSG.StandardType.RankOneXfer

lemma slMap_sl2Upper {k k' : Type*} [Field k] [Field k'] (e : k' ≃+* k) (t : k') :
    Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom (sl2Upper t) = sl2Upper (e t) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    coe_sl2Upper]
  fin_cases i <;> fin_cases j <;> simp

lemma slMap_sl2Diag {k k' : Type*} [Field k] [Field k'] (e : k' ≃+* k) (a : k'ˣ) :
    Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom (sl2Diag a) =
      sl2Diag (Units.map e.toMonoidHom a) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    coe_sl2Diag, Units.coe_map]
  fin_cases i <;> fin_cases j <;> simp

lemma slMap_sl2UpperUniSub {k k' : Type*} [Field k] [Field k'] (e : k' ≃+* k) :
    (sl2UpperUniSub k').map (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) =
      sl2UpperUniSub k := by
  ext M
  constructor
  · rintro ⟨N, hN, rfl⟩
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hN
    rw [slMap_sl2Upper]
    exact mem_sl2UpperUniSub_iff.mpr ⟨e t, rfl⟩
  · intro hM
    obtain ⟨t, rfl⟩ := mem_sl2UpperUniSub_iff.mp hM
    obtain ⟨t', ht'⟩ := e.surjective t
    exact ⟨sl2Upper t', mem_sl2UpperUniSub_iff.mpr ⟨t', rfl⟩, by rw [slMap_sl2Upper, ht']⟩

lemma slMap_injective {k k' : Type*} [Field k] [Field k'] (e : k' ≃+* k) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
  intro A B hAB
  ext i j
  apply e.injective
  have h' := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
    (M : Matrix (Fin 2) (Fin 2) k) i j) hAB
  simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using h'

lemma slMap_surjective {k k' : Type*} [Field k] [Field k'] (e : k' ≃+* k) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
  intro A
  refine ⟨Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom A, ?_⟩
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]

@[expose] noncomputable def SelectedSL2Model.congrField {K : Type*} [Group K]
    {D : UniversalRootDatum K}
    {k k' : Type*} [Field k] [Field k'] {γ : Fin D.rank → ℤ} (M : SelectedSL2Model D k γ)
    (e : k' ≃+* k) : SelectedSL2Model D k' γ where
  root_mem := M.root_mem
  phi := M.phi.comp (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom)
  injective := M.injective.comp (slMap_injective e)
  upper_eq := by
    rw [← Subgroup.map_map, slMap_sl2UpperUniSub e, M.upper_eq]
  diag_mem := by
    intro a
    rw [MonoidHom.comp_apply, slMap_sl2Diag]
    exact M.diag_mem _
  scalar := by
    intro h hh
    obtain ⟨c, hc⟩ := M.scalar h hh
    obtain ⟨c', hc'⟩ := (Units.map_bijective (f := e.toMonoidHom) e.bijective).2 c
    refine ⟨c', fun t => ?_⟩
    have hval : (c : k) = e (c' : k') := by
      have hcv := congrArg (fun u : kˣ => (u : k)) hc'.symm
      rw [Units.coe_map] at hcv
      exact hcv
    calc h * (M.phi.comp (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom))
          (sl2Upper t) * h⁻¹
        = h * M.phi (sl2Upper (e t)) * h⁻¹ := by rw [MonoidHom.comp_apply, slMap_sl2Upper]
      _ = M.phi (sl2Upper ((c : k) * e t)) := hc (e t)
      _ = M.phi (sl2Upper (e ((c' : k') * t))) := by rw [hval, map_mul]
      _ = (M.phi.comp (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom))
            (sl2Upper ((c' : k') * t)) := by
            rw [MonoidHom.comp_apply, slMap_sl2Upper]

theorem SelectedSL2Model.congrField_phi_apply {K : Type*} [Group K] {D : UniversalRootDatum K}
    {k k' : Type*} [Field k] [Field k'] {γ : Fin D.rank → ℤ} (M : SelectedSL2Model D k γ)
    (e : k' ≃+* k) (A : Matrix.SpecialLinearGroup (Fin 2) k') :
    (M.congrField e).phi A = M.phi (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom A) := rfl

end CFSG.StandardType.SelectedRoot

end
