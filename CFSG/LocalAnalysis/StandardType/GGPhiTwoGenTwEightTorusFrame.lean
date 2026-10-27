module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightTorus

public noncomputable section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Malle.SeitzCube
open scoped MatrixGroups


private lemma prod_reverse_map_smul (l : List (Fin TwistTag.E6.foldedTag.rank))
    (x : Fin TwistTag.E6.tag.rank → ℤ) :
    ((l.reverse.map fun a => TwistTag.E6.orbitReflection a).prod) • x =
      l.foldl (fun v a => TwistTag.E6.orbitReflection a • v) x := by
  induction l generalizing x with
  | nil => simp
  | cons a l ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    rw [mul_smul, ih, List.foldl_cons]

private lemma frameRoot_zero_eq :
    frameRoot (0 : Fin 4) =
      (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1 :
        Fin TwistTag.E6.tag.rank → ℤ) := by
  decide +kernel

private lemma frameCoroot_eq_corootPair (i : Fin 4) (k : Fin 6) :
    ((corootPair (frameRoot i) (Pi.single k 1) : ℤ) : ZMod 3) = frameCoroot i k := by
  fin_cases i <;> fin_cases k <;> decide +kernel


variable {K : Type} [Field K] [CharP K 2]

private def frameWeyl (i : Fin 4) : WeylGroup TwistTag.E6.tag :=
  ((frameSeq i).reverse.map fun a => TwistTag.E6.orbitReflection a).prod

private lemma prod_reverse_map_orbitN (σ : K →+* K) (i : Fin 4) :
    frameConj σ i = canonicalRep (coxeterSystem TwistTag.E6.tag) K (frameWeyl i) := by
  rw [frameConj, ← List.map_reverse, frameWeyl]
  generalize (frameSeq i).reverse = l
  induction l with
  | nil => simp [canonicalRep_one]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    rw [List.map_cons, List.prod_cons,
      CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
      ← canonicalRep_orbitReflection_eq_orbitN (t := TwistTag.E6) (σ := σ) a]

private lemma frameWeyl_smul (i : Fin 4) :
    frameWeyl i • (Pi.single (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) 1) = frameRoot i := by
  rw [frameWeyl, prod_reverse_map_smul, frameSeq_fold]

private theorem rankOneFix_leaf_eq (σ : K →+* K) :
    (rankOneFix σ orbLeaf orbLeaf_card) =
      (rootSL2 TwistTag.E6.tag K (frameRoot 0)).comp
        (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype) := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      (K := RingHom.eqLocusField σ (RingHom.id K))) ?_
  rintro M (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · change rankOneFix σ orbLeaf orbLeaf_card (uSL c) =
      rootSL2 TwistTag.E6.tag K (frameRoot 0)
        (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype (uSL c))
    have h1 : rankOneFix σ orbLeaf orbLeaf_card (CFSG.Timmesfeld.tv 0 1 c) =
        xUnit TwistTag.E6.tag K (CFSG.RankThree.E6.e6Index 3) (c : K) := (rankOneFix_leaf_tv σ c).1
    rw [tv_zero_one_eq_uSL] at h1
    rw [h1, map_uSL, rootSL2_uSL_of_charTwo (isRoot_frameRoot 0), frameRoot_zero_eq,
      pinnedX_single]
    rfl
  · change rankOneFix σ orbLeaf orbLeaf_card (vSL c) =
      rootSL2 TwistTag.E6.tag K (frameRoot 0)
        (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype (vSL c))
    have h1 : rankOneFix σ orbLeaf orbLeaf_card (CFSG.Timmesfeld.tv 1 0 c) =
        yUnit TwistTag.E6.tag K (CFSG.RankThree.E6.e6Index 3) (c : K) := (rankOneFix_leaf_tv σ c).2
    rw [tv_one_zero_eq_vSL] at h1
    rw [h1, map_vSL, rootSL2_vSL_of_charTwo (isRoot_frameRoot 0), frameRoot_zero_eq,
      pinnedX_neg_single]
    rfl

theorem frameRaw_eq_rootSL2 (σ : K →+* K) (i : Fin 4)
    (B : Matrix.SpecialLinearGroup (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) :
    frameRaw σ i B = rootSL2 TwistTag.E6.tag K (frameRoot i)
      (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype B) := by
  unfold frameRaw
  rw [MonoidHom.comp_apply]
  change frameConj σ i * rankOneFix σ orbLeaf orbLeaf_card B * (frameConj σ i)⁻¹ = _
  rw [prod_reverse_map_orbitN σ i]
  change canonicalRep (coxeterSystem TwistTag.E6.tag) K (frameWeyl i) *
      rankOneFix σ orbLeaf orbLeaf_card B *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K (frameWeyl i))⁻¹ = _
  rw [rankOneFix_leaf_eq σ]
  change canonicalRep (coxeterSystem Tag.E6) K (frameWeyl i) *
      rootSL2 Tag.E6 K (frameRoot 0)
        (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype B) *
      (canonicalRep (coxeterSystem Tag.E6) K (frameWeyl i))⁻¹ =
    rootSL2 Tag.E6 K (frameRoot i)
      (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype B)
  have hsmul_any (h : 3 < TwistTag.E6.tag.rank) :
      frameWeyl i • (Pi.single (⟨3, h⟩ : Fin TwistTag.E6.tag.rank) 1) = frameRoot i := by
    rw [show (⟨3, h⟩ : Fin TwistTag.E6.tag.rank) = ⟨3, by decide⟩ from Fin.ext rfl]
    exact frameWeyl_smul i
  rw [CFSG.RankThree.PartOne.KE6.canonicalRep_conj_rootSL2 (frameWeyl i)
      (isRoot_frameRoot 0) (Matrix.SpecialLinearGroup.map
        (RingHom.eqLocusField σ (RingHom.id K)).subtype B)]
  have hroot : frameWeyl i • frameRoot 0 = frameRoot i := by
    rw [frameRoot_zero_eq]
    exact hsmul_any _
  erw [hroot]

@[expose] def frameTorusHom (ζu : Kˣ) (hζu : ζu ^ 3 = 1) (a : ModGL TwistTag.E6.tag K) :
    Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3) →* ModGL TwistTag.E6.tag K :=
  (MulAut.conj a).toMonoidHom.comp
    ((rootDiagUnitHom TwistTag.E6.tag K).comp (NoOffE6Three.zetaHom ζu hζu))

omit
  [CharP K 2] in
theorem frameTorusHom_apply (ζu : Kˣ) (hζu : ζu ^ 3 = 1) (a : ModGL TwistTag.E6.tag K)
    (x : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod 3)) :
    frameTorusHom ζu hζu a x =
      a * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζu hζu x.toAdd) * a⁻¹ := by
  unfold frameTorusHom
  change MulAut.conj a (rootDiagUnit TwistTag.E6.tag
      (TableBExc.E6Three.zetaVec ζu hζu x.toAdd)) = _
  rw [MulAut.conj_apply]

omit
  [CharP K 2] in
theorem frameTorusHom_injective {ζu : Kˣ} (hζo : orderOf ζu = 3) (hζu : ζu ^ 3 = 1)
    {a : ModGL TwistTag.E6.tag K} : Function.Injective (frameTorusHom ζu hζu a) := by
  intro x y h
  have h1 : rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζu hζu x.toAdd) =
      rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζu hζu y.toAdd) := by
    have h' := congrArg (fun z => a⁻¹ * z * a) h
    simpa [frameTorusHom_apply, mul_assoc] using h'
  have h2 : TableBExc.E6Three.zetaVec ζu hζu x.toAdd =
      TableBExc.E6Three.zetaVec ζu hζu y.toAdd :=
    rootDiagUnit_injective h1
  have h3 : x.toAdd = y.toAdd :=
    TableBExc.E6Three.zetaVec_injective hζo hζu h2
  exact Multiplicative.toAdd.injective h3

private def frameB0 (K : Type) [Field K] : SL2 K := uSL (1 : K) * nSL 1

private def frameB0Fix (σ : K →+* K) :
    SL2 (RingHom.eqLocusField σ (RingHom.id K)) :=
  uSL (1 : RingHom.eqLocusField σ (RingHom.id K)) * nSL 1

omit
  [CharP K 2] in
private lemma map_nSL_one' {L : Type} [Field L] (f : L →+* K) :
    Matrix.SpecialLinearGroup.map f (nSL (1 : Lˣ)) = nSL (1 : Kˣ) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [nSL]

omit
  [CharP K 2] in
private theorem map_frameB0Fix (σ : K →+* K) :
    Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype
        (frameB0Fix σ) = frameB0 K := by
  simp [frameB0, frameB0Fix, map_mul, map_uSL, map_nSL_one']

private theorem frameLang_eq_prod {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    frameLang ζ hζ =
      (List.ofFn fun i : Fin 4 =>
        rootSL2 TwistTag.E6.tag K (frameRoot i) (frameLangSL2 ζ hζ)).prod := by
  simp [frameLang, List.ofFn_succ, List.ofFn_zero, mul_assoc]

private theorem frameLang_mul_HSL {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0) (i : Fin 4) :
    frameLang (ζu : K) hζ * rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu) =
      rootSL2 TwistTag.E6.tag K (frameRoot i)
        (frameLangSL2 (ζu : K) hζ * HSL ζu * (frameLangSL2 (ζu : K) hζ)⁻¹) *
          frameLang (ζu : K) hζ := by
  rw [frameLang_eq_prod]
  let f : Fin 4 → ModGL TwistTag.E6.tag K :=
    fun j => rootSL2 TwistTag.E6.tag K (frameRoot j) (frameLangSL2 (ζu : K) hζ)
  change (List.ofFn f).prod * rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu) =
    rootSL2 TwistTag.E6.tag K (frameRoot i)
      (frameLangSL2 (ζu : K) hζ * HSL ζu * (frameLangSL2 (ζu : K) hζ)⁻¹) *
        (List.ofFn f).prod
  refine CFSG.StandardType.TwE6CorootCore.list_prod_ofFn_mul_eq f i ?_ ?_
  · rw [← map_mul, ← map_mul]
    congr 1
    group
  · intro j hj
    constructor
    · exact rootSL2_frameRoot_commute hj (frameLangSL2 (ζu : K) hζ) (HSL ζu)
    · rw [map_mul, map_mul, map_inv]
      have hA : Commute (f j)
          (rootSL2 TwistTag.E6.tag K (frameRoot i) (frameLangSL2 (ζu : K) hζ)) :=
        rootSL2_frameRoot_commute hj (frameLangSL2 (ζu : K) hζ) (frameLangSL2 (ζu : K) hζ)
      have hS : Commute (f j) (rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu)) :=
        rootSL2_frameRoot_commute hj (frameLangSL2 (ζu : K) hζ) (HSL ζu)
      exact (hA.mul_right hS).mul_right hA.inv_right


open CFSG.StandardType.TableBExcTwoFusion

variable {K : Type} [Field K] [CharP K 2]

private lemma frameLangSL2_eq {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    frameLangSL2 ζ hζ = nSL (1 : Kˣ) * langP hζ := by
  ext i j
  change (!![ζ, ζ ^ 2; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j =
    ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) *
      (!![1, 1; ζ, ζ ^ 2] : Matrix (Fin 2) (Fin 2) K)) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private lemma nSL_mul_uSL_mul_vSL :
    (nSL (1 : Kˣ) : SL2 K) * (uSL (1 : K) * vSL (1 : K)) = uSL (1 : K) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq,
      CharTwo.add_self_eq_zero]

private lemma nSL_mul_self : (nSL (1 : Kˣ) : SL2 K) * nSL 1 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [nSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private lemma frameLangSL2_mul_HSL {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0) :
    frameLangSL2 (ζu : K) hζ * HSL ζu = frameB0 K * frameLangSL2 (ζu : K) hζ := by
  have hP : langP hζ * HSL ζu = (uSL (1 : K) * vSL (1 : K)) * langP hζ :=
    langP_mul_HSL hζ
  calc frameLangSL2 (ζu : K) hζ * HSL ζu
      = (nSL (1 : Kˣ) * langP hζ) * HSL ζu := by rw [frameLangSL2_eq hζ]
    _ = nSL (1 : Kˣ) * (langP hζ * HSL ζu) := by group
    _ = nSL (1 : Kˣ) * ((uSL (1 : K) * vSL (1 : K)) * langP hζ) := by rw [hP]
    _ = (nSL (1 : Kˣ) * (uSL (1 : K) * vSL (1 : K))) * langP hζ := by group
    _ = uSL (1 : K) * langP hζ := by rw [nSL_mul_uSL_mul_vSL]
    _ = frameB0 K * frameLangSL2 (ζu : K) hζ := by
        rw [frameB0]
        calc uSL (1 : K) * langP hζ
            = uSL (1 : K) * (nSL (1 : Kˣ) * nSL 1) * langP hζ := by
              rw [nSL_mul_self]; group
          _ = (uSL (1 : K) * nSL (1 : Kˣ)) * (nSL 1 * langP hζ) := by group
          _ = (uSL (1 : K) * nSL (1 : Kˣ)) * frameLangSL2 (ζu : K) hζ := by
              rw [← frameLangSL2_eq hζ]

omit
  [CharP K 2] in
private lemma zpow_zmod_val {ζu : Kˣ} (hζo : orderOf ζu = 3)
    (c : ℤ) : ζu ^ (((c : ZMod 3)).val) = ζu ^ c := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hζo]
  rw [Int.modEq_iff_dvd]
  have hdvd : (3 : ℤ) ∣ (((c : ZMod 3).val : ℤ) - c) := by
    have h0 : (((((c : ZMod 3).val : ℤ) - c : ℤ)) : ZMod 3) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  simpa [neg_sub] using dvd_neg.mpr hdvd

omit
  [CharP K 2] in
private lemma frame_torus_coroot {ζu : Kˣ} (hζo : orderOf ζu = 3) (hζu : ζu ^ 3 = 1)
    (i : Fin 4) :
    rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζu hζu (frameCoroot i)) =
      rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu) := by
  have hzv : TableBExc.E6Three.zetaVec (τ := TwistTag.E6.tag) ζu hζu (frameCoroot i) =
      fun k => ζu ^ corootPair (frameRoot i) (Pi.single k 1) := by
    funext k
    change ζu ^ ((frameCoroot i k).val) = ζu ^ corootPair (frameRoot i) (Pi.single k 1)
    rw [← frameCoroot_eq_corootPair i k]
    exact zpow_zmod_val hζo _
  rw [hzv]
  exact (@rootSL2_HSL_eq_coroot K _ (frameRoot i) (isRoot_frameRoot i) ζu).symm

private lemma frameTorusHom_coroot {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0)
    (hζo : orderOf ζu = 3) (hζu : ζu ^ 3 = 1) (σ : K →+* K) (i : Fin 4) :
    frameTorusHom ζu hζu (frameLang (ζu : K) hζ)
        (Multiplicative.ofAdd (frameCoroot i)) =
      frameRaw σ i (frameB0Fix σ) := by
  rw [frameTorusHom_apply]
  change frameLang (ζu : K) hζ *
      rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec ζu hζu (frameCoroot i)) *
      (frameLang (ζu : K) hζ)⁻¹ = _
  rw [show rootDiagUnit TwistTag.E6.tag
        (TableBExc.E6Three.zetaVec ζu hζu (frameCoroot i)) =
      rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu) from frame_torus_coroot hζo hζu i]
  have hstep := frameLang_mul_HSL hζ i
  calc frameLang (ζu : K) hζ * rootSL2 TwistTag.E6.tag K (frameRoot i) (HSL ζu) *
        (frameLang (ζu : K) hζ)⁻¹
      = rootSL2 TwistTag.E6.tag K (frameRoot i)
          (frameLangSL2 (ζu : K) hζ * HSL ζu * (frameLangSL2 (ζu : K) hζ)⁻¹) *
          frameLang (ζu : K) hζ * (frameLang (ζu : K) hζ)⁻¹ := by rw [hstep]
    _ = rootSL2 TwistTag.E6.tag K (frameRoot i)
          (frameLangSL2 (ζu : K) hζ * HSL ζu * (frameLangSL2 (ζu : K) hζ)⁻¹) := by group
    _ = rootSL2 TwistTag.E6.tag K (frameRoot i) (frameB0 K) := by
        congr 1
        calc frameLangSL2 (ζu : K) hζ * HSL ζu * (frameLangSL2 (ζu : K) hζ)⁻¹
            = (frameB0 K * frameLangSL2 (ζu : K) hζ) * (frameLangSL2 (ζu : K) hζ)⁻¹ := by
              rw [frameLangSL2_mul_HSL hζ]
          _ = frameB0 K := by group
    _ = rootSL2 TwistTag.E6.tag K (frameRoot i)
          (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField σ (RingHom.id K)).subtype
            (frameB0Fix σ)) := by rw [map_frameB0Fix]
    _ = frameRaw σ i (frameB0Fix σ) := (frameRaw_eq_rootSL2 σ i (frameB0Fix σ)).symm


theorem frameTorusHom_mem_frame {ζu : Kˣ} (hζ : (ζu : K) ^ 2 + ζu + 1 = 0)
    (hζo : orderOf ζu = 3) (hζu : ζu ^ 3 = 1) (σ : K ≃+* K)
    {t : Fin TwistTag.E6.tag.rank → ZMod 3} (ht : t ∈ frameVG) :
    frameTorusHom ζu hζu (frameLang (ζu : K) hζ)
        (Multiplicative.ofAdd t) ∈
      (⨆ i, (frameHom σ.toRingHom i).range).map (twistedE6RootGroup K σ).subtype := by
  let S := (⨆ i, (frameHom σ.toRingHom i).range).map (twistedE6RootGroup K σ).subtype
  let T0 := frameTorusHom ζu hζu (frameLang (ζu : K) hζ)
  let fc : Fin 4 → (Fin TwistTag.E6.tag.rank → ZMod 3) := fun i => frameCoroot i
  have hdec := frameVG_decomp t ht
  let c0 : ℤ := 2 * ((t 3).val : ℤ)
  let c1 : ℤ := ((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)
  let c2 : ℤ := ((t 0).val : ℤ) + ((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)
  let c3 : ℤ := ((t 0).val : ℤ) + ((t 1).val : ℤ) + 2 * ((t 2).val : ℤ)
  let vs : Fin TwistTag.E6.tag.rank → ZMod 3 :=
    c0 • fc 0 + c1 • fc 1 + c2 • fc 2 + c3 • fc 3
  have hdec' : t = vs := by
    change t = (2 * ((t 3).val : ℤ)) • frameCoroot 0 +
        (((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 1 +
        (((t 0).val : ℤ) + ((t 2).val : ℤ) + 2 * ((t 3).val : ℤ)) • frameCoroot 2 +
        (((t 0).val : ℤ) + ((t 1).val : ℤ) + 2 * ((t 2).val : ℤ)) • frameCoroot 3
    exact hdec
  have hmem : ∀ i : Fin 4, T0 (Multiplicative.ofAdd (fc i)) ∈ S := by
    intro i
    have hi := frameTorusHom_coroot hζ hζo hζu σ.toRingHom i
    change T0 (Multiplicative.ofAdd (frameCoroot i)) ∈ S
    rw [hi, ← coe_frameHom]
    have hy : frameHom σ.toRingHom i (frameB0Fix σ.toRingHom) ∈
        (frameHom σ.toRingHom i).range := ⟨frameB0Fix σ.toRingHom, rfl⟩
    have hy' : frameHom σ.toRingHom i (frameB0Fix σ.toRingHom) ∈
        ⨆ i, (frameHom σ.toRingHom i).range := Subgroup.mem_iSup_of_mem i hy
    exact Subgroup.mem_map_of_mem _ hy'
  have hprod : T0 (Multiplicative.ofAdd t) =
      (T0 (Multiplicative.ofAdd (fc 0))) ^ c0 *
        (T0 (Multiplicative.ofAdd (fc 1))) ^ c1 *
        (T0 (Multiplicative.ofAdd (fc 2))) ^ c2 *
        (T0 (Multiplicative.ofAdd (fc 3))) ^ c3 := by
    calc T0 (Multiplicative.ofAdd t)
        = T0 (Multiplicative.ofAdd vs) := by rw [hdec']
      _ = T0 (Multiplicative.ofAdd (c0 • fc 0)) *
            T0 (Multiplicative.ofAdd (c1 • fc 1)) *
            T0 (Multiplicative.ofAdd (c2 • fc 2)) *
            T0 (Multiplicative.ofAdd (c3 • fc 3)) := by
            simp only [vs, ofAdd_add, map_mul]
      _ = (T0 (Multiplicative.ofAdd (fc 0))) ^ c0 *
            (T0 (Multiplicative.ofAdd (fc 1))) ^ c1 *
            (T0 (Multiplicative.ofAdd (fc 2))) ^ c2 *
            (T0 (Multiplicative.ofAdd (fc 3))) ^ c3 := by
            simp only [ofAdd_zsmul, map_zpow]
  rw [hprod]
  exact mul_mem (mul_mem (mul_mem (zpow_mem (hmem 0) c0) (zpow_mem (hmem 1) c1))
    (zpow_mem (hmem 2) c2)) (zpow_mem (hmem 3) c3)

end CFSG.StandardType.PhiTwoRootGen

end
