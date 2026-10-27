module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Frame
public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Toral
public import CFSG.LieType.AschbacherSeitz.F4LangDatumOdd
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB
open CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

private theorem exists_toral_conjugator_F4Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq3 : 3 ∣ Nat.card K + 1) {E : Subgroup (adjointGroup .F4 K)}
    (hE : IsElemAbelian 3 E) (h4 : 3 ^ 4 ≤ Nat.card E) :
    ∃ g ∈ adjointGroup .F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g ∈
        torusGroup .F4 (AlgebraicClosure K) := by
  have hd : 3 ∣ Nat.card K ^ 2 - 1 :=
    hq3.trans (CFSG.Timmesfeld.Orders.add_one_dvd_sq_sub_one (Nat.card K))
  have hmax : ∀ A : Subgroup (adjointGroup .F4 K),
      IsElemAbelian 3 A → Nat.card A ≤ Nat.card E := by
    intro A hA
    exact (ExcFieldAutCentRankF4.card_le_pow_four (p := 3) Nat.prime_three
      (by norm_num) hd hA).trans h4
  obtain ⟨Fr, hFr, w, g0, hg0C, hg0, hmem⟩ :=
    CFSG.LieType.AschbacherSeitz.exists_langDatum_of_maxElem_F4 (K := K) (p := 3)
      Nat.prime_three (by norm_num) E hE h4 hmax
  refine ⟨g0, hg0C, fun x hx => ?_⟩
  exact (mem_twistedTorus.1 (hmem x hx)).1

private theorem frameDiag_mem_twistedTorus_F4Three
    {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup Tag.F4} {g0 : ModGL Tag.F4 (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1}
    {ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup Tag.F4 K}
    (hbase : ∀ s : Fin Tag.F4.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        g0 * frameDiag (τ := Tag.F4) ζ hζ s * g0⁻¹) :
    ∀ s : Fin Tag.F4.rank → ZMod 3,
      frameDiag (τ := Tag.F4) ζ hζ s ∈
        twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr := by
  intro s
  have hfix := units_map_entrywiseHom_baseChangeGL_algebraMap (k := K)
    (L := AlgebraicClosure K) Fr hFr
    ((ι₀ (Multiplicative.ofAdd s) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)
  rw [hbase s] at hfix
  rw [map_mul, map_mul, map_inv, hg0] at hfix
  refine mem_twistedTorus.2 ⟨?_, ?_⟩
  · rw [frameDiag]
    exact rootDiagUnit_mem_torusGroup _
  · have h1 : g0 * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
        Units.map (entrywiseHom Fr) (frameDiag (τ := Tag.F4) ζ hζ s) *
        (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ =
        g0 * frameDiag (τ := Tag.F4) ζ hζ s * g0⁻¹ := by
      calc g0 * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
            Units.map (entrywiseHom Fr) (frameDiag (τ := Tag.F4) ζ hζ s) *
            (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹) * g0⁻¹
          = (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) *
              Units.map (entrywiseHom Fr) (frameDiag (τ := Tag.F4) ζ hζ s) *
              (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹ := by
            group
        _ = g0 * frameDiag (τ := Tag.F4) ζ hζ s * g0⁻¹ := hfix
    exact mul_left_cancel (mul_right_cancel h1)

private theorem frameCoord_eigen_F4Three
    {K : Type} [Field K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hq : ((Nat.card K : ℕ) : ZMod 3) = -1)
    {w : WeylGroup Tag.F4} {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ 3 = 1}
    (hζo : orderOf ζ = 3)
    (hmem : ∀ s : Fin Tag.F4.rank → ZMod 3,
      frameDiag (τ := Tag.F4) ζ hζ s ∈
        twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr)
    (s : Fin Tag.F4.rank → ZMod 3) :
    (modMat 3 (weylMatrix w))ᵀ *ᵥ frameCoord Tag.F4 3 s =
      (-1 : ZMod 3) • frameCoord Tag.F4 3 s := by
  have hζprim : IsPrimitiveRoot ζ 3 := by
    have h := IsPrimitiveRoot.orderOf ζ
    rwa [hζo] at h
  have hmap : frameDiag (τ := Tag.F4) ζ hζ s ∈
      (fixedCharTuples (weylMatrix w) Fr).map
        (rootDiagUnitHom Tag.F4 (AlgebraicClosure K)) := by
    rw [← twistedTorus_eq_map_fixedCharTuples w Fr]
    exact hmem s
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.1 hmap
  change rootDiagUnit Tag.F4 a = frameDiag (τ := Tag.F4) ζ hζ s at haeq
  have haz : a = TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 3 s) := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective
    rw [haeq, frameDiag]
  have hz : TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 3 s) ∈
      fixedCharTuples (weylMatrix w) Fr := by
    rw [← haz]
    exact ha
  have hzveq : TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 3 s) =
      expTuple ζ (frameCoord Tag.F4 3 s) := by
    funext i
    rw [TableBExc.E6Three.zetaVec_apply]
    rfl
  rw [hzveq] at hz
  have heig := (expTuple_mem_fixedCharTuples_iff hζprim (weylMatrix w) Fr hFr
    (frameCoord Tag.F4 3 s)).1 hz
  rw [hq] at heig
  exact heig

private theorem modMat_weylMatrix_eq_neg_one_F4Three
    {w : WeylGroup Tag.F4}
    (hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod 3))
    (hall : ∀ s : Fin Tag.F4.rank → ZMod 3,
      (modMat 3 (weylMatrix w))ᵀ *ᵥ frameCoord Tag.F4 3 s =
        (-1 : ZMod 3) • frameCoord Tag.F4 3 s) :
    modMat 3 (weylMatrix w) = -1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsurj : Function.Surjective (frameCoord Tag.F4 3) :=
    Finite.injective_iff_surjective.mp (frameCoord_injective hdet)
  have hall' : ∀ x : Fin Tag.F4.rank → ZMod 3,
      (modMat 3 (weylMatrix w))ᵀ *ᵥ x = (-1 : ZMod 3) • x := by
    intro x
    obtain ⟨s, rfl⟩ := hsurj x
    exact hall s
  ext i j
  have h := congrFun (hall' (Pi.single i 1)) j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply] at h
  rw [Pi.smul_apply, Pi.single_apply] at h
  rw [h, Matrix.neg_apply, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij.symm, if_pos hij]; ring
  · rw [if_neg (fun hji => hij hji.symm), if_neg hij]; ring

private theorem smul_modEq_neg_of_modMat_neg_one_F4Three
    {w : WeylGroup Tag.F4} (h : modMat 3 (weylMatrix w) = -1)
    (v : Fin Tag.F4.rank → ℤ) (i : Fin Tag.F4.rank) :
    (((w • v) i : ℤ) : ZMod 3) = -(v i : ZMod 3) := by
  have hM : ∀ j, ((weylMatrix w i j : ℤ) : ZMod 3) = if i = j then -1 else 0 := by
    intro j
    have h1 : ((weylMatrix w i j : ℤ) : ZMod 3) = -if i = j then 1 else 0 := by
      have h2 := congrFun (congrFun h i) j
      rw [modMat, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply] at h2
      simpa using h2
    rw [h1]
    by_cases hij : i = j <;> simp [hij]
  calc
    (((w • v) i : ℤ) : ZMod 3) = (((weylMatrix w).mulVec v) i : ZMod 3) := by
      rw [← weylMatrix_mulVec]
    _ = ((∑ j, weylMatrix w i j * v j : ℤ) : ZMod 3) := by
      rw [Matrix.mulVec_apply_eq_sum]
    _ = ∑ j, ((weylMatrix w i j : ℤ) : ZMod 3) * (v j : ZMod 3) := by
      push_cast; rfl
    _ = ∑ j, (if i = j then (-1 : ZMod 3) else 0) * (v j : ZMod 3) := by
      exact Finset.sum_congr rfl fun j _ => by rw [hM j]
    _ = -(v i : ZMod 3) := by simp

private theorem mul_f4Neg_eq_one_of_modMat_neg_one_F4Three
    {w : WeylGroup Tag.F4} (h : modMat 3 (weylMatrix w) = -1) :
    w * f4Neg = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.RankThree.Chevalley.F4_eq_one_of_smul_modEq (p := 3) (by norm_num)
    fun v i => ?_
  rw [mul_smul, f4Neg_smul]
  have h1 := smul_modEq_neg_of_modMat_neg_one_F4Three h (-v) i
  rw [h1]
  simp

private theorem f4Neg_mul_self_F4Three :
    f4Neg * f4Neg = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.RankThree.Chevalley.F4_eq_one_of_smul_modEq (p := 3) (by norm_num)
    fun v i => ?_
  rw [mul_smul, f4Neg_smul, f4Neg_smul]
  simp

private theorem eq_f4Neg_of_mul_f4Neg_eq_one_F4Three
    {w : WeylGroup Tag.F4} (hmul : w * f4Neg = 1) (hsq : f4Neg * f4Neg = 1) :
    w = f4Neg := by
  calc w = w * 1 := (mul_one w).symm
    _ = w * (f4Neg * f4Neg) := by rw [hsq]
    _ = (w * f4Neg) * f4Neg := by group
    _ = f4Neg := by rw [hmul]; group

theorem exists_langFrame_F4_three
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq3 : 3 ∣ Nat.card K + 1)
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian 3 E) (h4 : 3 ^ 4 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ 3 = 1 → x ∈ E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL .F4 (AlgebraicClosure K))
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ 3 = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .F4 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) f4Neg ∧
      orderOf ζ = 3 ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ s : Fin Tag.F4.rank → ZMod 3,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ := by
  obtain ⟨g, hgC, htor⟩ := exists_toral_conjugator_F4Three (K := K) hq3 hE h4
  have hcard : 3 ^ 3 ≤ Nat.card E := (by norm_num : (3 : ℕ) ^ 3 ≤ 3 ^ 4).trans h4
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, _hcent, hζo, hιinj, hιrange, hιbase⟩ :=
    Irred937.exists_langFrame_F4 K hq3 E hE ⟨g, hgC, htor⟩ hcard hSC
  have hq : ((Nat.card K : ℕ) : ZMod 3) = -1 := SpNS.natCast_card_eq_neg_one hq3
  have hmem := frameDiag_mem_twistedTorus_F4Three (K := K) hFr hg0 hιbase
  have hall := fun s => frameCoord_eigen_F4Three (K := K) hFr hq hζo hmem s
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod 3) :=
    isUnit_det_symmetrizedCartan (Or.inl rfl) (p := 3) (by norm_num)
  have hmod : modMat 3 (weylMatrix w) = -1 :=
    modMat_weylMatrix_eq_neg_one_F4Three hdet hall
  have hmul : w * f4Neg = 1 := mul_f4Neg_eq_one_of_modMat_neg_one_F4Three hmod
  have hsq : f4Neg * f4Neg = 1 := f4Neg_mul_self_F4Three
  have hw : w = f4Neg := eq_f4Neg_of_mul_f4Neg_eq_one_F4Three hmul hsq
  rw [hw] at hg0
  exact ⟨Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hζo, hιinj, hιrange, hιbase⟩

end CFSG.StandardType

end
