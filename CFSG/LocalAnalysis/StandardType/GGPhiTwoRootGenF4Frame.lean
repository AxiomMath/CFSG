module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableB
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
open CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped Matrix

theorem f4Neg_comm
    (v : WeylGroup .F4) :
    v * CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg =
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg * v := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul, smul_neg]

private abbrev f4LangTorsion (K : Type) [Field K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (p : ℕ) :
    Type :=
  {t : ModGL .F4 (AlgebraicClosure K) //
    t ∈ twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr ∧ t ^ p = 1}

private theorem frobenius_baseChangeGL_F4Frame
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, hFr, ← map_pow]
    congr 1
    letI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  calc
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y)
        = baseChangeGL Fr (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) :=
          units_map_entrywiseHom_eq_baseChangeGL Fr _
    _ = baseChangeGL (Fr.comp (algebraMap K (AlgebraicClosure K))) y :=
          baseChangeGL_baseChangeGL (f := algebraMap K (AlgebraicClosure K)) Fr y
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by rw [hcomp]

private theorem weylMatrix_f4Neg_eq_neg_one_F4Frame :
    weylMatrix (τ := Tag.F4) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg = -1 := by
  ext i j
  have hcol : (weylMatrix (τ := Tag.F4)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) *ᵥ (Pi.single j 1) =
      -(Pi.single j 1) := by
    rw [weylMatrix_mulVec, CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul]
  have h := congrFun hcol i
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.neg_apply, Pi.single_apply] at h
  by_cases hij : i = j
  · subst hij
    simpa [Matrix.neg_apply, Matrix.one_apply, Pi.single_apply] using h
  · have hji : ¬ j = i := fun hji => hij hji.symm
    simpa [Matrix.neg_apply, Matrix.one_apply, Pi.single_apply, hij, hji] using h

private theorem modMat_weylMatrix_f4Neg_eq_neg_one_F4Frame
    {p : ℕ} :
    modMat p (weylMatrix (τ := Tag.F4)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) = -1 := by
  rw [weylMatrix_f4Neg_eq_neg_one_F4Frame]
  ext i j
  simp [modMat, Matrix.neg_apply, Matrix.one_apply]

private theorem frameDiag_mem_twistedTorus_F4_neg
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hmod : modMat p (weylMatrix (τ := Tag.F4)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) = -1)
    (hq : ((Nat.card K : ℕ) : ZMod p) = -1) (s : Fin Tag.F4.rank → ZMod p) :
    frameDiag (τ := Tag.F4) ζ hζ s ∈
      twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr := by
  have hζprim : IsPrimitiveRoot ζ p := hζo ▸ IsPrimitiveRoot.orderOf ζ
  rw [twistedTorus_eq_map_fixedCharTuples]
  refine Subgroup.mem_map.2
    ⟨TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 p s), ?_, ?_⟩
  · have hzv : TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 p s) =
        expTuple ζ (frameCoord Tag.F4 p s) := by
      funext i
      rw [TableBExc.E6Three.zetaVec_apply]
      rfl
    rw [hzv]
    refine (expTuple_mem_fixedCharTuples_iff hζprim
      (weylMatrix (τ := Tag.F4) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)
      Fr hFr (frameCoord Tag.F4 p s)).2 ?_
    rw [hmod, hq, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mulVec,
      Matrix.one_mulVec]
    simp
  · rfl

private theorem exists_conj_langTorus_F4_neg
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    (hpq : p ∣ Nat.card K + 1) {E : Subgroup (adjointGroup .F4 K)}
    (hE : IsElemAbelian p E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL .F4 (AlgebraicClosure K))
      (c : adjointGroup .F4 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∧
      ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) ∈
        (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
          CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
          (MulAut.conj g0).toMonoidHom := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_conj_into_langTorus_F4_neg
      K (Fact.out : p.Prime) hp5 hpq
  obtain ⟨c, hc⟩ := hconj E hE.2
  exact ⟨Fr, g0, c, hFr, hg0C, hg0, hc⟩

private theorem exists_rebased_langConj_F4_neg
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    (hpq : p ∣ Nat.card K + 1) {E : Subgroup (adjointGroup .F4 K)}
    (hE : IsElemAbelian p E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g1 : ModGL .F4 (AlgebraicClosure K)),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g1 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g1 = g1 * canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∧
      ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
        (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
          CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
          (MulAut.conj g1).toMonoidHom := by
  obtain ⟨Fr, g0, c, hFr, hg0C, hg0, hconj⟩ :=
    exists_conj_langTorus_F4_neg (p := p) hp5 hpq hE
  let ic : ModGL .F4 (AlgebraicClosure K) := baseChangeGL (algebraMap K (AlgebraicClosure K))
    ((c : adjointGroup .F4 K) : ModGL .F4 K)
  have hicC : ic ∈ adjointGroup .F4 (AlgebraicClosure K) :=
    CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup _ c.2
  have hicFr : Units.map (entrywiseHom Fr) ic = ic :=
    frobenius_baseChangeGL_F4Frame hFr ((c : adjointGroup .F4 K) : ModGL .F4 K)
  have hg1 : Units.map (entrywiseHom Fr) (ic⁻¹ * g0) = ic⁻¹ * g0 *
      canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg := by
    rw [map_mul, map_inv, hicFr, hg0]
    group
  refine ⟨Fr, ic⁻¹ * g0, hFr, mul_mem (inv_mem hicC) hg0C, hg1, fun x hx => ?_⟩
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (hconj x hx)
  change g0 * t * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
    ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) at htx
  have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup .F4 K) : ModGL .F4 K) =
      ic * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * ic⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    rfl
  refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
  change (ic⁻¹ * g0) * t * (ic⁻¹ * g0)⁻¹ =
    baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K)
  rw [hbc] at htx
  calc (ic⁻¹ * g0) * t * (ic⁻¹ * g0)⁻¹
      = ic⁻¹ * (g0 * t * g0⁻¹) * ic := by group
    _ = ic⁻¹ * (ic * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x : adjointGroup .F4 K) : ModGL .F4 K) * ic⁻¹) * ic := by rw [htx]
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x : adjointGroup .F4 K) : ModGL .F4 K) := by group

private theorem pTorsion_mem_pow_F4_neg
    {p : ℕ} {K : Type} [Field K]
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
        (MulAut.conj g0).toMonoidHom) (x : E) :
    (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0) ∈
      twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr ∧
    (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0) ^ p = 1 := by
  obtain ⟨t, ht, htx⟩ := Subgroup.mem_map.1 (hEin x x.2)
  change g0 * t * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
    ((x : adjointGroup .F4 K) : ModGL .F4 K) at htx
  have hmem : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 ∈
      twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr := by
    rw [← htx]
    have : g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t := by group
    rw [this]
    exact ht
  have hpow : (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0) ^ p = 1 := by
    have h1 : ((x : adjointGroup .F4 K) : ModGL .F4 K) ^ p = 1 :=
      congrArg Subtype.val (hE.2 x x.2)
    have := conj_pow (a := g0⁻¹) (b := baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K)) (i := p)
    rw [inv_inv] at this
    rw [this, ← map_pow, h1, map_one]
    group
  exact ⟨hmem, hpow⟩

private theorem pTorsion_injective_F4_neg
    {K : Type} [Field K] {E : Subgroup (adjointGroup .F4 K)}
    {g0 : ModGL .F4 (AlgebraicClosure K)} {x y : E}
    (h : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((y : adjointGroup .F4 K) : ModGL .F4 K) * g0) : x = y := by
  have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((y : adjointGroup .F4 K) : ModGL .F4 K) :=
    mul_left_cancel (mul_right_cancel h)
  exact Subtype.ext (Subtype.ext (baseChangeGL_injective _ h2))

private theorem pTorsion_centralizes_F4_neg
    {K : Type} [Field K]
    {E : Subgroup (adjointGroup .F4 K)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
        (MulAut.conj g0).toMonoidHom)
    {t : ModGL .F4 (AlgebraicClosure K)}
    (ht : t ∈ twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr)
    {c : ModGL .F4 K}
    (hc : baseChangeGL (algebraMap K (AlgebraicClosure K)) c = g0 * t * g0⁻¹) :
    ∀ x ∈ E, (x : ModGL .F4 K) * c = c * (x : ModGL .F4 K) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (hEin x hx)
  change g0 * s * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
    (x : ModGL .F4 K) at hsx
  have hts : s * t = t * s := by
    have hcomm := (isMulCommutative_twistedTorus (L := AlgebraicClosure K)
      f4Neg Fr).is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩
    exact congrArg Subtype.val hcomm
  have h3 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .F4 K) *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) c =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) c *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .F4 K) := by
    rw [hc, ← hsx]
    calc g0 * s * g0⁻¹ * (g0 * t * g0⁻¹) = g0 * (s * t) * g0⁻¹ := by group
      _ = g0 * (t * s) * g0⁻¹ := by rw [hts]
      _ = g0 * t * g0⁻¹ * (g0 * s * g0⁻¹) := by group
  exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by
    rw [map_mul, map_mul]
    exact h3)

private theorem pTorsion_surjective_F4_neg
    {p : ℕ} {K : Type} [Field K] [Finite K]
    {E : Subgroup (adjointGroup .F4 K)}
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
      (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
        (MulAut.conj g0).toMonoidHom)
    {t : ModGL .F4 (AlgebraicClosure K)}
    (ht : t ∈ twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr) (htp : t ^ p = 1) :
    ∃ x : E, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 = t := by
  have htC : t ∈ adjointGroup .F4 (AlgebraicClosure K) :=
    twistedTorusOf_le_adjointGroup _ _ ht
  have hyC : g0 * t * g0⁻¹ ∈ adjointGroup .F4 (AlgebraicClosure K) :=
    mul_mem (mul_mem hg0C htC) (inv_mem hg0C)
  have hyp : (g0 * t * g0⁻¹) ^ p = 1 := by
    rw [conj_pow, htp]
    group
  have hyΦ : Units.map (entrywiseHom Fr) (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
    have ht2 : canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg *
        Units.map (entrywiseHom Fr) t *
        (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
          CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)⁻¹ = t :=
      (mem_twistedTorus.1 ht).2
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
          CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg *
          Units.map (entrywiseHom Fr) t *
          (g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
            CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)⁻¹
        = g0 * (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
            CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg *
            Units.map (entrywiseHom Fr) t *
            (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
              CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)⁻¹) * g0⁻¹ := by group
      _ = g0 * t * g0⁻¹ := by rw [ht2]
  obtain ⟨c, hcC, hc⟩ := Subgroup.mem_map.1
    (mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr hyC hyΦ)
  let c₀ : adjointGroup .F4 K := ⟨c, hcC⟩
  have hcomm : ∀ x ∈ E, (x : ModGL .F4 K) * c = c * (x : ModGL .F4 K) :=
    pTorsion_centralizes_F4_neg hEin ht hc
  have hcE : c₀ ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (hcomm x hx)
  have hcp : c₀ ^ p = 1 := by
    refine Subtype.ext ?_
    show c ^ p = 1
    refine baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) ?_
    rw [map_pow, hc, hyp, map_one]
  have hcEmem : c₀ ∈ E := hSC c₀ hcE hcp
  refine ⟨⟨c₀, hcEmem⟩, ?_⟩
  change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) c * g0 = t
  rw [hc]
  group

private theorem exists_equiv_pTorsion_F4_neg
    {p : ℕ} {K : Type} [Field K] [Finite K]
    {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
      (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem .F4) (AlgebraicClosure K)
        CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr).map
        (MulAut.conj g0).toMonoidHom) :
    ∃ e : E ≃ f4LangTorsion K Fr p,
      ∀ x : E, (e x : ModGL .F4 (AlgebraicClosure K)) =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0 := by
  classical
  let f : E → f4LangTorsion K Fr p := fun x =>
    ⟨g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0,
      (pTorsion_mem_pow_F4_neg hE hEin x).1,
      (pTorsion_mem_pow_F4_neg hE hEin x).2⟩
  have hinj : Function.Injective f := fun x y hxy =>
    pTorsion_injective_F4_neg (congrArg Subtype.val hxy)
  have hsurj : Function.Surjective f := by
    rintro ⟨t, ht, htp⟩
    obtain ⟨x, hx⟩ := pTorsion_surjective_F4_neg hSC hFr hg0C hg0 hEin ht htp
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun x => rfl⟩

private theorem exists_equiv_frameDiag_F4_neg
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {ζ : (AlgebraicClosure K)ˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod p))
    (hframe_mem : ∀ s : Fin Tag.F4.rank → ZMod p,
      frameDiag ζ hζ s ∈ twistedTorus (canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr) :
    ∃ e : (Fin Tag.F4.rank → ZMod p) ≃ f4LangTorsion K Fr p,
      ∀ s, (e s : ModGL .F4 (AlgebraicClosure K)) = frameDiag ζ hζ s := by
  classical
  let g : (Fin Tag.F4.rank → ZMod p) → f4LangTorsion K Fr p := fun s =>
    ⟨frameDiag ζ hζ s, hframe_mem s, frameDiag_pow ζ hζ s⟩
  have ginj : Function.Injective g := by
    intro s t h
    exact frameDiag_injective hζo hζ hdet (congrArg Subtype.val h)
  have gsurj : Function.Surjective g := by
    rintro ⟨x, hx, hxp⟩
    obtain ⟨a, -, hap, hxa⟩ := exists_tuple_of_mem_twistedTorus f4Neg Fr hx hxp
    obtain ⟨s, hs⟩ := exists_frameDiag_eq hζo hζ hdet (funext hap)
    exact ⟨s, Subtype.ext (hs.trans hxa)⟩
  exact ⟨Equiv.ofBijective g ⟨ginj, gsurj⟩, fun s => rfl⟩

private theorem frame_e0_mul_F4_neg
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    {E : Subgroup (adjointGroup .F4 K)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    {eE : E ≃ f4LangTorsion K Fr p}
    {eT : (Fin Tag.F4.rank → ZMod p) ≃ f4LangTorsion K Fr p}
    (heE : ∀ x : E, (eE x : ModGL .F4 (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0)
    (heT : ∀ s, (eT s : ModGL .F4 (AlgebraicClosure K)) = frameDiag ζ hζ s) :
    ∀ a b : Multiplicative (Fin Tag.F4.rank → ZMod p),
      eE.symm (eT (Multiplicative.toAdd (a * b))) =
        eE.symm (eT (Multiplicative.toAdd a)) *
          eE.symm (eT (Multiplicative.toAdd b)) := by
  have hx : ∀ m : Multiplicative (Fin Tag.F4.rank → ZMod p),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((eE.symm (eT (Multiplicative.toAdd m)) : E) : ModGL .F4 K) * g0 =
      frameDiag ζ hζ (Multiplicative.toAdd m) := by
    intro m
    rw [← heE, eE.apply_symm_apply, heT]
  intro a b
  rw [show Multiplicative.toAdd (a * b) =
    Multiplicative.toAdd a + Multiplicative.toAdd b from rfl]
  apply eE.injective
  rw [eE.apply_symm_apply]
  show eT (Multiplicative.toAdd a + Multiplicative.toAdd b) =
    eE (eE.symm (eT (Multiplicative.toAdd a)) * eE.symm (eT (Multiplicative.toAdd b)))
  apply Subtype.ext
  rw [heT, heE, frameDiag_add, ← hx a, ← hx b]
  simp only [Subgroup.coe_mul, map_mul]
  group

private theorem exists_frameMulEquiv_F4_neg
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    {E : Subgroup (adjointGroup .F4 K)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    {eE : E ≃ f4LangTorsion K Fr p}
    {eT : (Fin Tag.F4.rank → ZMod p) ≃ f4LangTorsion K Fr p}
    (heE : ∀ x : E, (eE x : ModGL .F4 (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0)
    (heT : ∀ s, (eT s : ModGL .F4 (AlgebraicClosure K)) = frameDiag ζ hζ s) :
    ∃ e0Equiv : Multiplicative (Fin Tag.F4.rank → ZMod p) ≃* E,
      ∀ s : Fin Tag.F4.rank → ZMod p,
        (e0Equiv (Multiplicative.ofAdd s) : E) = eE.symm (eT s) := by
  classical
  let e0 : Multiplicative (Fin Tag.F4.rank → ZMod p) → E :=
    fun m => eE.symm (eT (Multiplicative.toAdd m))
  have e0_one : e0 1 = 1 := by
    show eE.symm (eT (Multiplicative.toAdd
      (1 : Multiplicative (Fin Tag.F4.rank → ZMod p)))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin Tag.F4.rank → ZMod p)) = 0 from rfl]
    rw [Equiv.symm_apply_eq]
    show eT 0 = eE 1
    apply Subtype.ext
    rw [heT, heE, frameDiag_zero]
    simp only [Subgroup.coe_one, map_one, inv_one, mul_one]
    group
  have e0_mul : ∀ a b : Multiplicative (Fin Tag.F4.rank → ZMod p),
      e0 (a * b) = e0 a * e0 b := frame_e0_mul_F4_neg heE heT
  let e0Hom : Multiplicative (Fin Tag.F4.rank → ZMod p) →* E :=
    { toFun := e0, map_one' := e0_one, map_mul' := e0_mul }
  have e0Hom_bij : Function.Bijective e0Hom := by
    constructor
    · intro a b hab
      have h1 : eT (Multiplicative.toAdd a) = eT (Multiplicative.toAdd b) := by
        have h2 := congrArg eE hab
        simpa [e0Hom, e0, eE.apply_symm_apply] using h2
      exact Multiplicative.toAdd.injective (eT.injective h1)
    · intro y
      refine ⟨Multiplicative.ofAdd (eT.symm (eE y)), ?_⟩
      show eE.symm (eT (Multiplicative.toAdd
        (Multiplicative.ofAdd (eT.symm (eE y))))) = y
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (eT.symm (eE y))) =
        eT.symm (eE y) from rfl]
      rw [eT.apply_symm_apply, eE.symm_apply_apply]
  exact ⟨MulEquiv.ofBijective e0Hom e0Hom_bij, fun s => rfl⟩

private theorem exists_frameHom_F4_neg
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    {E : Subgroup (adjointGroup .F4 K)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {ζ : (AlgebraicClosure K)ˣ} {hζ : ζ ^ p = 1}
    {g0 : ModGL .F4 (AlgebraicClosure K)}
    {eE : E ≃ f4LangTorsion K Fr p}
    {eT : (Fin Tag.F4.rank → ZMod p) ≃ f4LangTorsion K Fr p}
    (heE : ∀ x : E, (eE x : ModGL .F4 (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup .F4 K) : ModGL .F4 K) * g0)
    (heT : ∀ s, (eT s : ModGL .F4 (AlgebraicClosure K)) = frameDiag ζ hζ s) :
    ∃ ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K,
      Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * frameDiag ζ hζ s * g0⁻¹ := by
  classical
  obtain ⟨e0Equiv, he0⟩ := exists_frameMulEquiv_F4_neg heE heT
  let ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K :=
    E.subtype.comp e0Equiv.toMonoidHom
  have hιinj : Function.Injective ι₀ :=
    (Subgroup.subtype_injective E).comp e0Equiv.injective
  have hιrange : ι₀.range = E := by
    rw [show ι₀ = E.subtype.comp e0Equiv.toMonoidHom from rfl, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e0Equiv.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  refine ⟨ι₀, hιinj, hιrange, fun s => ?_⟩
  have hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((eE.symm (eT s) : E) : ModGL .F4 K) * g0 = frameDiag ζ hζ s := by
    rw [← heE, eE.apply_symm_apply, heT]
  have hι0 : ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
      ((eE.symm (eT s) : E) : ModGL .F4 K) := by
    change ((e0Equiv (Multiplicative.ofAdd s) : E) : ModGL .F4 K) = _
    rw [he0 s]
  rw [hι0, ← hx]
  group

theorem exists_langFrame_F4_of_sc
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Field K] [Finite K]
    (hpq : p ∣ Nat.card K + 1) {E : Subgroup (adjointGroup .F4 K)} (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup .F4 K)), x ^ p = 1 → x ∈ E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL .F4 (AlgebraicClosure K))
      (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod p) →* adjointGroup .F4 K),
      (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup .F4 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg ∧
      orderOf ζ = p ∧ Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ s : Fin Tag.F4.rank → ZMod p,
        baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((ι₀ (Multiplicative.ofAdd s) : adjointGroup .F4 K) : ModGL .F4 K) =
          g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹ := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Fr, g1, hFr, hg1C, hg1, hEin⟩ :=
    exists_rebased_langConj_F4_neg (p := p) hp5 hpq hE
  have hmod := modMat_weylMatrix_f4Neg_eq_neg_one_F4Frame (p := p)
  have hq : ((Nat.card K : ℕ) : ZMod p) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod p) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (p := p) hp2
  obtain ⟨ζ, hζo, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_orderOf_eq_of_dvd_add_one
      K (L := AlgebraicClosure K) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hframe_mem : ∀ s : Fin Tag.F4.rank → ZMod p,
      frameDiag ζ hζ s ∈ twistedTorus (canonicalRep (coxeterSystem .F4)
        (AlgebraicClosure K) CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) Fr :=
    fun s => frameDiag_mem_twistedTorus_F4_neg hFr hζo hζ hmod hq s
  obtain ⟨eE, heE⟩ := exists_equiv_pTorsion_F4_neg hE hSC hFr hg1C hg1 hEin
  obtain ⟨eT, heT⟩ := exists_equiv_frameDiag_F4_neg hζo hζ hdet hframe_mem
  obtain ⟨ι₀, hιinj, hιrange, hιeq⟩ :=
    exists_frameHom_F4_neg (ζ := ζ) (hζ := hζ) (g0 := g1) (eE := eE) (eT := eT) heE heT
  exact ⟨Fr, g1, ζ, hζ, ι₀, hFr, hg1C, hg1, hζo, hιinj, hιrange, hιeq⟩

end CFSG.StandardType

end
