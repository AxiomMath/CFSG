module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Aut
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.ClassicalGroups.Orthogonal.OddOrder
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplitSp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open scoped Matrix

private lemma rckLiftHom_rho_mul_POmegaMinus {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (hε : IsIdempotentElem ε) {x y : Matrix ι ι F}
    (hx : x * ε = ε * x) (hy : y * ε = ε * y) :
    (x * ε + (1 - ε)) * (y * ε + (1 - ε)) = (x * y) * ε + (1 - ε) := by
  have hε' : ε * ε = ε := hε.eq
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε']
    abel
  have hx0 : x * ε * (1 - ε) = 0 := by
    rw [mul_assoc, hε.mul_one_sub_self, mul_zero]
  have hy0 : (1 - ε) * (y * ε) = 0 := by
    rw [hy, ← mul_assoc, hε.one_sub_mul_self, zero_mul]
  calc
    (x * ε + (1 - ε)) * (y * ε + (1 - ε))
        = x * ε * (y * ε) + x * ε * (1 - ε) + (1 - ε) * (y * ε) +
            (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * ε * (y * ε) + (1 - ε) * (1 - ε) := by simp [hx0, hy0]
    _ = x * (ε * y) * ε + (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * (y * ε) * ε + (1 - ε) * (1 - ε) := by rw [hy]
    _ = x * y * ε + (1 - ε) := by
      rw [mul_assoc x (y * ε) ε, mul_assoc y ε ε, hε', ← mul_assoc x y ε, h1]

private lemma rckLiftHom_s₁_mul_POmegaMinus {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {B : Type} [Group B] {s' s₁ : B → GL ι F} {ε : Matrix ι ι F}
    (hform : ∀ b : B, ((s₁ b : GL ι F) : Matrix ι ι F) =
      ((s' b : GL ι F) : Matrix ι ι F) * ε + (1 - ε))
    (hε : IsIdempotentElem ε)
    (hεcomm : ∀ b : B, ((s' b : GL ι F) : Matrix ι ι F) * ε =
      ε * ((s' b : GL ι F) : Matrix ι ι F))
    (hs'_mul : ∀ b b' : B, s' (b * b') = s' b * s' b') :
    ∀ b b' : B, s₁ (b * b') = s₁ b * s₁ b' := by
  intro b b'
  apply Units.ext
  rw [Units.val_mul, hform (b * b'), hform b, hform b', hs'_mul b b']
  exact (rckLiftHom_rho_mul_POmegaMinus hε (hεcomm b) (hεcomm b')).symm

private lemma rckLiftHom_isUnit_det_polarGram_POmegaMinus {n : ℕ} {F : Type} [Field F]
    [Finite F] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) :
    IsUnit (LinearMap.toMatrix₂' F
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).det := by
  have h1 : (LinearMap.toMatrix₂' F
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) =
      LinearMap.BilinForm.toMatrix'
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr
      (Spin.nondegenerate_polarBilin_quadMinus_of_finite n F hirr)))

private lemma rckLiftHom_polar_eq_dot_POmegaMinus {n : ℕ} {F : Type} [Field F] {bq cq : F}
    (x y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :
    QuadraticMap.polar (Spin.quadMinus n F bq cq) x y =
      dotProduct x ((LinearMap.toMatrix₂' F
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) =
      LinearMap.BilinForm.toMatrix'
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix'
      (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma rckLiftHom_quad_add_POmegaMinus {n : ℕ} {F : Type} [Field F] {bq cq : F}
    (u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) :
    Spin.quadMinus n F bq cq (u + v) =
      Spin.quadMinus n F bq cq u + Spin.quadMinus n F bq cq v +
        dotProduct u ((LinearMap.toMatrix₂' F
          (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq))).mulVec v) := by
  rw [QuadraticMap.map_add (Spin.quadMinus n F bq cq) u v,
    rckLiftHom_polar_eq_dot_POmegaMinus (n := n) (bq := bq) (cq := cq) u v]

private lemma rckLiftHom_block_mem_omega_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {p : ℕ}
    (hp : Odd p) {s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hQ₁ : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      Spin.quadMinus n F bq cq
        (((s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
        Spin.quadMinus n F bq cq v)
    (hpow : s₁ ^ p = 1) :
    s₁ ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range := by
  obtain ⟨hQnd, hT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := F) (n := n) (b := bq) (c := cq)
      hn hirr
  have hsq : s₁ ^ 2 ∈ CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq) :=
    CFSG.ComponentClassification.RankTwoClassical.sq_mem_statedOmega
      (Spin.quadMinus n F bq cq) hQnd hT hQ₁
  have hmem : s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq) :=
    CFSG.ClassicalGroups.Orthogonal.mem_of_odd_pow_of_sq_mem
      (N := CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq)) (g := s₁)
      (fun x hx => hx ▸ hsq) hp hpow
  have hrange : (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range =
      CFSG.Open.StatedOmega ⇑(Spin.quadMinus n F bq cq) :=
    CFSG.StandardType.AutOm.range_spinMatrix_minus (K := F) (b := bq) (c := cq) hn hirr
  rwa [hrange]

private lemma rckLiftHom_exists_blockRestrict_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)}
    (hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v)
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F
        (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    {p : ℕ} (hp : Odd p) (s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)
    (hs'Q : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      Spin.quadMinus n F bq cq
        (((s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
        Spin.quadMinus n F bq cq v)
    (hs'p : s' ^ p = 1)
    (hcomm_s' : ∀ u ∈ S, Commute s' u) :
    ∃ s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      ((s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε =
        ε * ((s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ∧
      ((s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        ((s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * ε + (1 - ε) ∧
      s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) ∧
      s₁ ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range ∧
      (∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
        s' * g * s'⁻¹ = s₁ * g * s₁⁻¹) := by
  obtain ⟨hεcomm, s₁, hform, hmem, hord, hconj⟩ :=
    rckGLBlock_restrict hS hε.1 hε.2.1 s' hcomm_s'
  have hpow : s₁ ^ p = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord.trans (orderOf_dvd_iff_pow_eq_one.mpr hs'p))
  have hQ₁ : ∀ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F,
      Spin.quadMinus n F bq cq
        (((s₁ : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
          Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
            (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
        Spin.quadMinus n F bq cq v :=
    rckGLBlock_restrict_quad (rckLiftHom_isUnit_det_polarGram_POmegaMinus hirr)
      hε.2.2.2.1 hε.2.1 (rckLiftHom_quad_add_POmegaMinus (n := n) (bq := bq) (cq := cq))
      hs'Q hεcomm hform
  exact ⟨s₁, hεcomm, hform, hmem,
    rckLiftHom_block_mem_omega_POmegaMinus hirr hn hp hQ₁ hpow, hconj⟩

private lemma rckLiftHom_exists_sb_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {X : Type} [Group X] {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {s : spinGroup (Spin.quadMinus n F bq cq)} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ sb : ↥B → spinGroup (Spin.quadMinus n F bq cq),
      (∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
        ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) ∧
      (∀ b : ↥B, Commute (sb b) s) := by
  let sb : ↥B → spinGroup (Spin.quadMinus n F bq cq) := fun b =>
    Classical.choose
      (exists_conj_eq_POmegaMinus n hirr hn ψ hker (hBID b b.2))
  have hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹) := fun b u =>
    Classical.choose_spec
      (exists_conj_eq_POmegaMinus n hirr hn ψ hker (hBID b b.2)) u
  refine ⟨sb, hsb_spec, fun b => ?_⟩
  exact conj_eq_commute_POmegaMinus n hirr hn ψ hker (hBe b b.2) (hsb_spec b) hs

private lemma rckLiftHom_sb_inv_mul_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {X : Type} [Group X] {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadMinus n F bq cq)}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) :
    ∀ b b' : ↥B,
      ((sb (b * b'))⁻¹ : spinGroup (Spin.quadMinus n F bq cq)) =
        (sb b)⁻¹ * (sb b')⁻¹ := by
  intro b b'
  have hanti : sb (b * b') = sb b' * sb b := by
    refine conj_eq_unique_POmegaMinus n hirr hn ψ hker ?_
    intro u
    rw [← hsb_spec (b * b') u]
    calc ((b * b' : ↥B) : X)⁻¹ * ψ u * ((b * b' : ↥B) : X)
        = (b' : X)⁻¹ * ((b : X)⁻¹ * ψ u * (b : X)) * (b' : X) := by
          simp only [Subgroup.coe_mul]
          group
      _ = (b' : X)⁻¹ * ψ (sb b * u * (sb b)⁻¹) * (b' : X) := by rw [hsb_spec b u]
      _ = ψ (sb b' * (sb b * u * (sb b)⁻¹) * (sb b')⁻¹) := by
          rw [hsb_spec b' (sb b * u * (sb b)⁻¹)]
      _ = ψ ((sb b' * sb b) * u * (sb b' * sb b)⁻¹) := by
          congr 1
          group
  rw [hanti, mul_inv_rev]

private lemma rckLiftHom_conj_lift_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadMinus n F bq cq)}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    (b : ↥B) (y : spinGroup (Spin.quadMinus n F bq cq)) :
    (b : X) * ψ y * (b : X)⁻¹ = ψ ((sb b)⁻¹ * y * (sb b)) := by
  have h := hsb_spec b ((sb b)⁻¹ * y * (sb b))
  have h' : (b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X) = ψ y := by
    rw [h, show sb b * ((sb b)⁻¹ * y * (sb b)) * (sb b)⁻¹ = y by group]
  calc (b : X) * ψ y * (b : X)⁻¹
      = (b : X) * ((b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X)) *
          (b : X)⁻¹ := by rw [← h']
    _ = ψ ((sb b)⁻¹ * y * (sb b)) := by group

private lemma rckLiftHom_exists_s'_data_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {X : Type} [Group X] {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {s : spinGroup (Spin.quadMinus n F bq cq)} {B : Subgroup X}
    {sb : ↥B → spinGroup (Spin.quadMinus n F bq cq)} {p : ℕ}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    (hcomm_s : ∀ b : ↥B, Commute (sb b) s) (hsb_pow : ∀ b : ↥B, sb b ^ p = 1) :
    ∃ s' : ↥B → GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      (∀ b : ↥B,
        s' b = Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹)) ∧
      (∀ (b : ↥B) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F),
        Spin.quadMinus n F bq cq
          (((s' b : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
            Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v) =
          Spin.quadMinus n F bq cq v) ∧
      (∀ b : ↥B, s' b ^ p = 1) ∧
      (∀ (b : ↥B) (u : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F),
        u ∈ ({Spin.spinMatrix (Spin.quadMinus n F bq cq) s} :
          Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) → Commute (s' b) u) ∧
      (∀ b b' : ↥B, s' (b * b') = s' b * s' b') := by
  let s' : ↥B → GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F := fun b =>
    Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹)
  have hs'def : ∀ b : ↥B,
      s' b = Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹) := fun _ => rfl
  refine ⟨s', hs'def, ?_, ?_, ?_, ?_⟩
  · intro b v
    exact Spin.spinMatrix_mem (Spin.quadMinus n F bq cq) ((sb b)⁻¹) v
  · intro b
    have hj : (Spin.spinMatrix (Spin.quadMinus n F bq cq) (sb b)) ^ p = 1 := by
      rw [← map_pow, hsb_pow b, map_one]
    rw [hs'def b, map_inv, inv_pow, hj, inv_one]
  · intro b u hu
    rw [Set.mem_singleton_iff] at hu
    subst u
    have hci := ((hcomm_s b).map (Spin.spinMatrix (Spin.quadMinus n F bq cq))).inv_left
    simpa [s', map_inv] using hci
  · intro b b'
    rw [hs'def (b * b'), hs'def b, hs'def b',
      rckLiftHom_sb_inv_mul_POmegaMinus hirr hn hker hsb_spec b b', map_mul]

private lemma rckLiftHom_blockAction_POmegaMinus {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadMinus n F bq cq) →* X}
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadMinus n F bq cq)}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadMinus n F bq cq)),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    {S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)}
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    {s' s₁ : ↥B → GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    {t₁ : ↥B → spinGroup (Spin.quadMinus n F bq cq)}
    (hs'def : ∀ b : ↥B,
      s' b = Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹))
    (hconj : ∀ b : ↥B, ∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
      s' b * g * (s' b)⁻¹ = s₁ b * g * (s₁ b)⁻¹)
    (ht₁j : ∀ b : ↥B, Spin.spinMatrix (Spin.quadMinus n F bq cq) (t₁ b) = s₁ b) :
    ∀ (b : ↥B) (y : spinGroup (Spin.quadMinus n F bq cq)),
      y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε →
      (b : X) * ψ y * (b : X)⁻¹ = ψ (t₁ b * y * (t₁ b)⁻¹) := by
  intro b y hy
  have hyGL : Spin.spinMatrix (Spin.quadMinus n F bq cq) y ∈
      Subgroup.centralizer S ⊓ glFixing (1 - ε) := by
    have h : y ∈ (Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap
        (Spin.spinMatrix (Spin.quadMinus n F bq cq)) := by
      simpa [glBlockCentralizer] using hy
    exact Subgroup.mem_comap.mp h
  have hconj_y := hconj b (Spin.spinMatrix (Spin.quadMinus n F bq cq) y) hyGL
  have hmat : Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹ * y * (sb b)) =
      Spin.spinMatrix (Spin.quadMinus n F bq cq) (t₁ b * y * (t₁ b)⁻¹) := by
    calc Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹ * y * (sb b))
        = Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹) *
            Spin.spinMatrix (Spin.quadMinus n F bq cq) y *
            (Spin.spinMatrix (Spin.quadMinus n F bq cq) ((sb b)⁻¹))⁻¹ := by
          rw [map_mul, map_mul, map_inv, inv_inv]
      _ = s' b * Spin.spinMatrix (Spin.quadMinus n F bq cq) y * (s' b)⁻¹ := by
          rw [hs'def b]
      _ = s₁ b * Spin.spinMatrix (Spin.quadMinus n F bq cq) y * (s₁ b)⁻¹ := hconj_y
      _ = Spin.spinMatrix (Spin.quadMinus n F bq cq) (t₁ b * y * (t₁ b)⁻¹) := by
          rw [map_mul, map_mul, map_inv, ht₁j b]
  rw [rckLiftHom_conj_lift_POmegaMinus hsb_spec b y]
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  rw [hinj hmat]

theorem exists_rckRestrictLiftHom_POmegaMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) {X : Type} [Group X]
    {ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X}
    (hker : ψ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)))
    {s : ↥(spinGroup (Spin.quadMinus n F bq cq))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε)
    {p : ℕ} (hp : Odd p) {B : Subgroup X} (hBp : ∀ b ∈ B, b ^ p = 1)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ β : ↥B →* ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
        {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε),
      ∀ (b : ↥B) (y : ↥(spinGroup (Spin.quadMinus n F bq cq))),
        y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
          {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε →
        (b : X) * ψ y * (b : X)⁻¹ =
          ψ ((β b : ↥(spinGroup (Spin.quadMinus n F bq cq))) * y *
            (β b : ↥(spinGroup (Spin.quadMinus n F bq cq)))⁻¹) := by
  let S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    {Spin.spinMatrix (Spin.quadMinus n F bq cq) s}
  have hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    exact Commute.refl _
  obtain ⟨sb, hsb_spec, hcomm_s⟩ :=
    rckLiftHom_exists_sb_POmegaMinus hirr hn hker hs hBN hBID hBe
  have hsb_pow : ∀ b : ↥B, sb b ^ p = 1 := fun b =>
    spin_pow_eq_one_of_conj_POmegaMinus hirr hn ψ hker (hBp b b.2) (hsb_spec b)
  obtain ⟨s', hs'def, hs'Q, hs'p, hcomm_s', hs'_mul⟩ :=
    rckLiftHom_exists_s'_data_POmegaMinus hirr hn hker hsb_spec hcomm_s hsb_pow
  choose s₁ hεcomm hform hmem hrange hconj using fun b : ↥B =>
    rckLiftHom_exists_blockRestrict_POmegaMinus (S := S) hirr hn hS hε hp (s' b) (hs'Q b) (hs'p b)
      (hcomm_s' b)
  let t₁ : ↥B → spinGroup (Spin.quadMinus n F bq cq) := fun b =>
    Classical.choose (MonoidHom.mem_range.mp (hrange b))
  have ht₁j : ∀ b : ↥B,
      Spin.spinMatrix (Spin.quadMinus n F bq cq) (t₁ b) = s₁ b := fun b =>
    Classical.choose_spec (MonoidHom.mem_range.mp (hrange b))
  have ht₁mem : ∀ b : ↥B,
      t₁ b ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε := by
    intro b
    have h : t₁ b ∈ ((Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap
        (Spin.spinMatrix (Spin.quadMinus n F bq cq))) :=
      Subgroup.mem_comap.mpr (by rw [ht₁j b]; exact hmem b)
    simpa [glBlockCentralizer] using h
  let βfun : ↥B → ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S ε) :=
    fun b => ⟨t₁ b, ht₁mem b⟩
  have hs₁_mul : ∀ b b' : ↥B, s₁ (b * b') = s₁ b * s₁ b' :=
    rckLiftHom_s₁_mul_POmegaMinus hform hε.2.1 hεcomm hs'_mul
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hβmul : ∀ b b' : ↥B, βfun (b * b') = βfun b * βfun b' := by
    intro b b'
    have ht : t₁ (b * b') = t₁ b * t₁ b' :=
      hinj (by rw [ht₁j (b * b'), map_mul, ht₁j b, ht₁j b', hs₁_mul b b'])
    exact Subtype.ext ht
  refine ⟨MonoidHom.mk' βfun hβmul, ?_⟩
  intro b y hy
  simpa [βfun] using
    rckLiftHom_blockAction_POmegaMinus hirr hsb_spec hs'def hconj ht₁j b y hy

end CFSG.StandardType.RCKRP
