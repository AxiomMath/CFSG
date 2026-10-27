module

public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.Quasithin.Background.C41PfW
public import CFSG.Quasithin.Background.C126RFSurj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Cent
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellMult
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
public import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSingTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3
public import CFSG.Quasithin.H13.NQTermAmbientQuotient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourCover

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.RankThree.SteinbergR3ECAFieldFixedLayerQuotient
public import CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension
public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus
public import CFSG.LinearAlgebra.RootGroupSL.SLFacts
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.Quasithin.Background.C22PfC
public import CFSG.Quasithin.Background.C2PushH129
public import CFSG.Quasithin.Background.C41PfO
public import CFSG.Quasithin.Background.C41PfQ
public import CFSG.Quasithin.Background.E6TwentyThreeD
public import CFSG.Quasithin.Background.E6TwentyThreeE
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.EmptyFaithful.S152Y20
public import CFSG.Quasithin.EmptyFaithful.S152Y21
public import CFSG.Quasithin.EmptyFaithful.S153F18C
public import CFSG.Quasithin.EmptyFaithful.S153IClose
public import CFSG.Quasithin.EmptyFaithful.SBd3L3
public import CFSG.Quasithin.EmptyFaithful.SBd4B1
public import CFSG.Quasithin.EmptyFaithful.SBd5Label
public import CFSG.Quasithin.EmptyFaithful.SBd6Close
public import CFSG.Quasithin.Vol2.KGFactLem1211G2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Quasithin Subgroup
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.GLTheoremA.H81Orth
open Polynomial CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open scoped commutatorElement
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

private abbrev I3 : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

noncomputable def beta (t : Fˣ) (ht : t ^ 3 = 1) : StatedOmega (StatedQuadMinus 3 F b c) :=
  minusDiagGL (n := 3) (b := b) (c := c) (r := 3) (by decide) (Pi.mulSingle (0 : Fin (3 - 1)) t)
    (by
      intro j
      fin_cases j
      · simpa [Pi.mulSingle] using ht
      · simp [Pi.mulSingle])

private noncomputable def eGamma (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus 3 F b c) ≃* ↥(orthDerived (quadMinus 3 F b c)) :=
  (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).trans
    (MulEquiv.subgroupCongr (commutator_orthogonalGroup_quadMinus_of_two_le (n := 3) (by norm_num) hirr)).symm

private noncomputable def xbeta (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : Fˣ) (ht : t ^ 3 = 1) :
    ↥(orthDerived (quadMinus 3 F b c)) :=
  eGamma hirr (beta (b := b) (c := c) t ht)

private lemma coe_eGamma_apply (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (A : StatedOmega (StatedQuadMinus 3 F b c)) (v : I3 → F) :
    (((eGamma (b := b) (c := c) hirr A : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) v) = (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr A).app v := by
  rfl

private lemma orderOf_beta (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    orderOf (beta (b := b) (c := c) t ht) = 3 := by
  rw [beta, orderOf_minusDiagGL_mulSingle]
  exact hord

private lemma orderOf_xbeta (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    orderOf (xbeta (b := b) (c := c) hirr t ht) = 3 := by
  change orderOf (eGamma (b := b) (c := c) hirr (beta (b := b) (c := c) t ht)) = 3
  rw [MulEquiv.orderOf_eq, orderOf_beta t ht hord]

private lemma beta_coe (t : Fˣ) (ht : t ^ 3 = 1) :
    ((beta (b := b) (c := c) t ht : StatedOmega (StatedQuadMinus 3 F b c)) :
        GL I3 F) =
      diagGL (torusEntMinus (3 - 1) F (Pi.mulSingle (0 : Fin (3 - 1)) t)) := by
  rw [beta, coe_minusDiagGL]

private lemma beta_app (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : Fˣ) (ht : t ^ 3 = 1)
    (v : I3 → F) :
    (statedOmegaMinusEquiv (m := 3) (by norm_num) hirr (beta (b := b) (c := c) t ht)).app v =
      fun j => ((torusEntMinus (3 - 1) F (Pi.mulSingle (0 : Fin (3 - 1)) t) j : Fˣ) : F) * v j := by
  rw [statedOmegaMinusEquiv_app, beta_coe, coe_diagGL]
  funext j
  exact Matrix.mulVec_diagonal _ _ j

private lemma xbeta_app (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : Fˣ) (ht : t ^ 3 = 1)
    (v : I3 → F) :
    (((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) v) =
      fun j => ((torusEntMinus (3 - 1) F (Pi.mulSingle (0 : Fin (3 - 1)) t) j : Fˣ) : F) * v j := by
  rw [xbeta, coe_eGamma_apply]
  exact beta_app hirr t ht v

private abbrev vx : I3 → F := Pi.single (Sum.inl (0 : Fin (3 - 1))) 1
private abbrev vy : I3 → F := Pi.single (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) 1

private lemma xbeta_vx (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : Fˣ) (ht : t ^ 3 = 1) :
    (((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) vx) = t • vx := by
  rw [xbeta_app]
  funext j
  rcases j with i | i | k
  · fin_cases i
    · simp [vx, torusEntMinus, Pi.mulSingle, Units.smul_def]
    · simp [vx]
  · fin_cases i <;> simp [vx]
  · fin_cases k <;> simp [vx]

private lemma xbeta_vy (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (t : Fˣ) (ht : t ^ 3 = 1) :
    (((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) vy) = t⁻¹ • vy := by
  rw [xbeta_app]
  funext j
  rcases j with i | i | k
  · fin_cases i <;> simp [vy]
  · fin_cases i
    · simp [vy, torusEntMinus, Pi.mulSingle, Units.smul_def]
    · simp [vy]
  · fin_cases k <;> simp [vy]

private noncomputable def P : HypPair (quadMinus 3 F b c) :=
  minusPair (n := 3) F b c (⟨0, by norm_num⟩ : Fin (3 - 1))

private lemma P_e : (P (b := b) (c := c)).e = Pi.single (Sum.inl (0 : Fin (3 - 1))) 1 :=
  minusPair_e (n := 3) (K := F) (b := b) (c := c) (i := ⟨0, by norm_num⟩)

private lemma P_f : (P (b := b) (c := c)).f = Pi.single (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) 1 :=
  minusPair_f (n := 3) (K := F) (b := b) (c := c) (i := ⟨0, by norm_num⟩)

private lemma t_ne_one {t : Fˣ} (hord : orderOf t = 3) : t ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hord
  exact absurd hord (by norm_num)

private lemma t_inv_ne_one {t : Fˣ} (hord : orderOf t = 3) : t⁻¹ ≠ 1 := by
  intro h
  have h1 : t = 1 := by
    have := congrArg Inv.inv h
    simpa using this
  exact t_ne_one hord h1

private lemma t_ne_inv {t : Fˣ} (hord : orderOf t = 3) : t ≠ t⁻¹ := by
  intro h
  have h2 : t ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h]
    exact inv_mul_cancel t
  have hdvd2 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hdvd3 : orderOf t ∣ 3 := by rw [hord]
  have hdvd1 : orderOf t ∣ 1 := by
    have := Nat.dvd_gcd hdvd2 hdvd3
    simpa using this
  have hone : orderOf t = 1 := Nat.dvd_one.mp hdvd1
  exact t_ne_one hord (orderOf_eq_one_iff.mp hone)

private lemma fixedSpace_eq_Pperp (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    fixedSpace ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) = (P (b := b) (c := c)).perp := by
  ext v
  rw [mem_fixedSpace, HypPair.mem_perp]
  constructor
  · intro hv
    have hvy : v (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = 0 := by
      have h := congrFun hv (Sum.inr (Sum.inl (0 : Fin (3 - 1))))
      rw [xbeta_app] at h
      simp only [torusEntMinus, Pi.mulSingle] at h
      have h' : ((t⁻¹ : Fˣ) : F) * v (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) =
          v (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) := h
      have hne : ((t⁻¹ : Fˣ) : F) - 1 ≠ 0 := by
        have := t_inv_ne_one hord
        exact sub_ne_zero.mpr (by simpa using this)
      have h0 : (((t⁻¹ : Fˣ) : F) - 1) * v (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = 0 := by
        rw [sub_mul, one_mul, h', sub_self]
      exact (mul_eq_zero.mp h0).resolve_left hne
    have hvx : v (Sum.inl (0 : Fin (3 - 1))) = 0 := by
      have h := congrFun hv (Sum.inl (0 : Fin (3 - 1)))
      rw [xbeta_app] at h
      simp only [torusEntMinus, Pi.mulSingle] at h
      have h' : ((t : Fˣ) : F) * v (Sum.inl (0 : Fin (3 - 1))) =
          v (Sum.inl (0 : Fin (3 - 1))) := h
      have hne : ((t : Fˣ) : F) - 1 ≠ 0 := by
        have := t_ne_one hord
        exact sub_ne_zero.mpr (by simpa using this)
      have h0 : (((t : Fˣ) : F) - 1) * v (Sum.inl (0 : Fin (3 - 1))) = 0 := by
        rw [sub_mul, one_mul, h', sub_self]
      exact (mul_eq_zero.mp h0).resolve_left hne
    constructor
    · rw [P_e, polar_single_inl_quadMinus]
      exact hvy
    · rw [P_f, polar_single_inr_quadMinus]
      exact hvx
  · intro hv
    have hvy : v (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = 0 := by
      have h := hv.1
      rwa [P_e, polar_single_inl_quadMinus] at h
    have hvx : v (Sum.inl (0 : Fin (3 - 1))) = 0 := by
      have h := hv.2
      rwa [P_f, polar_single_inr_quadMinus] at h
    funext j
    rw [xbeta_app]
    rcases j with i | i | k
    · fin_cases i
      · simp [hvx]
      · simp [torusEntMinus, Pi.mulSingle]
    · fin_cases i
      · simp [hvy]
      · simp [torusEntMinus, Pi.mulSingle]
    · fin_cases k <;> simp [torusEntMinus]

private lemma X_sub_C_ne_X_sub_one {t : Fˣ} (hord : orderOf t = 3) :
    (X - C (t : F) : F[X]) ≠ X - 1 := by
  intro h
  have h1 : C (t : F) = C (1 : F) := sub_right_injective h
  have h2 : (t : F) = 1 := C_injective h1
  exact t_ne_one hord (Units.ext h2)

private lemma X_sub_C_inv_ne_X_sub_one {t : Fˣ} (hord : orderOf t = 3) :
    (X - C ((t⁻¹ : Fˣ) : F) : F[X]) ≠ X - 1 := by
  intro h
  have h1 : C ((t⁻¹ : Fˣ) : F) = C (1 : F) := sub_right_injective h
  have h2 : ((t⁻¹ : Fˣ) : F) = 1 := C_injective h1
  exact t_inv_ne_one hord (Units.ext h2)

private lemma vx_ne_zero : (vx : I3 → F) ≠ 0 := by
  intro h
  have h1 : vx (Sum.inl (0 : Fin (3 - 1))) = (1 : F) := by
    change (Pi.single (Sum.inl (0 : Fin (3 - 1))) (1 : F) : I3 → F)
      (Sum.inl (0 : Fin (3 - 1))) = 1
    simp
  rw [h] at h1
  exact zero_ne_one h1

private lemma vy_ne_zero : (vy : I3 → F) ≠ 0 := by
  intro h
  have h1 : vy (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = (1 : F) := by
    change (Pi.single (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) (1 : F) : I3 → F)
      (Sum.inr (Sum.inl (0 : Fin (3 - 1)))) = 1
    simp
  rw [h] at h1
  exact zero_ne_one h1

private lemma aeval_X_sub_C_apply (x : (I3 → F) ≃ₗ[F] (I3 → F)) (t : F) (v : I3 → F) :
    ((aeval x.toLinearMap) (X - C t)) v = x v - t • v := by
  simp [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply]

private lemma xbeta_vx_mem_others (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    vx ∈ othersSpace ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1) := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  change vx ∈ othersSpace x.toLinearMap (X - 1)
  have hxeq : x vx = t • vx := xbeta_vx hirr t ht
  have hzero : ((aeval x.toLinearMap) (X - C (t : F))) vx = 0 := by
    rw [aeval_X_sub_C_apply, hxeq]
    simp only [Units.smul_def]
    exact sub_self _
  have hdvd : (X - C (t : F)) ∣ minpoly F x.toLinearMap :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.dvd_minpoly_of_aeval_eq_zero
      x.toLinearMap (irreducible_X_sub_C (t : F)) vx_ne_zero hzero
  have hfact : (X - C (t : F)) ∈ primaryFactors x.toLinearMap :=
    mem_primaryFactors.mpr ⟨irreducible_X_sub_C (t : F), monic_X_sub_C (t : F), hdvd⟩
  have hcomp : vx ∈ primaryComponent x.toLinearMap (X - C (t : F)) :=
    mem_primaryComponent.mpr hzero
  have hne := X_sub_C_ne_X_sub_one (t := t) hord
  refine Submodule.mem_iSup_of_mem (X - C (t : F)) (Submodule.mem_iSup_of_mem ?_ hcomp)
  exact ⟨hfact, hne, by rw [reciprocalPolynomial_X_sub_one]; exact hne⟩

private lemma xbeta_vy_mem_others (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    vy ∈ othersSpace ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1) := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  change vy ∈ othersSpace x.toLinearMap (X - 1)
  have hxeq : x vy = t⁻¹ • vy := xbeta_vy hirr t ht
  have hzero : ((aeval x.toLinearMap) (X - C ((t⁻¹ : Fˣ) : F))) vy = 0 := by
    rw [aeval_X_sub_C_apply, hxeq]
    simp only [Units.smul_def]
    exact sub_self _
  have hdvd : (X - C ((t⁻¹ : Fˣ) : F)) ∣ minpoly F x.toLinearMap :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.dvd_minpoly_of_aeval_eq_zero
      x.toLinearMap (irreducible_X_sub_C ((t⁻¹ : Fˣ) : F)) vy_ne_zero hzero
  have hfact : (X - C ((t⁻¹ : Fˣ) : F)) ∈ primaryFactors x.toLinearMap :=
    mem_primaryFactors.mpr ⟨irreducible_X_sub_C ((t⁻¹ : Fˣ) : F),
      monic_X_sub_C ((t⁻¹ : Fˣ) : F), hdvd⟩
  have hcomp : vy ∈ primaryComponent x.toLinearMap (X - C ((t⁻¹ : Fˣ) : F)) :=
    mem_primaryComponent.mpr hzero
  have hne := X_sub_C_inv_ne_X_sub_one (t := t) hord
  refine Submodule.mem_iSup_of_mem (X - C ((t⁻¹ : Fˣ) : F)) (Submodule.mem_iSup_of_mem ?_ hcomp)
  exact ⟨hfact, hne, by rw [reciprocalPolynomial_X_sub_one]; exact hne⟩

private theorem hx_of (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    OddOrderIsometry (quadMinus 3 F b c) 3
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) :=
  oddOrderIsometry_of_orthDerived Nat.prime_three
    (by rw [ringChar.eq F 2]; norm_num)
    (isMinus_quadMinus (m := 3) (by norm_num) hirr).nondeg
    (xbeta (b := b) (c := c) hirr t ht) (orderOf_xbeta hirr t ht hord)

private lemma finrank_othersSpace (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    Module.finrank F ↥(othersSpace
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1)) = 2 := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  change Module.finrank F ↥(othersSpace x.toLinearMap (X - 1)) = 2
  have hx := hx_of (b := b) (c := c) hirr t ht hord
  have hcompl : IsCompl (fixedSpace x) (othersSpace x.toLinearMap (X - 1)) := by
    simpa [x] using hx.fixed_others.1
  have hV : Module.finrank F (I3 → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum]
    norm_num
  have hfix : Module.finrank F ↥(fixedSpace x) = 4 := by
    rw [fixedSpace_eq_Pperp hirr t ht hord]
    have hminus := isMinus_quadMinus (m := 3) (by norm_num) hirr
    have hperp := hminus.perp (P (b := b) (c := c))
    exact hperp.finrank_eq
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hfix, hV] at hadd
  omega

private theorem selfMemX (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) :
    ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) ∈
      isometryCentralizer (quadMinus 3 F b c)
        ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
          (I3 → F) ≃ₗ[F] (I3 → F)) :=
  Subgroup.mem_inf.mpr
    ⟨orthDerived_le_orthogonalGroup (xbeta (b := b) (c := c) hirr t ht).2,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

private lemma commute_restrictOthers_self_x (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1)
    {g : (I3 → F) ≃ₗ[F] (I3 → F)}
    (hg : g ∈ isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))) :
    Commute (restrictOthers (Q := quadMinus 3 F b c)
        (x := ((xbeta (b := b) (c := c) hirr t ht :
          ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F))) g hg)
      (restrictOthers (Q := quadMinus 3 F b c)
        (x := ((xbeta (b := b) (c := c) hirr t ht :
          ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)))
        ((xbeta (b := b) (c := c) hirr t ht :
          ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F))
        (selfMemX (b := b) (c := c) hirr t ht)) := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  have hc : g * ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) =
      ((xbeta (b := b) (c := c) hirr t ht :
        ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
  show g (((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) r) =
    ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) (g r)
  exact congrArg (fun f : (I3 → F) ≃ₗ[F] (I3 → F) => f r) hc

private lemma restrictOthers_x_ne_smul (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) (a : F) :
    restrictOthers (Q := quadMinus 3 F b c)
      (x := ((xbeta (b := b) (c := c) hirr t ht :
        ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)))
      ((xbeta (b := b) (c := c) hirr t ht :
        ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F))
      (selfMemX (b := b) (c := c) hirr t ht) ≠ a • 1 := by
  intro hc
  have hvx := xbeta_vx_mem_others (b := b) (c := c) hirr t ht hord
  have hvy := xbeta_vy_mem_others (b := b) (c := c) hirr t ht hord
  have h1 := congrArg (fun f : Module.End F
      ↥(othersSpace ((xbeta (b := b) (c := c) hirr t ht :
        ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1)) =>
    ((f ⟨vx, hvx⟩ : ↥(othersSpace ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1))) :
        I3 → F)) hc
  have h2 : ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) vx = a • vx := by
    simpa only [coe_restrictOthers_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul] using h1
  have ht_eq : (t : F) = a := by
    have h := congrFun h2 (Sum.inl (0 : Fin (3 - 1)))
    rw [xbeta_vx (b := b) (c := c) hirr t ht] at h
    simpa [vx, Units.smul_def] using h
  have h1' := congrArg (fun f : Module.End F
      ↥(othersSpace ((xbeta (b := b) (c := c) hirr t ht :
        ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1)) =>
    ((f ⟨vy, hvy⟩ : ↥(othersSpace ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)).toLinearMap (X - 1))) :
        I3 → F)) hc
  have h2' : ((xbeta (b := b) (c := c) hirr t ht :
      ↥(orthDerived (quadMinus 3 F b c))) : (I3 → F) ≃ₗ[F] (I3 → F)) vy = a • vy := by
    simpa only [coe_restrictOthers_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul] using h1'
  have htinv_eq : ((t⁻¹ : Fˣ) : F) = a := by
    have h := congrFun h2' (Sum.inr (Sum.inl (0 : Fin (3 - 1))))
    rw [xbeta_vy (b := b) (c := c) hirr t ht] at h
    simpa [vy, Units.smul_def] using h
  have htinv : t = t⁻¹ := Units.ext (ht_eq.trans htinv_eq.symm)
  exact t_ne_inv hord htinv

private lemma commutator_mem_supportedFixedDerived_x (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3)
    {g h : (I3 → F) ≃ₗ[F] (I3 → F)}
    (hg : g ∈ isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)))
    (hh : h ∈ isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))) :
    ⁅g, h⁆ ∈ supportedFixedDerived (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)) := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  change ⁅g, h⁆ ∈ supportedFixedDerived (quadMinus 3 F b c) x
  have hx := hx_of (b := b) (c := c) hirr t ht hord
  have h2 : Module.finrank F ↥(othersSpace x.toLinearMap (X - 1)) = 2 := by
    simpa [x] using finrank_othersSpace (b := b) (c := c) hirr t ht hord
  have hne := restrictOthers_x_ne_smul (b := b) (c := c) hirr t ht hord
  have hself := selfMemX (b := b) (c := c) hirr t ht
  have hcomm := commute_of_finrank_two h2
    (by simpa [x] using hne)
    (by simpa [x] using commute_restrictOthers_self_x (b := b) (c := c) hirr t ht hg)
    (by simpa [x] using commute_restrictOthers_self_x (b := b) (c := c) hirr t ht hh)
  have hgh : ∀ r ∈ othersSpace x.toLinearMap (X - 1), g (h r) = h (g r) := by
    intro r hr
    have := congrArg (fun f : Module.End F ↥(othersSpace x.toLinearMap (X - 1)) =>
      ((f ⟨r, hr⟩ : ↥(othersSpace x.toLinearMap (X - 1))) : I3 → F)) hcomm.eq
    simpa [coe_restrictOthers_apply] using this
  have hmemC : ⁅g, h⁆ ∈ isometryCentralizer (quadMinus 3 F b c) x := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hS : ⁅g, h⁆ ∈ supportedBlock (quadMinus 3 F b c) x (X - 1) := by
    refine mem_supportedBlock.mpr ⟨hmemC, fun r hr => ?_⟩
    have hinv : (h * g)⁻¹ r ∈ othersSpace x.toLinearMap (X - 1) :=
      mem_othersSpace_of_apply (Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_inf.mp hh).2 (Subgroup.mem_inf.mp hg).2)) hr
    have hc : ⁅g, h⁆ = (g * h) * (h * g)⁻¹ := by group
    rw [hc, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgh _ hinv,
      ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  refine mem_supportedFixedDerived.mpr ⟨hS, ?_⟩
  have h1 : restrictFixed (quadMinus 3 F b c) x ⟨⁅g, h⁆, hS⟩ =
      ⁅isometryRestrictFixed (quadMinus 3 F b c) x ⟨g, hg⟩,
        isometryRestrictFixed (quadMinus 3 F b c) x ⟨h, hh⟩⁆ := by
    rw [← isometryRestrictFixed_restrictFixed]
    rw [← map_commutatorElement]
    rfl
  rw [h1]
  exact Subgroup.commutator_mem_commutator
    (isometryRestrictFixed_mem_orthogonalGroup _)
    (isometryRestrictFixed_mem_orthogonalGroup _)

private lemma isMinus_fixedSpace (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    IsMinus ((quadMinus 3 F b c).restrict (fixedSpace
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)))) 2 := by
  rw [fixedSpace_eq_Pperp hirr t ht hord]
  exact (isMinus_quadMinus (m := 3) (by norm_num) hirr).perp (P (b := b) (c := c))

private lemma hts_fixedSpace (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    ∀ U : Submodule F ↥(fixedSpace
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))),
      Module.finrank F U = 2 →
        ∃ u ∈ U, (quadMinus 3 F b c).comp (fixedSpace
          ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
            (I3 → F) ≃ₗ[F] (I3 → F))).subtype u ≠ 0 := by
  intro U hU
  have hminus := isMinus_fixedSpace (b := b) (c := c) hirr t ht hord
  have := hminus.noTS U hU
  simpa using this

private lemma isL2_supportedFixedDerived (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    IsL2 (Bar2 (supportedFixedDerived (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F)))) 4 := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  let H : Subgroup ((I3 → F) ≃ₗ[F] (I3 → F)) := supportedFixedDerived (quadMinus 3 F b c) x
  change IsL2 (Bar2 H) 4
  have hx := hx_of (b := b) (c := c) hirr t ht hord
  have hdim : Module.finrank F ↥(fixedSpace x) = 4 := by
    rw [show fixedSpace x = (P (b := b) (c := c)).perp from fixedSpace_eq_Pperp hirr t ht hord]
    exact ((isMinus_quadMinus (m := 3) (by norm_num) hirr).perp
      (P (b := b) (c := c))).finrank_eq
  have hts : ∀ U : Submodule F ↥(fixedSpace x), Module.finrank F U = 2 →
      ∃ u ∈ U, (quadMinus 3 F b c).comp (fixedSpace x).subtype u ≠ 0 := by
    simpa [x] using hts_fixedSpace (b := b) (c := c) hirr t ht hord
  obtain ⟨E, hEf, hAlg, D, ψ, ρ, hψ, hρψ, hinj, hρO, hrange, hsimple,
    hperf, hnonab, hcard, hidx, hnorm, hodd⟩ :=
    even_minus_four_actual_derived_extraction ((quadMinus 3 F b c).comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate hdim hts
  letI : Field E := hEf
  letI : Algebra F E := hAlg
  letI : Finite E := D.finite_E
  letI : CharP E 2 := charP_two_of_algebra (K := F)
  letI : Fintype E := Fintype.ofFinite E
  have hEcard : Nat.card E = 2 ^ 4 := by
    rw [D.card_E, hF]
    norm_num
  let eSL : Matrix.SpecialLinearGroup (Fin 2) E ≃* ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange).symm
  let eH : ↥H ≃* ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) :=
    supportedFixedDerivedEquiv hx
  let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) E := eH.trans eSL.symm
  have hEcardF : Fintype.card E = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hEcard
  have hIsPSL : CFSG.Quasithin.IsPSL 2 2 4 ↥H :=
    CFSG.Quasithin.C41Pf.isPSL_two_two_of_equiv_sl2 (by norm_num) hEcard e
  have hL2H : IsL2 ↥H 4 := Or.inl ⟨by decide, hIsPSL⟩
  have hsimpleOrth :
      IsSimpleGroup ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) := by
    change IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup
      ((quadMinus 3 F b c).comp (fixedSpace x).subtype),
      TauCeti.QuadraticMap.orthogonalGroup
        ((quadMinus 3 F b c).comp (fixedSpace x).subtype)⁆
    rw [hrange]
    exact hsimple
  have hsimpleH : IsSimpleGroup ↥H :=
    (MulEquiv.isSimpleGroup_congr eH).mpr hsimpleOrth
  have hcardH : Nat.card ↥H = Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by
    rw [Nat.card_congr eH.toEquiv]
    have hEq : Nat.card ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) =
        Nat.card ↥ρ.range := by
      change Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup
        ((quadMinus 3 F b c).comp (fixedSpace x).subtype),
        TauCeti.QuadraticMap.orthogonalGroup
          ((quadMinus 3 F b c).comp (fixedSpace x).subtype)⁆ = Nat.card ↥ρ.range
      rw [hrange]
    rw [hEq, hcard]
  have h3card : 3 ∣ Nat.card ↥H := by
    rw [hcardH, hF]
    norm_num
  have hO2 : CFSG.pCore 2 ↥H = ⊥ := by
    rcases hsimpleH.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥H) with h | h
    · exact h
    · exfalso
      have hp2 : IsPGroup 2 ↥H := by
        have htop : IsPGroup 2 ↥(⊤ : Subgroup ↥H) := by
          rw [← h]
          exact CFSG.pCore_isPGroup (p := 2) (G := ↥H)
        exact htop.of_equiv Subgroup.topEquiv
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp2
      have h3 : 3 ∣ 2 ^ n := by
        rw [← hn]
        exact h3card
      have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at h32
  let eBar : Bar2 H ≃* ↥H :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  exact CFSG.Blueprint.LieModel.of_mulEquiv eBar.symm hL2H

private lemma isPerfect_supportedFixedDerived (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    Group.IsPerfect ↥(supportedFixedDerived (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))) := by
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c)))
  let H : Subgroup ((I3 → F) ≃ₗ[F] (I3 → F)) := supportedFixedDerived (quadMinus 3 F b c) x
  change Group.IsPerfect ↥H
  have hx := hx_of (b := b) (c := c) hirr t ht hord
  have hdim : Module.finrank F ↥(fixedSpace x) = 4 := by
    rw [show fixedSpace x = (P (b := b) (c := c)).perp from fixedSpace_eq_Pperp hirr t ht hord]
    exact ((isMinus_quadMinus (m := 3) (by norm_num) hirr).perp
      (P (b := b) (c := c))).finrank_eq
  have hts : ∀ U : Submodule F ↥(fixedSpace x), Module.finrank F U = 2 →
      ∃ u ∈ U, (quadMinus 3 F b c).comp (fixedSpace x).subtype u ≠ 0 := by
    simpa [x] using hts_fixedSpace (b := b) (c := c) hirr t ht hord
  obtain ⟨E, hEf, hAlg, D, ψ, ρ, hψ, hρψ, hinj, hρO, hrange, hsimple,
    hperf, hnonab, hcard, hidx, hnorm, hodd⟩ :=
    even_minus_four_actual_derived_extraction ((quadMinus 3 F b c).comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate hdim hts
  letI : Field E := hEf
  letI : Algebra F E := hAlg
  letI : Finite E := D.finite_E
  letI : CharP E 2 := charP_two_of_algebra (K := F)
  letI : Fintype E := Fintype.ofFinite E
  have hEcard : Nat.card E = 2 ^ 4 := by
    rw [D.card_E, hF]
    norm_num
  let eSL : Matrix.SpecialLinearGroup (Fin 2) E ≃*
      ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange).symm
  let eH : ↥H ≃* ↥(orthDerived ((quadMinus 3 F b c).comp (fixedSpace x).subtype)) :=
    supportedFixedDerivedEquiv hx
  let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 2) E := eH.trans eSL.symm
  have hEcardF : Fintype.card E = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hEcard
  exact CFSG.Quasithin.C126.isPerfect_of_sl2_equiv (by norm_num) hEcardF e

private lemma centralizer_subgroupOf_eq (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) :
    (isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c)) =
      Subgroup.centralizer ({xbeta (b := b) (c := c) hirr t ht} :
        Set ↥(orthDerived (quadMinus 3 F b c))) := by
  ext g
  constructor
  · intro hg
    have hg' := Subgroup.mem_subgroupOf.mp hg
    refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
    simpa using Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg').2
  · intro hg
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr
        ⟨orthDerived_le_orthogonalGroup g.2,
          Subgroup.mem_centralizer_singleton_iff.mpr (by
            simpa using congrArg (fun z : ↥(orthDerived (quadMinus 3 F b c)) =>
              (z : (I3 → F) ≃ₗ[F] (I3 → F)))
              (Subgroup.mem_centralizer_singleton_iff.mp hg))⟩)

private lemma derInf8_subgroupOf_centralizer_eq (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    F08.DerInf8 ((isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c))) =
      (supportedFixedDerived (quadMinus 3 F b c)
        ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
          (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c)) := by
  let Ω := orthDerived (quadMinus 3 F b c)
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : Ω)
  let CΩ : Subgroup Ω := (isometryCentralizer (quadMinus 3 F b c) x).subgroupOf Ω
  let H : Subgroup ((I3 → F) ≃ₗ[F] (I3 → F)) := supportedFixedDerived (quadMinus 3 F b c) x
  let HΩ : Subgroup Ω := H.subgroupOf Ω
  change F08.DerInf8 CΩ = HΩ
  have hx := hx_of (b := b) (c := c) hirr t ht hord
  have hHperf : Group.IsPerfect ↥H :=
    isPerfect_supportedFixedDerived (b := b) (c := c) hF hirr t ht hord
  have hHleΩ : H ≤ Ω := hx.supportedFixedDerived_le_orthDerived
  have hHperfΩ : Group.IsPerfect ↥HΩ := by
    haveI := hHperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hHleΩ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHleΩ).symm.surjective
  have hHleC : HΩ ≤ CΩ :=
    Subgroup.subgroupOf_mono Ω
      (supportedFixedDerived_le_isometryCentralizer (Q := quadMinus 3 F b c) (x := x))
  have hcomm_le : ⁅CΩ, CΩ⁆ ≤ HΩ := by
    refine Subgroup.commutator_le.mpr ?_
    intro g hg k hk
    exact Subgroup.mem_subgroupOf.mpr
      (commutator_mem_supportedFixedDerived_x (b := b) (c := c) hirr t ht hord
        (Subgroup.mem_subgroupOf.mp hg) (Subgroup.mem_subgroupOf.mp hk))
  have hcommHΩ : ⁅HΩ, HΩ⁆ = HΩ := by
    have h := CFSG.GroupTheory.commutator_subgroupOf_eq hHleΩ hHleΩ
    rw [Subgroup.isPerfect_iff.mp hHperf] at h
    exact h
  have hcomm_eq : ⁅CΩ, CΩ⁆ = HΩ :=
    le_antisymm hcomm_le (by
      calc HΩ = ⁅HΩ, HΩ⁆ := hcommHΩ.symm
        _ ≤ ⁅CΩ, CΩ⁆ := Subgroup.commutator_mono hHleC hHleC)
  have hcommSub_le : commutator ↥CΩ ≤ HΩ.subgroupOf CΩ := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := CΩ.subtype) CΩ.subtype_injective]
    change Subgroup.map CΩ.subtype (commutator ↥CΩ) ≤
      Subgroup.map CΩ.subtype (HΩ.subgroupOf CΩ)
    rw [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hHleC]
    exact hcomm_eq.le
  have hcommSub_ge : HΩ.subgroupOf CΩ ≤ commutator ↥CΩ := by
    rw [← Subgroup.map_le_map_iff_of_injective (f := CΩ.subtype) CΩ.subtype_injective]
    rw [Subgroup.map_subgroupOf_eq_of_le hHleC]
    rw [Subgroup.map_subtype_commutator]
    exact hcomm_eq.ge
  have hcommSub : commutator ↥CΩ = HΩ.subgroupOf CΩ :=
    le_antisymm hcommSub_le hcommSub_ge
  have hHΩnormal : (HΩ.subgroupOf CΩ).Normal := by
    rw [← hcommSub]
    infer_instance
  haveI := hHΩnormal
  have hsolv : Group.IsSolvable (↥CΩ ⧸ HΩ.subgroupOf CΩ) :=
    CFSG.RankThree.FieldFixedLayer.isSolvable_quotient_of_commutator_le
      (HΩ.subgroupOf CΩ) hcommSub.le
  have hlePR : CFSG.perfectResidual ↥CΩ ≤ HΩ.subgroupOf CΩ :=
    CFSG.GroupTheory.CoprimeActionSupport.TwoModuloExtension.perfectResidual_le_of_isSolvable_quotient
      hsolv
  have hsubPerf : Group.IsPerfect ↥(HΩ.subgroupOf CΩ) := by
    haveI := hHperfΩ
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hHleC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHleC).symm.surjective
  have hgePR : HΩ.subgroupOf CΩ ≤ CFSG.perfectResidual ↥CΩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
      (HΩ.subgroupOf CΩ) hsubPerf
  change (CFSG.perfectResidual ↥CΩ).map CΩ.subtype = HΩ
  rw [le_antisymm hlePR hgePR, Subgroup.map_subgroupOf_eq_of_le hHleC]

private lemma isL2_bar2_HΩ (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    IsL2 (Bar2 ((supportedFixedDerived (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c)))) 4 := by
  let Ω := orthDerived (quadMinus 3 F b c)
  let x : (I3 → F) ≃ₗ[F] (I3 → F) :=
    (xbeta (b := b) (c := c) hirr t ht : Ω)
  let H : Subgroup ((I3 → F) ≃ₗ[F] (I3 → F)) := supportedFixedDerived (quadMinus 3 F b c) x
  let HΩ : Subgroup Ω := H.subgroupOf Ω
  change IsL2 (Bar2 HΩ) 4
  have hH : IsL2 (Bar2 H) 4 := isL2_supportedFixedDerived (b := b) (c := c) hF hirr t ht hord
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_mulEquiv_map_subtype
    (H := Ω) HΩ
  have hmap : HΩ.map Ω.subtype = H := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (hx_of (b := b) (c := c) hirr t ht hord).supportedFixedDerived_le_orthDerived
  rw [hmap] at e
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hH

private lemma isL2_bar2_derInf8_CΩ (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    IsL2 (Bar2 (F08.DerInf8 ((isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c))))) 4 := by
  rw [derInf8_subgroupOf_centralizer_eq (b := b) (c := c) hF hirr t ht hord]
  exact isL2_bar2_HΩ (b := b) (c := c) hF hirr t ht hord

private lemma map_centralizer_beta (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) :
    (Subgroup.centralizer ({beta (b := b) (c := c) t ht} :
      Set (StatedOmega (StatedQuadMinus 3 F b c)))).map
        (eGamma (b := b) (c := c) hirr).toMonoidHom =
      (isometryCentralizer (quadMinus 3 F b c)
        ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
          (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c)) := by
  rw [CFSG.centralizer_singleton_map (eGamma (b := b) (c := c) hirr)
    (beta (b := b) (c := c) t ht)]
  change Subgroup.centralizer ({xbeta (b := b) (c := c) hirr t ht} :
    Set ↥(orthDerived (quadMinus 3 F b c))) = _
  exact (centralizer_subgroupOf_eq (b := b) (c := c) hirr t ht).symm

private lemma map_derInf8_centralizer_beta (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    (F08.DerInf8 (Subgroup.centralizer ({beta (b := b) (c := c) t ht} :
      Set (StatedOmega (StatedQuadMinus 3 F b c))))).map
        (eGamma (b := b) (c := c) hirr).toMonoidHom =
      F08.DerInf8 ((isometryCentralizer (quadMinus 3 F b c)
        ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
          (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf
        (orthDerived (quadMinus 3 F b c))) := by
  let Γ := StatedOmega (StatedQuadMinus 3 F b c)
  let Ω := orthDerived (quadMinus 3 F b c)
  let CΓ : Subgroup Γ := Subgroup.centralizer ({beta (b := b) (c := c) t ht} : Set Γ)
  let CΩ : Subgroup Ω := (isometryCentralizer (quadMinus 3 F b c)
    ((xbeta (b := b) (c := c) hirr t ht : Ω) : (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf Ω
  change (F08.DerInf8 CΓ).map (eGamma (b := b) (c := c) hirr).toMonoidHom = F08.DerInf8 CΩ
  have hCmap : CΓ.map (eGamma (b := b) (c := c) hirr).toMonoidHom = CΩ :=
    map_centralizer_beta (b := b) (c := c) hirr t ht
  let eC : ↥CΓ ≃* ↥CΩ :=
    ((eGamma (b := b) (c := c) hirr).subgroupMap CΓ).trans
      (MulEquiv.subgroupCongr hCmap)
  have hperf : (CFSG.perfectResidual ↥CΓ).map eC.toMonoidHom =
      CFSG.perfectResidual ↥CΩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
      eC.toMonoidHom eC.surjective
  change ((CFSG.perfectResidual ↥CΓ).map CΓ.subtype).map
      (eGamma (b := b) (c := c) hirr).toMonoidHom =
    (CFSG.perfectResidual ↥CΩ).map CΩ.subtype
  rw [Subgroup.map_map]
  rw [show (eGamma (b := b) (c := c) hirr).toMonoidHom.comp CΓ.subtype =
      CΩ.subtype.comp eC.toMonoidHom from rfl]
  rw [← Subgroup.map_map, hperf]

theorem s168e3_three_centralizer_IsL2 (hF : Nat.card F = 4)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (t : Fˣ) (ht : t ^ 3 = 1) (hord : orderOf t = 3) :
    IsL2 (Bar2 (F08.DerInf8 (Subgroup.centralizer ({beta (b := b) (c := c) t ht} :
      Set (StatedOmega (StatedQuadMinus 3 F b c)))))) 4 := by
  let Γ := StatedOmega (StatedQuadMinus 3 F b c)
  let CΓ : Subgroup Γ := Subgroup.centralizer ({beta (b := b) (c := c) t ht} : Set Γ)
  let CΩ : Subgroup ↥(orthDerived (quadMinus 3 F b c)) :=
    (isometryCentralizer (quadMinus 3 F b c)
      ((xbeta (b := b) (c := c) hirr t ht : ↥(orthDerived (quadMinus 3 F b c))) :
        (I3 → F) ≃ₗ[F] (I3 → F))).subgroupOf (orthDerived (quadMinus 3 F b c))
  change IsL2 (Bar2 (F08.DerInf8 CΓ)) 4
  have hL2CΩ : IsL2 (Bar2 (F08.DerInf8 CΩ)) 4 :=
    isL2_bar2_derInf8_CΩ (b := b) (c := c) hF hirr t ht hord
  have hmapDer : (F08.DerInf8 CΓ).map (eGamma (b := b) (c := c) hirr).toMonoidHom =
      F08.DerInf8 CΩ :=
    map_derInf8_centralizer_beta (b := b) (c := c) hF hirr t ht hord
  have hcomp : (eGamma (b := b) (c := c) hirr).symm.toMonoidHom.comp
      (eGamma (b := b) (c := c) hirr).toMonoidHom = MonoidHom.id Γ := by
    refine MonoidHom.ext fun x => ?_
    exact (eGamma (b := b) (c := c) hirr).symm_apply_apply x
  have hmapSymm : (F08.DerInf8 CΩ).map
      (eGamma (b := b) (c := c) hirr).symm.toMonoidHom = F08.DerInf8 CΓ := by
    have h := congrArg (fun X : Subgroup ↥(orthDerived (quadMinus 3 F b c)) =>
      X.map (eGamma (b := b) (c := c) hirr).symm.toMonoidHom) hmapDer
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h.symm
  obtain ⟨eBar⟩ := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_map
    (φ := (eGamma (b := b) (c := c) hirr).symm) (F08.DerInf8 CΩ)
  rw [← hmapSymm]
  exact CFSG.Blueprint.LieModel.of_mulEquiv eBar.symm hL2CΩ

private abbrev vz : I3 → F := Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1

private lemma vz_ne_zero : (vz : I3 → F) ≠ 0 := by
  intro h
  have h1 : vz (Sum.inr (Sum.inr (0 : Fin 2))) = (1 : F) := by
    change (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) (1 : F) : I3 → F)
      (Sum.inr (Sum.inr (0 : Fin 2))) = 1
    simp
  rw [h] at h1
  exact zero_ne_one h1

private lemma beta_vz (t : Fˣ) (ht : t ^ 3 = 1) :
    (((beta (b := b) (c := c) t ht : GL I3 F) : Matrix I3 I3 F) *ᵥ vz) = vz := by
  rw [beta_coe, coe_diagGL]
  funext j
  rw [Matrix.mulVec_diagonal]
  rcases j with i | i | k
  · fin_cases i <;> simp [vz, torusEntMinus]
  · fin_cases i <;> simp [vz, torusEntMinus]
  · fin_cases k <;> simp [vz, torusEntMinus]

private theorem kOf8103_map_iso {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') (B : Subgroup G) :
    F08.KOf8103 ⊤ (B.map e.toMonoidHom) = (F08.KOf8103 ⊤ B).map e.toMonoidHom := by
  have hcen : Subgroup.centralizer
      ((B.map e.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (B : Set G)).map e.toMonoidHom := by
    rw [Subgroup.coe_map,
      ← CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e (B : Set G)]
  unfold F08.KOf8103
  rw [show (⊤ ⊓ Subgroup.centralizer ((B.map e.toMonoidHom : Subgroup G') : Set G')) =
        (⊤ ⊓ Subgroup.centralizer (B : Set G)).map e.toMonoidHom from by
      rw [top_inf_eq, top_inf_eq, hcen]]
  change Hinf ((⊤ ⊓ Subgroup.centralizer (B : Set G)).map e.toMonoidHom) =
      (Hinf (⊤ ⊓ Subgroup.centralizer (B : Set G))).map e.toMonoidHom
  exact (Hinf_map e.toMonoidHom (⊤ ⊓ Subgroup.centralizer (B : Set G))).symm

private theorem isL2_bar2_map_iso {G G' : Type} [Group G] [Group G'] (A : Subgroup G)
    (e : G ≃* G') {m : ℕ} (h : IsL2 (Bar2 A) m) : IsL2 (Bar2 (A.map e.toMonoidHom)) m := by
  unfold IsL2 at h ⊢
  obtain ⟨e'⟩ := nonempty_bar2_mulEquiv_map A e
  exact CFSG.Blueprint.LieModel.of_mulEquiv e' h

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_exists_notationB_fixed_of_exact_omegaMinus_six_four_cover
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    {K : Subgroup G} (hKc : K ∈ calC D.M)
    (hbarK : barSub V₀ V hV K = lBar V₀ V hV L)
    (hU4K : IsU4 (Bar2 K) 2) :
    ∃ P B : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P K ∧ B ≤ K ∧
      F08.NotationB8103 K P 2 B ∧ V ⊓ centralizer (B : Set G) ≠ ⊥ := by
  classical
  have hH : Hyp125 D V₀ V := c.setting.hyp151.hyp125
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hNat : NatOmegaMinus (lBar V₀ V hV L) ⊤ ⊥ 6 2 := by
    have h := hN
    rwa [hwT] at h
  obtain ⟨F, hFfield, hFfin, b, c₀, hFcard, hbc, ε, ψ, hcoords⟩ :=
    S18.exists_natCoords_of_natOmegaMinus hNat
  letI : Field F := hFfield
  letI : Finite F := hFfin
  have hF2 : Nat.card F = 4 := by
    rw [hFcard]; norm_num
  have hFcard' : Nat.card F = 2 ^ 2 := by rw [hF2]; norm_num
  let : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard'
  obtain ⟨t, htord⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by
    rw [Nat.card_units, hF2])
  have ht : t ^ 3 = 1 := by
    rw [← htord]
    exact pow_orderOf_eq_one t
  let Γ : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :=
    StatedOmega (StatedQuadMinus 3 F b c₀)
  let β : Γ := beta (b := b) (c := c₀) t ht
  have hKstab : K ≤ stabTil V₀ V :=
    hKc.1.le.trans (le_stabTil hH.pairFacts.le_normalizer hH.pairFacts.le_normalizer₀)
  obtain ⟨ψM, hψM⟩ := exists_barLift_of_hyp125 (hV := hV) hH
  obtain ⟨eKM, heKM⟩ := UC22.uc22p22l_barImage_equiv hKc
  have hmap : (UC22.barImage D.M K).map ψM = barSub V₀ V hV K :=
    barImage_map_eq_of_mem_calC hH hKc rfl ψM hψM
  let φ0 : Bar2 K →* ↥(barSub V₀ V hV K) :=
    (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
      ((ψM.subgroupMap (UC22.barImage D.M K)).comp eKM.toMonoidHom)
  have hφ0_act (k : ↥K) :
      ((φ0 (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) :
          ↥(barSub V₀ V hV K)) : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨(k : G), hKstab k.2⟩ := by
    have heKM' : ((eKM (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) :
        ↥(UC22.barImage D.M K)) : Bar2 D.M) =
        QuotientGroup.mk (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hKc.1) k) := by
      simpa only [QuotientGroup.mk'_apply] using heKM k
    change ((MulEquiv.subgroupCongr hmap
      ((ψM.subgroupMap (UC22.barImage D.M K))
        (eKM (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k))) :
        ↥(barSub V₀ V hV K)) : MulAut (Vtil V₀ V hV)) = _
    rw [MulEquiv.subgroupCongr_apply, MonoidHom.subgroupMap_apply_coe, heKM']
    simpa using hψM (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hKc.1) k)
  have hφ0surj : Function.Surjective φ0 :=
    (MulEquiv.subgroupCongr hmap).surjective.comp
      ((MonoidHom.subgroupMap_surjective ψM (UC22.barImage D.M K)).comp eKM.surjective)
  have hsimpleK : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4K
  have hφ0ker : φ0.ker = ⊥ := by
    rcases hsimpleK.eq_bot_or_eq_top_of_normal φ0.ker with h | h
    · exact h
    · exfalso
      have hbot : barSub V₀ V hV K = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨x, hx⟩ := hφ0surj ⟨y, hy⟩
        have hxker : x ∈ φ0.ker := by rw [h]; exact Subgroup.mem_top x
        have hx1 : (⟨y, hy⟩ : ↥(barSub V₀ V hV K)) = 1 :=
          hx.symm.trans (MonoidHom.mem_ker.mp hxker)
        exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)
      exact c.ne (by
        show lBar V₀ V hV L = ⊥
        rw [← hbarK]
        exact hbot)
  have hφ0inj : Function.Injective φ0 :=
    (MonoidHom.ker_eq_bot_iff φ0).mp hφ0ker
  let eBar0 : Bar2 K ≃* ↥(barSub V₀ V hV K) :=
    MulEquiv.ofBijective φ0 ⟨hφ0inj, hφ0surj⟩
  let eBar : Bar2 K ≃* ↥(lBar V₀ V hV L) :=
    eBar0.trans (MulEquiv.subgroupCongr hbarK)
  let e : Bar2 K ≃* Γ := eBar.trans ε
  let Astar : Subgroup Γ := Subgroup.zpowers β
  have hAstarp : IsPGroup 3 Astar := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by
      rw [Nat.card_zpowers, orderOf_beta (b := b) (c := c₀) t ht htord]
      norm_num⟩
  let Abar : Subgroup (Bar2 K) := Astar.comap e.toMonoidHom
  have hAbarp : IsPGroup 3 Abar := hAstarp.comap_of_injective e.toMonoidHom e.injective
  have hAbarmap : Abar.map e.toMonoidHom = Astar := by
    rw [Subgroup.map_comap_eq_self_of_surjective e.surjective]
  have hAbarcard : Nat.card Abar = 3 := by
    let eA : ↥Abar ≃* ↥Astar :=
      (e.subgroupMap Abar).trans (MulEquiv.subgroupCongr hAbarmap)
    rw [Nat.card_congr eA.toEquiv, Nat.card_zpowers,
      orderOf_beta (b := b) (c := c₀) t ht htord]
  have hker3 : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* Bar2 K).ker := by
    have hpc : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) : ↥K →* Bar2 K).ker = CFSG.pCore 2 ↥K := by
      rw [QuotientGroup.ker_mk']
    rw [hpc]
    exact CFSG.Quasithin.H13.NQTerm.not_dvd_card_pCore_two_of_ne (K := ↥K) Nat.prime_three (by norm_num)
  obtain ⟨Bsub, hBsubp, hBsuble, hBsubmap, hBsubdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _) hker3 hAbarp
  let B : Subgroup G := Bsub.map K.subtype
  have hBleK : B ≤ K := Subgroup.map_subtype_le Bsub
  have hBcard : Nat.card B = 3 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    let ψsub : ↥Bsub →* ↥Abar :=
      { toFun := fun x => ⟨(QuotientGroup.mk' (CFSG.pCore 2 ↥K)) x, by
          rw [← hBsubmap]
          exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro x y; ext; simp }
    have hψsubsurj : Function.Surjective ψsub := by
      intro y
      have hy : (y : Bar2 K) ∈ Bsub.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [hBsubmap]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨x, hx⟩, ?_⟩
      exact Subtype.ext hxy
    have hψsubinj : Function.Injective ψsub := by
      intro x y hxy
      have h1 : ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (x : ↥K)) =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (y : ↥K) := by
        exact congrArg Subtype.val hxy
      have h2 : (x : ↥K)⁻¹ * (y : ↥K) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h2' : (x : ↥K)⁻¹ * (y : ↥K) ∈ CFSG.pCore 2 ↥K := by
        rw [QuotientGroup.ker_mk'] at h2; exact h2
      have h3 : (x : ↥K)⁻¹ * (y : ↥K) ∈ Bsub := Bsub.mul_mem (Bsub.inv_mem x.2) y.2
      have h4 : (x : ↥K)⁻¹ * (y : ↥K) ∈ Bsub ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker :=
        ⟨h3, h2⟩
      rw [hBsubdisj] at h4
      have h5 : (x : ↥K)⁻¹ * (y : ↥K) = 1 := Subgroup.mem_bot.mp h4
      exact Subtype.ext (inv_mul_eq_one.mp h5)
    have hcardsub : Nat.card ↥Bsub = Nat.card ↥Abar :=
      Nat.card_congr (MulEquiv.ofBijective ψsub ⟨hψsubinj, hψsubsurj⟩).toEquiv
    rw [hcardsub, hAbarcard]
  have hBsubOf : B.subgroupOf K = Bsub := by
    change (Bsub.map K.subtype).comap K.subtype = Bsub
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective Bsub
  have hBbar : barImage K B = Abar := by
    change (B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = Abar
    rw [hBsubOf, hBsubmap]
  have hBp : IsPGroup 3 B := hBsubp.map K.subtype
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hPsyl, hBP⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isSylowOf_ge_of_isPGroup
      (p := 3) hBleK hBp
  have hL2barA : IsL2 (Bar2 (F08.KOf8103 ⊤ Astar)) 4 := by
    have h := s168e3_three_centralizer_IsL2 (b := b) (c := c₀) hF2 hbc t ht htord
    have hcz : Subgroup.centralizer (Astar : Set Γ) = Subgroup.centralizer ({β} : Set Γ) := by
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hx β (Subgroup.mem_zpowers β)).symm
      · intro hx y hy
        rw [Subgroup.mem_centralizer_singleton_iff] at hx
        have hle : Astar ≤ Subgroup.centralizer ({x} : Set Γ) := by
          rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr hx.symm
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    unfold F08.KOf8103
    rw [top_inf_eq, hcz]
    exact h
  have hAbarSymm : Astar.map (e.symm).toMonoidHom = Abar := by
    rw [← hAbarmap, Subgroup.map_map]
    change Abar.map ((e.symm).toMonoidHom.comp e.toMonoidHom) = Abar
    rw [show (e.symm).toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from by
      refine MonoidHom.ext fun x => ?_
      exact e.symm_apply_apply x, Subgroup.map_id]
  have hL2barAbar : IsL2 (Bar2 (F08.KOf8103 ⊤ Abar)) 4 := by
    have hk := kOf8103_map_iso (G := ↥Γ) (G' := Bar2 K) e.symm Astar
    rw [hAbarSymm] at hk
    have hL2map := isL2_bar2_map_iso (F08.KOf8103 ⊤ Astar) e.symm hL2barA
    rw [← hk] at hL2map
    exact hL2map
  have hL2KB : IsL2 (Bar2 (F08.KOf8103 K B)) 4 := by
    obtain ⟨eDer⟩ := nonempty_bar2_derInf8_equiv hBleK Nat.prime_three (by norm_num) hBp
    have hbar : barImage K B = Abar := hBbar
    have hL2 := hL2barAbar
    rw [← hbar] at hL2
    exact CFSG.Blueprint.LieModel.of_mulEquiv eDer.symm hL2
  have hnotB : F08.NotationB8103 K P 2 B := ⟨hBcard, hBP, hL2KB⟩
  let u : Vtil V₀ V hV := (ψ.symm (Multiplicative.ofAdd (vz : I3 → F))).val
  have hψu : ψ ⟨u, Subgroup.mem_top u⟩ = Multiplicative.ofAdd (vz : I3 → F) := by
    change ψ (ψ.symm (Multiplicative.ofAdd (vz : I3 → F))) = _
    exact ψ.apply_symm_apply _
  have hu_ne : u ≠ 1 := by
    intro hu1
    have h1 : Multiplicative.ofAdd (vz : I3 → F) = 1 := by
      rw [← hψu, hu1]
      exact map_one ψ
    have h2 : (vz : I3 → F) = 0 := by
      simpa using congrArg Multiplicative.toAdd h1
    exact vz_ne_zero h2
  have hβvz : (((β : Γ) : GL I3 F) : Matrix I3 I3 F) *ᵥ (vz : I3 → F) = vz := by
    exact beta_vz (b := b) (c := c₀) t ht
  let α : MulAut (Vtil V₀ V hV) := (ε.symm β : MulAut (Vtil V₀ V hV))
  have hαu : α u = u := by
    have hcoord := hcoords (ε.symm β) ⟨u, Subgroup.mem_top u⟩
    rw [show ε (ε.symm β) = β from ε.apply_symm_apply β, hψu,
      toAdd_ofAdd, hβvz] at hcoord
    rw [← hψu] at hcoord
    exact congrArg Subtype.val (ψ.injective hcoord)
  have hu_fix : u ∈ CFSG.Quasithin.fixV (Subgroup.zpowers α) :=
    CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr hαu
  have hBsub_fix_u : ∀ b : ↥Bsub,
      actTil V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ u = u := by
    intro b
    let bbar : Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) b.1
    have hmemAbar : bbar ∈ Abar := by
      rw [← hBsubmap]
      exact Subgroup.mem_map.mpr ⟨b.1, b.2, rfl⟩
    have hmemAstar : e bbar ∈ Astar := by
      have h : e bbar ∈ Abar.map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨bbar, hmemAbar, rfl⟩
      rwa [hAbarmap] at h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmemAstar
    let l : ↥(lBar V₀ V hV L) := (MulEquiv.subgroupCongr hbarK) (φ0 bbar)
    have hl : ε l = β ^ n := by
      exact hn.symm
    have hlα : (l : MulAut (Vtil V₀ V hV)) = α ^ n := by
      have h := congrArg (fun x : Γ => ε.symm x) hl
      rw [MulEquiv.symm_apply_apply] at h
      rw [h, map_zpow]
      rfl
    have hlu : (l : MulAut (Vtil V₀ V hV)) u = u := by
      rw [hlα]
      exact hu_fix (α ^ n) (Subgroup.zpow_mem_zpowers α n)
    have hlact : (l : MulAut (Vtil V₀ V hV)) =
        actTil V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ := by
      change ((φ0 bbar : ↥(barSub V₀ V hV K)) : MulAut (Vtil V₀ V hV)) = _
      exact hφ0_act b.1
    simpa [hlact] using hlu
  let ρ : ↥Bsub →* MulAut (IntMod V hV) :=
    ((actStab V₀ V hV).comp (Subgroup.inclusion hKstab)).comp Bsub.subtype
  haveI hcommInt : IsMulCommutative (IntMod V hV) := hV.1
  haveI hRnormal : (modNull V₀ V hV).Normal := Subgroup.normal_of_isMulCommutative _
  have hRinv : ∀ b : ↥Bsub, ∀ r ∈ modNull V₀ V hV,
      ρ b r ∈ modNull V₀ V hV := by
    intro b r hr
    change actStab V₀ V hV (Subgroup.inclusion hKstab b.1) r ∈ modNull V₀ V hV
    have hmap := map_modNull V₀ V hV (Subgroup.inclusion hKstab b.1)
    have hm : actStab V₀ V hV (Subgroup.inclusion hKstab b.1) r ∈
        (modNull V₀ V hV).map
          ((actStab V₀ V hV (Subgroup.inclusion hKstab b.1) :
            MulAut (IntMod V hV)) : IntMod V hV →* IntMod V hV) :=
      Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    rwa [hmap] at hm
  have h3V : ¬ 3 ∣ Nat.card ↥V := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV.isPGroup
    rw [hm]
    intro h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hp3 : ¬ 3 ∣ Nat.card ↥(modNull V₀ V hV) := by
    intro h3
    have hdvd : Nat.card ↥(modNull V₀ V hV) ∣ Nat.card (IntMod V hV) :=
      Subgroup.card_subgroup_dvd_card _
    have h3' : 3 ∣ Nat.card (IntMod V hV) := h3.trans hdvd
    have h3'' : 3 ∣ Nat.card ↥V := by
      simpa [IntMod] using h3'
    exact h3V h3''
  obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV u
  have hxcoset : ∀ b : ↥Bsub, ρ b x * x⁻¹ ∈ modNull V₀ V hV := by
    intro b
    have hfixb := hBsub_fix_u b
    have hmk : mkTil V₀ V hV (ρ b x * x⁻¹) = 1 := by
      change mkTil V₀ V hV
        (actStab V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ x * x⁻¹) = 1
      calc mkTil V₀ V hV
            (actStab V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ x * x⁻¹)
          = mkTil V₀ V hV
              (actStab V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ x * x⁻¹) := rfl
        _ = actTil V₀ V hV ⟨(b.1 : G), hKstab b.1.2⟩ (mkTil V₀ V hV x) *
              (mkTil V₀ V hV x)⁻¹ := by
              rw [map_mul, map_inv, actTil_mk]
        _ = mkTil V₀ V hV x * (mkTil V₀ V hV x)⁻¹ := by rw [hx, hfixb]
        _ = 1 := mul_inv_cancel _
    exact (QuotientGroup.eq_one_iff (ρ b x * x⁻¹)).mp hmk
  obtain ⟨y, hycoset, hyfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed
      (p := 3) hBsubp ρ (modNull V₀ V hV) hRnormal hRinv hp3 x hxcoset
  have hmyx : mkTil V₀ V hV y = mkTil V₀ V hV x :=
    (mkTil_eq_iff V₀ V hV y x).mpr hycoset
  have hy_not_v0 : y ∉ modNull V₀ V hV := by
    intro hyR
    have hmu : mkTil V₀ V hV y = u := by rw [hmyx, hx]
    have hy1 : mkTil V₀ V hV y = 1 := (QuotientGroup.eq_one_iff y).mpr hyR
    rw [hy1] at hmu
    exact hu_ne hmu.symm
  have hy_ne_one : y.val ≠ 1 := by
    intro hy1
    apply hy_not_v0
    have hyeq : y = 1 := Subtype.ext hy1
    rw [hyeq]
    exact (modNull V₀ V hV).one_mem
  have hBleCy : B ≤ Subgroup.centralizer ({y.val} : Set G) := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb
    let b1 : ↥Bsub := ⟨b0, hb0⟩
    have hfixb := hyfix b1
    have hval : (b0 : G) * y.val * (b0 : G)⁻¹ = y.val := by
      have h := congrArg (fun z : IntMod V hV => z.val) hfixb
      simpa [ρ, actStab_apply_val] using h
    rw [Subgroup.mem_centralizer_singleton_iff]
    rwa [mul_inv_eq_iff_eq_mul] at hval
  have hfixV : V ⊓ centralizer (B : Set G) ≠ ⊥ := by
    intro hbot
    have hyC : y.val ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBleCy hb)
    have hmem : y.val ∈ V ⊓ centralizer (B : Set G) := ⟨y.2, hyC⟩
    have hy1 : y.val = 1 := by
      have hmem' : y.val ∈ (⊥ : Subgroup G) := by
        simpa [hbot] using hmem
      exact Subgroup.mem_bot.mp hmem'
    exact hy_ne_one hy1
  exact ⟨P, B, hPsyl, hBleK, hnotB, hfixV⟩

theorem s168e3_exists_three_centralizer_fixed_omegaMinus_six_four
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2) :
    ∃ K P B : Subgroup G, K ∈ calC D.M ∧ D.M ≤ normalizer (K : Set G) ∧
      barSub V₀ V hV K = lBar V₀ V hV L ∧ IsU4 (Bar2 K) 2 ∧
      CFSG.ABGLocalTools.IsSylowOf 3 P K ∧ B ≤ K ∧
      F08.NotationB8103 K P 2 B ∧ V ⊓ centralizer (B : Set G) ≠ ⊥ := by
  obtain ⟨K, hKc, hbarK, hnorm, hU4K, _hinj⟩ :=
    s168e3_exists_normal_cover_omegaMinus_six_four D c hs hN
  obtain ⟨P, B, hPsyl, hBK, hnotB, hfixV⟩ :=
    s168e3_exists_notationB_fixed_of_exact_omegaMinus_six_four_cover
      D c hs hN hKc hbarK hU4K
  exact ⟨K, P, B, hKc, hnorm, hbarK, hU4K, hPsyl, hBK, hnotB, hfixV⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
