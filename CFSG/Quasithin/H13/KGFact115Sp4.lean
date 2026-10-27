module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726CPar
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagTriangular
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourModel
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.CGT.PushingUpLit.LIT.Foote.GroupAux
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Chevalley
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Linear
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Symplectic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.H13.KG14726Elim
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
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.H13.KG115Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Quasithin.H13.KG14726

theorem cond_conj {X : Type} [Group X] (g : X) {u : X}
    (h : (∃ ℓ : X, ℓ * u = u * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) ∨
      ∀ y : X, y * u = u * y → orderOf y ≠ 3) :
    (∃ ℓ : X, ℓ * (g * u * g⁻¹) = g * u * g⁻¹ * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) ∨
      ∀ y : X, y * (g * u * g⁻¹) = g * u * g⁻¹ * y → orderOf y ≠ 3 := by
  rcases h with h | h
  · exact Or.inl (prime_conj g h)
  · refine Or.inr fun y hy => ?_
    have h1 : g⁻¹ * y * g * u = u * (g⁻¹ * y * g) := by
      calc g⁻¹ * y * g * u = g⁻¹ * (y * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * u * g⁻¹ * y) * g := by rw [hy]
        _ = u * (g⁻¹ * y * g) := by group
    have h2 : orderOf (g⁻¹ * y * g) = orderOf y := by
      rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by rw [MulAut.conj_apply, inv_inv],
        MulEquiv.orderOf_eq]
    exact h2 ▸ h _ h1

variable {K : Type} [Field K]

local notation "Sp₄" => StatedSp 2 K
local notation "M₂" => Matrix (Fin 2) (Fin 2) K
local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K

theorem mul_mul_transpose_eq {g : Sp₄} {E : M₂}
    (h0 : ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₂₁ = 0)
    (h : ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄) * fromBlocks 1 E 0 1 =
      fromBlocks 1 E 0 1 * ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁ * E *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁ᵀ = E := by
  set M := ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄) with hM
  have hMb : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h0]
    exact (fromBlocks_toBlocks M).symm
  have hsp := mem_statedSp_iff.mp g.2
  rw [← hM, hMb] at hsp
  obtain ⟨h1, -⟩ := fromBlocks_symplectic_of_lower_zero hsp
  rw [hMb, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨-, h2, -, -⟩ := h
  simp only [Matrix.one_mul, Matrix.mul_one] at h2
  have h3 : M.toBlocks₁₁ * E = E * M.toBlocks₂₂ := by
    rw [add_comm] at h2
    exact add_left_cancel h2
  rw [h3, Matrix.mul_assoc, mul_eq_one_comm.mp h1, Matrix.mul_one]

theorem toBlocks₂₁_eq_zero_of_comm {g : Sp₄} {E : M₂} (hE : IsUnit E.det)
    (h : ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄) * fromBlocks 1 E 0 1 =
      fromBlocks 1 E 0 1 * ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₂₁ = 0 := by
  set M := ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)
  rw [← fromBlocks_toBlocks M, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h1, -, -, -⟩ := h
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero] at h1
  have h2 : E * M.toBlocks₂₁ = 0 := by simpa using h1
  calc M.toBlocks₂₁ = E⁻¹ * (E * M.toBlocks₂₁) := (nonsing_inv_mul_cancel_left _ _ hE).symm
    _ = 0 := by rw [h2, Matrix.mul_zero]

theorem comm_of_blockDiag {h : Sp₄} {P D C : M₂}
    (hh : ((h : GL (Fin 2 ⊕ Fin 2) K) : M₄) = fromBlocks P 0 0 D) (hC : P * C * Pᵀ = C) :
    ((h : GL (Fin 2 ⊕ Fin 2) K) : M₄) * fromBlocks 1 C 0 1 =
      fromBlocks 1 C 0 1 * ((h : GL (Fin 2 ⊕ Fin 2) K) : M₄) := by
  have hsp := mem_statedSp_iff.mp h.2
  rw [hh] at hsp
  obtain ⟨h1, -⟩ := fromBlocks_symplectic_of_lower_zero hsp
  have h2 : C * D = P * C := by
    calc C * D = P * C * Pᵀ * D := by rw [hC]
      _ = P * C * (Pᵀ * D) := by rw [Matrix.mul_assoc (P * C)]
      _ = P * C := by rw [h1, Matrix.mul_one]
  rw [hh, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, by simp⟩
  simp [h2]

theorem zSym (c d : K) : (!![c, d; d, 0] : M₂)ᵀ = !![c, d; d, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (K) in
@[expose] noncomputable def zElt (c d : K) : Sp₄ :=
  upperUnipotentSp 2 K (zSym c d)

theorem coe_zElt (c d : K) :
    (((zElt K c d : Sp₄) : GL (Fin 2 ⊕ Fin 2) K) : M₄) = fromBlocks 1 !![c, d; d, 0] 0 1 :=
  coe_upperUnipotentSp _

theorem zElt_mem (c d : K) : zElt K c d ∈ unipotent 2 K :=
  ⟨1, !![c, d; d, 0], isUnitriangular_one, zSym c d, by rw [coe_zElt]; simp [blockMat]⟩

theorem exists_eq_zElt {u : Sp₄} (hu : u ∈ unipotent 2 K)
    (hc : ∀ s ∈ unipotent 2 K, s * u = u * s) : ∃ c d : K, u = zElt K c d := by
  obtain ⟨A, C, hA, hC, hM⟩ := hu
  have hE : (!![0, 0; 0, 1] : M₂)ᵀ = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hs₁ : upperUnipotentSp 2 K hE ∈ unipotent 2 K :=
    ⟨1, _, isUnitriangular_one, hE, by rw [coe_upperUnipotentSp]; simp [blockMat]⟩
  have h1 := congrArg (fun g : Sp₄ => ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) (hc _ hs₁)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp] at h1
  have h0 : ((u : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₂₁ = 0 := by
    rw [hM]
    simp [blockMat]
  have hAE := mul_mul_transpose_eq h0 h1.symm
  have hA11 : ((u : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁ = A := by
    rw [hM]
    simp [blockMat]
  rw [hA11] at hAE
  have h00 := congrFun (congrFun hAE 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hA1 : A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using hA.2 0
    · simpa using h00
    · simpa using hA.1 (show (0 : Fin 2) < 1 by decide)
    · simpa using hA.2 1
  subst hA1
  have hN : IsUnitriangular (!![1, 1; 0, 1] : M₂) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> rfl
  obtain ⟨s₂, hs₂, hs₂M⟩ := exists_mem_unipotent hN (transpose_zero (m := Fin 2) (n := Fin 2))
  have h2 := congrArg (fun g : Sp₄ => ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) (hc _ hs₂)
  simp only [Subgroup.coe_mul, Units.val_mul] at h2
  have hM' : ((u : GL (Fin 2 ⊕ Fin 2) K) : M₄) = fromBlocks 1 C 0 1 := by
    rw [hM]
    simp [blockMat]
  rw [hM'] at h2
  have h0₂ : ((s₂ : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₂₁ = 0 := by
    rw [hs₂M]
    simp [blockMat]
  have hNC := mul_mul_transpose_eq h0₂ h2
  have hN11 : ((s₂ : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁ = !![1, 1; 0, 1] := by
    rw [hs₂M]
    simp [blockMat]
  rw [hN11] at hNC
  have h01 := congrFun (congrFun hNC 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at h01
  have hC10 : C 1 0 = C 0 1 := by
    have := congrFun (congrFun hC 0) 1
    simpa using this
  refine ⟨C 0 0, C 0 1, ?_⟩
  apply statedSp_ext
  rw [hM', coe_zElt]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · simpa using hC10
  · simpa using h01

variable [CharP K 2]

theorem mem_unipotent_of_comm {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) {g : Sp₄}
    (h : g * zElt K c d = zElt K c d * g) : g ∈ unipotent 2 K := by
  have hm := congrArg (fun g : Sp₄ => ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_zElt] at hm
  have hdet : IsUnit (!![c, d; d, 0] : M₂).det := by
    rw [det_fin_two_of]
    simpa using hd
  have h0 := toBlocks₂₁_eq_zero_of_comm hdet hm
  obtain ⟨-, R, hR, hgR⟩ := exists_blockMat_of_toBlocks₂₁_eq_zero h0
  have hAC := mul_mul_transpose_eq h0 hm
  set A := ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁
  have e11 := congrFun (congrFun hAC 1) 1
  have e00 := congrFun (congrFun hAC 0) 0
  have e01 := congrFun (congrFun hAC 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11 e00 e01
  have h10 : A 1 0 = 0 := by
    have h' : c * A 1 0 ^ 2 = 0 := by
      linear_combination e11 - d * A 1 0 * A 1 1 * CharTwo.two_eq_zero (R := K)
    simpa [hc] using h'
  rw [h10] at e01
  have h00 : A 0 0 = 1 := by
    have h' : c * (A 0 0 - 1) ^ 2 = 0 := by
      linear_combination e00 + (c - c * A 0 0 - d * A 0 0 * A 0 1) * CharTwo.two_eq_zero (R := K)
    have h'' : (A 0 0 - 1) ^ 2 = 0 := by simpa [hc] using h'
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'')
  rw [h00] at e01
  have h11 : A 1 1 = 1 := by
    have h' : d * (A 1 1 - 1) = 0 := by linear_combination e01
    simpa [hd, sub_eq_zero] using h'
  refine ⟨A, R, ⟨fun i j hij => ?_, fun i => ?_⟩, hR, hgR⟩
  · fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact h10
    · exact absurd hij (by decide)
  · fin_cases i
    · exact h00
    · exact h11

variable [Finite K]

theorem orderOf_ne_three_of_mem_unipotent {g : Sp₄} (hg : g ∈ unipotent 2 K) :
    orderOf g ≠ 3 := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hP ▸ hg⟩
  have h1 : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  intro h3
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [h3] at h2
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h2)
  omega

omit [CharP K 2] [Finite K] in
theorem lam_injective (i : Fin 2) :
    Function.Injective (lam i : SpecialLinearGroup (Fin 2) K →* Sp₄) := by
  intro A B h
  have h' := congrArg (fun g : Sp₄ => ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄)) h
  simp only [coe_lam] at h'
  obtain ⟨a1, a2, a3, a4⟩ := pairMat_apply_pair (R := K)
    (Sum.inl_ne_inr : (Sum.inl i : Fin 2 ⊕ Fin 2) ≠ Sum.inr i) (A : M₂)
  obtain ⟨b1, b2, b3, b4⟩ := pairMat_apply_pair (R := K)
    (Sum.inl_ne_inr : (Sum.inl i : Fin 2 ⊕ Fin 2) ≠ Sum.inr i) (B : M₂)
  rw [h'] at a1 a2 a3 a4
  ext j k
  fin_cases j <;> fin_cases k
  · exact a1.symm.trans b1
  · exact a2.symm.trans b2
  · exact a3.symm.trans b3
  · exact a4.symm.trans b4

omit [CharP K 2] [Finite K] in
theorem leviSL_injective :
    Function.Injective (leviSp.comp Matrix.SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 2) K →* Sp₄) := by
  intro A B h
  have h' := congrArg (fun g : Sp₄ => ((g : GL (Fin 2 ⊕ Fin 2) K) : M₄).toBlocks₁₁) h
  simp only [MonoidHom.comp_apply, coe_leviSp, toBlocks_fromBlocks₁₁] at h'
  exact Subtype.ext h'

omit [CharP K 2] [Finite K] in
theorem lam_comm_long (c : K) (A : SpecialLinearGroup (Fin 2) K) :
    lam 1 A * zElt K c 0 = zElt K c 0 * lam 1 A := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_lam, coe_zElt]
  have hz : IsSupp ({Sum.inl 0, Sum.inr 0} : Set (Fin 2 ⊕ Fin 2))
      (fromBlocks 1 !![c, 0; 0, 0] 0 1 : M₄) := by
    rintro (i | i) (j | j) h <;> fin_cases i <;> fin_cases j <;> simp_all [one_apply]
  have hdisj : Disjoint ({Sum.inl 1, Sum.inr 1} : Set (Fin 2 ⊕ Fin 2)) {Sum.inl 0, Sum.inr 0} := by
    rw [Set.disjoint_left]
    rintro x hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp at h
  exact ((isSupp_pairMat (A : M₂)).commute hz hdisj).eq

omit [Finite K] in
theorem levi_comm_short (d : K) (A : SpecialLinearGroup (Fin 2) K) :
    leviSp (Matrix.SpecialLinearGroup.toGL A) * zElt K 0 d =
      zElt K 0 d * leviSp (Matrix.SpecialLinearGroup.toGL A) := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_zElt]
  refine comm_of_blockDiag (coe_leviSp _) ?_
  have hdet := A.2
  rw [det_fin_two] at hdet
  have h2 := CharTwo.two_eq_zero (R := K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  · linear_combination (d * (A : M₂) 0 0 * (A : M₂) 0 1) * h2
  · linear_combination d * hdet + (d * (A : M₂) 0 1 * (A : M₂) 1 0) * h2
  · linear_combination d * hdet + (d * (A : M₂) 0 1 * (A : M₂) 1 0) * h2
  · linear_combination (d * (A : M₂) 1 0 * (A : M₂) 1 1) * h2

theorem cond_of_center {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) {u : Sp₄}
    (hu : u ∈ unipotent 2 K) (hc : ∀ s ∈ unipotent 2 K, s * u = u * s) :
    (∃ ℓ : Sp₄, ℓ * u = u * ℓ ∧ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) ∨
      ∀ y : Sp₄, y * u = u * y → orderOf y ≠ 3 := by
  obtain ⟨c, d, rfl⟩ := exists_eq_zElt hu hc
  obtain ⟨p, hp, hp5, A, hA⟩ := exists_prime_orderOf_sl2 hK hf
  by_cases hd : d = 0
  · subst hd
    exact Or.inl ⟨lam 1 A, lam_comm_long c A, p, hp, hp5, by
      rw [orderOf_injective _ (lam_injective 1) A, hA]⟩
  by_cases hc0 : c = 0
  · subst hc0
    refine Or.inl ⟨leviSp (Matrix.SpecialLinearGroup.toGL A), levi_comm_short d A, p, hp, hp5, ?_⟩
    rw [← MonoidHom.comp_apply, orderOf_injective _ leviSL_injective A, hA]
  · exact Or.inr fun y hy => orderOf_ne_three_of_mem_unipotent (mem_unipotent_of_comm hc0 hd hy)

theorem kg115Excluded_sp4 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    KG115Excluded Sp₄ := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hs : IsSimpleGroup (StatedProj Sp₄) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))
  have e : StatedProj Sp₄ ≃* Sp₄ := (QuotientGroup.quotientMulEquivOfEq
    (SymplecticCoverFour.statedScalars_subgroupOf_eq_bot 2)).trans QuotientGroup.quotientBot
  have : IsSimpleGroup Sp₄ := e.symm.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU : IsPGroup 2 (unipotent 2 K) := hP ▸ P.isPGroup'
  have hUi : ¬ 2 ∣ (unipotent 2 K).index := hP ▸ P.not_dvd_index
  refine kg115Excluded_of_simple fun hc => kg115Excluded_of_data hc ⟨?_, ?_⟩
  · exact sylowTwoNoThree_of_conj hU hUi fun y hy hyU =>
      orderOf_ne_three_of_mem_unipotent
        (mem_unipotent_of_comm one_ne_zero one_ne_zero (hyU _ (zElt_mem 1 1)).symm) hy
  · exact forall_center_of_conj hU hUi (fun g _ hu => cond_conj g hu)
      fun u hu huc _ => cond_of_center hK hf hu huc

end CFSG.Quasithin.H13.KG115Sp4

namespace CFSG.Quasithin.H13.KG115Sp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.KG14726

theorem kg115Sp4Input_holds : KG115Sp4Input := by
  intro f X _ hf hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  exact kg115Excluded_of_mulEquiv (e.trans ((QuotientGroup.quotientMulEquivOfEq
    (SymplecticCoverFour.statedScalars_subgroupOf_eq_bot 2)).trans QuotientGroup.quotientBot))
    (kg115Excluded_sp4 hK hf)

end CFSG.Quasithin.H13.KG115Sp4

end
