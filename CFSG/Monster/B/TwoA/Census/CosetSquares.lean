module

public import CFSG.Monster.B.TwoA.Census.CosetReps
public import CFSG.Monster.B.TwoA.Census.CosetCert
public import CFSG.Monster.B.TwoA.Census.LatticeInv
public import CFSG.Monster.B.Rep4371.SpinAct
public import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public import CFSG.Monster.B.TwoA.Census.CosetSquaresInputs
public import Certificates.Certificate3022
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem toC_cosetA (i : ℕ) :
    toC (cosetA i) = cosetCode i :=
  toC_coeffN (monoWord_mem i)

theorem repPerm_cosetArr (i : ℕ) :
    RepPerm (seedAut (monoSeed.getD i 0) : Equiv.Perm (Fin 24)) (cosetArr i) := by
  intro k
  rw [coe_seedAut_eq (monoSeed_lt i)]
  exact decode_apply (seedHyp (monoSeed_lt i)).perm k

theorem cosetPair_eq (i : ℕ) :
    cosetPair i =
    ⟨(YU ⟨toC (cosetA i), 0⟩, gO (toC (cosetA i))), YU_gO_mem_Pvis _⟩ *
      ⟨(sU (seedAut (monoSeed.getD i 0)), PO (seedAut (monoSeed.getD i 0))),
        sU_PO_mem_Pvis _⟩ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, toC_cosetA]
  rfl

@[expose] def alphaN (i : ℕ) (y : Model.Pauli) : Model.Pauli :=
  Model.conjPermN (cosetArr i) (Model.conjYN (cosetA i) y)

theorem conjQ_cosetPair
    (i : ℕ) (y : Model.Pauli) :
    conjQ (cosetPair i) (pauliQ y) = pauliQ (alphaN i y) := by
  rw [cosetPair_eq, conjQ_mul, conjQ_sign_toQ, conjQ_perm_toQ _ (repPerm_cosetArr i)]
  rfl

theorem genCheck_native :
    genCheck Native.conjYN Native.conjPermN = true :=
  Certificates.certificate3022.1

theorem genCheck_eq_true : genCheck Model.conjYN Model.conjPermN =
    true := by
  rw [← native_conjYN, ← native_conjPermN]
  exact genCheck_native

theorem alphaN_gen {c : CosetRecord} (hc : c ∈ cosetData) {k : ℕ}
    (hk : k < 24) :
    alphaN c.index (genPauli k) = ofTriple (c.genImages.getD k (0, 0, 0)) := by
  have h := genCheck_eq_true
  simp only [genCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h c hc k hk

theorem sqRowCheck_native : ∀ i ∈ [1, 2, 6],
    sqRowCheck Native.eYN Native.ePermN Native.ePauliN i (sqPauli i) = true :=
  Certificates.certificate3022.2

theorem sqRowCheck_eq_true {i : ℕ} (hi : i ∈ [1, 2, 6]) :
    sqRowCheck Model.eYN Model.ePermN Model.ePauliN i (sqPauli i) = true := by
  rw [← native_eYN, ← native_ePermN, ← native_ePauliN]
  exact sqRowCheck_native i hi

theorem sgn_boolZ_xor (a b : Bool) : sgn (boolZ (a ^^ b)) = sgn (boolZ a) * sgn (boolZ b) := by
  rw [sgn_boolZ, sgn_boolZ, sgn_boolZ, sgnI_xor]

@[expose] def sigmaMat (i : ℕ) : Matrix SpinIdx SpinIdx ℚ :=
  Ymat ⟨toC (cosetA i), 0⟩ * smat (seedAut (monoSeed.getD i 0))

theorem Evec_vecMul_sigma (i : ℕ)
    (η : Bool) (c : ℕ) :
    Evec η c ᵥ* sigmaMat i =
      sgn (boolZ (eSigma Model.eYN Model.ePermN i η c).1) •
        Evec (eSigma Model.eYN Model.ePermN i η c).2.1
          (eSigma Model.eYN Model.ePermN i η c).2.2 := by
  rw [sigmaMat, ← vecMul_vecMul, Evec_vecMul_Ymat, smul_vecMul,
    Evec_vecMul_smat _ (repPerm_cosetArr i), smul_smul]
  simp only [eSigma]
  rw [sgn_boolZ_xor]

theorem Evec_vecMul_sigmaSq (i : ℕ)
    (η : Bool) (c : ℕ) :
    Evec η c ᵥ* (sigmaMat i * sigmaMat i) =
      sgn (boolZ (eSigmaSq Model.eYN Model.ePermN i η c).1) •
        Evec (eSigmaSq Model.eYN Model.ePermN i η c).2.1
          (eSigmaSq Model.eYN Model.ePermN i η c).2.2 := by
  rw [← vecMul_vecMul, Evec_vecMul_sigma, smul_vecMul, Evec_vecMul_sigma, smul_smul]
  simp only [eSigmaSq]
  rw [sgn_boolZ_xor]

theorem matrix_eq_of_Evec {M N : Matrix SpinIdx SpinIdx ℚ}
    (h : ∀ η : Bool, ∀ c < 4096, Evec η c ᵥ* M = Evec η c ᵥ* N) : M = N := by
  ext ⟨η₀, c₀⟩ j
  obtain ⟨c, hc, hce⟩ := exists_toC (c₀ : C)
  have hE : (E η₀ c₀ : SpinIdx → ℚ) = Evec (decide (η₀ = 1)) c := by
    rw [Evec, boolZ_decide_eq_one, hce, π₀_coe]
  have hM : ∀ P : Matrix SpinIdx SpinIdx ℚ, P (η₀, c₀) j = (Evec (decide (η₀ = 1)) c ᵥ* P) j := by
    intro P
    rw [← hE, E, single_vecMul, one_smul]
    rfl
  rw [hM M, hM N, h _ c (by simpa using hc)]

theorem sigma_sq
    {i : ℕ} (hi : i ∈ [1, 2, 6]) :
    sigmaMat i * sigmaMat i =
      qmatR ℚ (boolZ (sqPauli i).s) (toC (sqPauli i).a) (toD (sqPauli i).d) := by
  have h := sqRowCheck_eq_true hi
  simp only [sqRowCheck, List.all_eq_true, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, beq_iff_eq] at h
  refine matrix_eq_of_Evec fun η c hc => ?_
  rw [Evec_vecMul_sigmaSq, Evec_vecMul_qmatR]
  have hc' := h c hc η (by cases η <;> simp)
  rw [hc']

theorem coe_cosetPair_fst (i : ℕ) :
    (((cosetPair i : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      sigmaMat i := by
  rw [coe_cosetPair, sigmaMat, toC_cosetA]
  rfl

theorem cosetPair_sq_fst
    {i : ℕ} (hi : i ∈ [1, 2, 6]) :
    ((cosetPair i * cosetPair i : Pvis) : GL SpinIdx ℚ × latticeO).1 =
      (pauliQ (sqPauli i) : GL SpinIdx ℚ) := by
  apply Units.ext
  rw [Subgroup.coe_mul, Prod.fst_mul, Units.val_mul, coe_cosetPair_fst, sigma_sq hi,
    qmatR_toSC_eq]

theorem monoAO_sq_eq_one
    {i : ℕ}
    (hi : i = 1 ∨ i = 2) : monoAO i * monoAO i = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -⟩ := lattice_quotient_three_involution_classes
  apply mat_injective
  rw [mat_mul, mat_monoAO, mat_one]
  rcases hi with rfl | rfl
  · exact h1
  · exact h2

theorem monoAO_six_sq :
    monoAO 6 *
    monoAO 6 = negOneO := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h6⟩ := lattice_quotient_three_involution_classes
  apply mat_injective
  rw [mat_mul, mat_monoAO, mat_negOneO]
  exact h6

theorem cosetPair_sq_of_ne_six
    {i : ℕ} (hi : i = 1 ∨ i = 2) :
    cosetPair i * cosetPair i = rhoPair (pauliQ (sqPauli i)) := by
  have hi' : i ∈ [1, 2, 6] := by rcases hi with rfl | rfl <;> simp
  apply Subtype.ext
  rw [coe_rhoPair]
  refine Prod.ext ?_ ?_
  · exact cosetPair_sq_fst hi'
  · rw [Subgroup.coe_mul, Prod.snd_mul, coe_cosetPair]
    exact monoAO_sq_eq_one hi

theorem pauliQ_sqPauli_one : pauliQ (sqPauli 1) = 1 := by
  rw [show sqPauli 1 = (false, 0, 0) from rfl, pauliQ, toSC]
  simp only [pauli_s, pauli_a, pauli_d, boolZ_false, toC_zero, toD_zero]
  exact map_one spinEquiv

theorem pauliQ_sqPauli_six : pauliQ (sqPauli 6) = 1 := by
  rw [show sqPauli 6 = (false, 0, 0) from rfl, pauliQ, toSC]
  simp only [pauli_s, pauli_a, pauli_d, boolZ_false, toC_zero, toD_zero]
  exact map_one spinEquiv

theorem cosetPair_six_sq :
    cosetPair 6 * cosetPair 6 = rhoPair zQ *
    negPair := by
  apply Subtype.ext
  conv_rhs => rw [Subgroup.coe_mul, coe_rhoPair, coe_negPair, Prod.mk_mul_mk, coe_zQ]
  refine Prod.ext ?_ ?_
  · rw [cosetPair_sq_fst (by simp), pauliQ_sqPauli_six, Subgroup.coe_one]
    show (1 : GL SpinIdx ℚ) = zU * zU
    apply Units.ext
    rw [Units.val_one, Units.val_mul, coe_zU]
    simp [zmat]
  · rw [Subgroup.coe_mul, Prod.snd_mul, coe_cosetPair]
    show monoAO 6 * monoAO 6 = 1 * negOneO
    rw [monoAO_six_sq, one_mul]

theorem cosetRep_sq :
    ((cosetRep 1 * cosetRep 1 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = 1 ∧
    ((cosetRep 2 * cosetRep 2 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv (qP 1 63 0) ∧
    ((cosetRep 6 * cosetRep 6 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = xB := by
  have hsq : ∀ i, ((cosetRep i * cosetRep i : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
      thetaEquiv (cosetPair i * cosetPair i) := fun i => by
    rw [thetaEquiv_mul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsq, cosetPair_sq_of_ne_six (Or.inl rfl), pauliQ_sqPauli_one, map_one, thetaEquiv_one]
  · rw [hsq, cosetPair_sq_of_ne_six (Or.inr rfl)]
    rfl
  · rw [hsq, cosetPair_six_sq, thetaEquiv_mul_negPair]
    exact rhoEquiv_zQ

end CFSG.Monster.B.TwoA.Census
