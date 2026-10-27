module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterModel
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuter
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterGraph
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterReal
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterOverlap
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterAnti
import CFSG.ClassicalGroups.UnitaryFlag.GramSURootGen
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUAniso
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary

namespace UOuter

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private theorem psi_one_fix (h : UnitaryFieldData p f K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hg : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨A, 1⟩
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := by
  rw [primeFormPsi_apply, map_one, mul_one, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  have hAg : (A : GL (Fin n) K) * (g : GL (Fin n) K) = (g : GL (Fin n) K) * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hg
  change (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = g
  rw [hAg, mul_inv_cancel_right]

private theorem psi_bar_fix (h : UnitaryFieldData p f K)
    (B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c) (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hg : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨B, φ⟩
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := by
  rw [primeFormPsi_apply, MulAut.mul_apply]
  change primeFormConjHom h _ B (primeFormFieldAut h
    CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one φ
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  have hBg : (B : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) = (g : GL (Fin n) K) * B := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut]
    have hm : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ =
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := by
      ext i j
      exact hφ _
    rw [hm]
    exact hg
  change (B : GL (Fin n) K) * glAut φ (g : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ = g
  rw [hBg, mul_inv_cancel_right]

private theorem planeGen_of_top (h : UnitaryFieldData p f K)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    {A B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c)
    (hAE : primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
      ⟨A, 1⟩ ∈ E)
    (hA1 : primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
      ⟨A, 1⟩ ≠ 1)
    (hBE : primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
      ⟨B, φ⟩ ∈ E)
    (hB1 : primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
      ⟨B, φ⟩ ≠ 1)
    (M : SUid h.barEquiv n)
    (hM : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {A' : Matrix (Fin n) (Fin n) K}
    (hA' : A' = ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((M⁻¹ : SUid h.barEquiv n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (htop : ∀ H : Subgroup (SUid h.barEquiv n), (∀ g : SUid h.barEquiv n,
      (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g : GL (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∨
        A' * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : GL (Fin n) K) * A') →
      g ∈ H) → H = ⊤) :
    PlaneGen E := by
  classical
  let e : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* SUid h.barEquiv n :=
    MulEquiv.subgroupCongr (gramSU_one_eq_SUid h n)
  let ρ : SUid h.barEquiv n →* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (QuotientGroup.mk' _).comp e.symm.toMonoidHom
  have hρ : ∀ g, ρ g = ((e.symm g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := fun _ => rfl
  have h1 : ∀ g : SUid h.barEquiv n, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g : GL (Fin n) K) * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      ρ g ∈ planeClosure E := fun g hg => by
    rw [hρ]
    exact mem_planeClosure_of_fixed hAE hA1 (psi_one_fix h A (e.symm g) hg)
  have hMfix : ρ M ∈ planeClosure E := by
    rw [hρ]
    exact mem_planeClosure_of_fixed hBE hB1 (psi_bar_fix h B hφ (e.symm M) hM)
  have hH : (planeClosure E).comap ρ = ⊤ := htop _ fun g hg => by
    rw [Subgroup.mem_comap]
    rcases hg with hg | hg
    · exact h1 g hg
    · have hgG : (M : GL (Fin n) K) * A * (M : GL (Fin n) K)⁻¹ * g =
          g * ((M : GL (Fin n) K) * A * (M : GL (Fin n) K)⁻¹) := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hA'] at hg
        simpa only [InvMemClass.coe_inv] using hg
      have hcomm : (A : GL (Fin n) K) * ((M : GL (Fin n) K)⁻¹ * g * M) =
          ((M : GL (Fin n) K)⁻¹ * g * M) * A := by
        calc (A : GL (Fin n) K) * ((M : GL (Fin n) K)⁻¹ * g * M)
            = (M : GL (Fin n) K)⁻¹ * ((M : GL (Fin n) K) * A * (M : GL (Fin n) K)⁻¹ * g) *
                M := by group
          _ = (M : GL (Fin n) K)⁻¹ * (g * ((M : GL (Fin n) K) * A * (M : GL (Fin n) K)⁻¹)) *
                M := by rw [hgG]
          _ = ((M : GL (Fin n) K)⁻¹ * g * M) * A := by group
      have hc := h1 (M⁻¹ * g * M) (by
        have := congrArg Units.val hcomm
        simpa only [Units.val_mul, Subgroup.coe_mul, InvMemClass.coe_inv] using this)
      have hg_eq : g = M * (M⁻¹ * g * M) * M⁻¹ := by group
      rw [hg_eq, map_mul, map_mul, map_inv]
      exact (planeClosure E).mul_mem ((planeClosure E).mul_mem hMfix hc)
        ((planeClosure E).inv_mem hMfix)
  rw [PlaneGen, eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : e y ∈ (planeClosure E).comap ρ := hH ▸ Subgroup.mem_top _
  rw [Subgroup.mem_comap, hρ, MulEquiv.symm_apply_apply] at hy
  exact hy

private theorem exists_conj_SU (h : UnitaryFieldData p f K) {P : GL (Fin n) K}
    {Bm G g : Matrix (Fin n) (Fin n) K} {ν ε : K} (hν : ν ≠ 0)
    (hBP : ν • Bm * (P : Matrix (Fin n) (Fin n) K).map h.bar = P)
    (hPG : ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P = ε • G)
    (hgr : g.map h.bar = g) (hgG : gᵀ * G * g = G) (hgdet : g.det = 1) :
    ∃ M : SUid h.barEquiv n,
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        P * g * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      (((M⁻¹ : SUid h.barEquiv n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        P * g⁻¹ * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ∧
      Bm * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar =
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Bm := by
  set Pm : Matrix (Fin n) (Fin n) K := (P : Matrix (Fin n) (Fin n) K) with hPm
  set Pi : Matrix (Fin n) (Fin n) K := ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hPi
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPb : Pm.map h.bar * Pi.map h.bar = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hgu : IsUnit g.det := by
    rw [hgdet]
    exact isUnit_one
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  have hBP' : Bm * Pm.map h.bar = ν⁻¹ • Pm := by
    calc Bm * Pm.map h.bar = ν⁻¹ • (ν • Bm * Pm.map h.bar) := by
          rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hν, one_smul]
      _ = ν⁻¹ • Pm := by rw [hBP]
  have hPib : Pi.map h.bar = ν • (Pi * Bm) := by
    have hl : ν • (Pi * Bm) * Pm.map h.bar = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc, hBP', Matrix.mul_smul, hPiP, smul_smul,
        mul_inv_cancel₀ hν, one_smul]
    calc Pi.map h.bar = ν • (Pi * Bm) * Pm.map h.bar * Pi.map h.bar := by
          rw [hl, Matrix.one_mul]
      _ = ν • (Pi * Bm) := by rw [Matrix.mul_assoc, hPb, Matrix.mul_one]
  set Mm : Matrix (Fin n) (Fin n) K := Pm * g * Pi with hMm
  have hdet : Mm.det = 1 := by
    rw [hMm, det_mul, det_mul, hgdet, mul_one, ← det_mul, hPPi, det_one]
  have hMbar : Mm.map h.bar = Pm.map h.bar * g * Pi.map h.bar := by
    rw [hMm, Matrix.map_mul, Matrix.map_mul, hgr]
  have hconj : conjTr h.barEquiv Mm * Mm = 1 := by
    have hc : conjTr h.barEquiv Mm = (Mm.map h.bar)ᵀ := rfl
    rw [hc, hMbar, Matrix.transpose_mul, Matrix.transpose_mul]
    calc (Pi.map h.bar)ᵀ * (gᵀ * (Pm.map h.bar)ᵀ) * (Pm * g * Pi)
        = (Pi.map h.bar)ᵀ * (gᵀ * ((Pm.map h.bar)ᵀ * Pm) * g) * Pi := by
          simp only [Matrix.mul_assoc]
      _ = (Pi.map h.bar)ᵀ * (ε • (gᵀ * G * g)) * Pi := by
          rw [hPG, Matrix.mul_smul, Matrix.smul_mul]
      _ = (Pi.map h.bar)ᵀ * ((Pm.map h.bar)ᵀ * Pm) * Pi := by rw [hgG, hPG]
      _ = (Pm.map h.bar * Pi.map h.bar)ᵀ * (Pm * Pi) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPb, hPPi, Matrix.transpose_one, Matrix.one_mul]
  let MG : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero Mm (by rw [hdet]; exact one_ne_zero)
  have hMG : (MG : Matrix (Fin n) (Fin n) K) = Mm := rfl
  have hmem : MG ∈ SUid h.barEquiv n := ⟨hdet, hconj⟩
  refine ⟨⟨MG, hmem⟩, hMG, ?_, ?_⟩
  · change ((MG⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Pm * g⁻¹ * Pi
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hMG, hMm]
    calc Pm * g * Pi * (Pm * g⁻¹ * Pi) = Pm * (g * (Pi * Pm) * g⁻¹) * Pi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPiP, Matrix.mul_one, hgg, Matrix.mul_one, hPPi]
  · change Bm * Mm.map h.bar = Mm * Bm
    rw [hMbar, hPib, hMm]
    calc Bm * (Pm.map h.bar * g * (ν • (Pi * Bm))) = (Bm * Pm.map h.bar) * g * (ν • (Pi * Bm)) := by
          simp only [Matrix.mul_assoc]
      _ = Pm * g * Pi * Bm := by
          rw [hBP', Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
            mul_inv_cancel₀ hν, one_smul]
          simp only [Matrix.mul_assoc]

private theorem conj_lift_props {P : GL (Fin n) K} {Am X X' g Mm Mi : Matrix (Fin n) (Fin n) K}
    {μ : K} (hμ : μ ≠ 0) (hAP : μ • Am * P = P * X) (hgX : g * X = X' * g)
    (hXX' : X * X' = X' * X) (hX'ne : ∀ c : K, X' ≠ c • X) (hgg : g * g⁻¹ = 1)
    (hMm : Mm = P * g * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hMi : Mi = P * g⁻¹ * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    Am * (Mm * Am * Mi) = Mm * Am * Mi * Am ∧ Mm * Am * Mi ≠ Am ∧ Mm * Am * Mi ≠ -Am := by
  set Pm : Matrix (Fin n) (Fin n) K := (P : Matrix (Fin n) (Fin n) K) with hPm
  set Pi : Matrix (Fin n) (Fin n) K := ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hPi
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAm : Am = μ⁻¹ • (Pm * X * Pi) := by
    calc Am = μ⁻¹ • (μ • Am * Pm * Pi) := by
          rw [Matrix.mul_assoc, hPPi, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (Pm * X * Pi) := by rw [hAP]
  have hX' : g * X * g⁻¹ = X' := by rw [hgX, Matrix.mul_assoc, hgg, Matrix.mul_one]
  have hA' : Mm * Am * Mi = μ⁻¹ • (Pm * X' * Pi) := by
    rw [hMm, hMi, hAm, ← hX']
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc Pm * g * Pi * (Pm * X * Pi) * (Pm * g⁻¹ * Pi)
        = Pm * g * (Pi * Pm) * X * (Pi * Pm) * g⁻¹ * Pi := by simp only [Matrix.mul_assoc]
      _ = Pm * (g * X * g⁻¹) * Pi := by
          rw [hPiP, Matrix.mul_one, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have hinj : ∀ Y Z : Matrix (Fin n) (Fin n) K, μ⁻¹ • (Pm * Y * Pi) = μ⁻¹ • (Pm * Z * Pi) →
      Y = Z := by
    intro Y Z hYZ
    have h1 : Pm * Y * Pi = Pm * Z * Pi := smul_right_injective _ (inv_ne_zero hμ) hYZ
    calc Y = Pi * (Pm * Y * Pi) * Pm := by
          simp only [← Matrix.mul_assoc]
          rw [hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
      _ = Pi * (Pm * Z * Pi) * Pm := by rw [h1]
      _ = Z := by
          simp only [← Matrix.mul_assoc]
          rw [hPiP, Matrix.one_mul, Matrix.mul_assoc, hPiP, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA', hAm]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    calc Pm * X * Pi * (Pm * X' * Pi) = Pm * X * (Pi * Pm) * X' * Pi := by
          simp only [Matrix.mul_assoc]
      _ = Pm * X' * (Pi * Pm) * X * Pi := by
          rw [hPiP, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc Pm X X', hXX',
            ← Matrix.mul_assoc]
      _ = Pm * X' * Pi * (Pm * X * Pi) := by simp only [Matrix.mul_assoc]
  · intro he
    rw [hA', hAm] at he
    exact hX'ne 1 (by rw [one_smul]; exact hinj _ _ he)
  · intro he
    rw [hA', hAm] at he
    refine hX'ne (-1) ?_
    rw [neg_one_smul]
    refine hinj _ _ ?_
    rw [he, Matrix.mul_neg, Matrix.neg_mul, smul_neg]

end UOuter

open UOuter in
theorem seitzFourUGraphAniso_holds : SeitzFourUGraphAniso := by
  intro p f K _ h hp n hn hn4 E hE h4 hED hW
  classical
  have := h.finite
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h2K : (2 : K) ≠ 0 := by
    have := h.charP
    exact Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  obtain ⟨A, B, φ, P, ν, μ, ε, α, G, X, hφ, hAE, hA1, hBE, hcover, hν, hμ, hε, hBP, hAP, hPG,
    hGr, hGs, hXr, hXG, hX2⟩ := exists_graph_descent h hp hn hE h4 hED
  set Am : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hAm
  set Pm : Matrix (Fin n) (Fin n) K := (P : Matrix (Fin n) (Fin n) K) with hPm
  set Pi : Matrix (Fin n) (Fin n) K := ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hPi
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAu : (Am.map h.bar)ᵀ * Am = 1 := by
    have hA : (Am.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Am =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := A.2
    simpa only [Units.val_one, Matrix.mul_one] using hA
  have hAA : Am * Am = (μ⁻¹ * μ⁻¹ * α) • 1 := by
    have h1 : (μ * μ) • (Am * Am) * Pm = α • Pm := by
      calc (μ * μ) • (Am * Am) * Pm = μ • Am * (μ • Am * Pm) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        _ = Pm * (X * X) := by rw [hAP, ← Matrix.mul_assoc, hAP, Matrix.mul_assoc]
        _ = α • Pm := by rw [hX2, Matrix.mul_smul, Matrix.mul_one]
    calc Am * Am = (μ⁻¹ * μ⁻¹) • ((μ * μ) • (Am * Am) * Pm * Pi) := by
          rw [Matrix.mul_assoc, hPPi, Matrix.mul_one, smul_smul,
            show μ⁻¹ * μ⁻¹ * (μ * μ) = 1 by field_simp, one_smul]
      _ = (μ⁻¹ * μ⁻¹ * α) • 1 := by
          rw [h1, Matrix.smul_mul, hPPi, smul_smul]
  have hα : α ≠ 0 := by
    rintro rfl
    have h0 : Am * Am = 0 := by rw [hAA, mul_zero, zero_smul]
    exact (A * A : primeFormUnitary h _).1.ne_zero (by simp [hAm] at h0 ⊢)
  have hG : IsUnit G.det := by
    have hPd : Pm.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hPPi
      rw [det_mul, h0, zero_mul, det_one] at this
      exact zero_ne_one this
    have h1 := congrArg Matrix.det hPG
    rw [det_mul, det_transpose, show (Pm.map h.bar).det = h.bar Pm.det from
      (RingHom.map_det h.bar Pm).symm, det_smul, Fintype.card_fin] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, mul_zero] at h1
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hPd) hPd h1
  have hXs : ∀ c : K, X ≠ c • 1 := by
    intro c hc
    have hAc : Am = (μ⁻¹ * c) • 1 := by
      calc Am = μ⁻¹ • (μ • Am * Pm * Pi) := by
            rw [Matrix.mul_assoc, hPPi, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hμ, one_smul]
        _ = (μ⁻¹ * c) • 1 := by
            rw [hAP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPPi, smul_smul]
    apply hA1
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [MulAut.one_apply]
    refine psi_one_fix h A g ?_
    rw [← hAm, hAc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  rcases real_stable_or_orth_conj h hp hn hGr hXr hG hGs hα hXG hX2 hXs with
    ⟨W₁, hW₁, hW₁i, hW₁X, hW₁b⟩ | ⟨-, hXsa, g, X', hgr, hgG, hgdet, hgX, hXX', hX'ne⟩
  · obtain ⟨W, hW0, hWi, hWs⟩ :=
      exists_stable_isotropic_of_real h hφ hcover hν hμ hBP hAP hPG hW₁ hW₁i hW₁X hW₁b
    exact absurd (hW W hWi hWs) hW0
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (by rw [hgdet]; exact isUnit_one)
  have hG0 : G ≠ 0 := fun h0 => by
    have hd : G.det = 0 := by rw [h0]; exact Matrix.det_zero
    rw [hd] at hG
    exact not_isUnit_zero hG
  have hNα : h.norm μ = α := by
    have h1 : α • G = h.norm μ • G := by
      calc α • G = G * (X * X) := by rw [hX2, Matrix.mul_smul, Matrix.mul_one]
        _ = Xᵀ * G * X := by rw [hXsa, Matrix.mul_assoc]
        _ = h.norm μ • G := hXG
    exact (smul_left_injective K hG0 h1).symm
  obtain ⟨M, hMm, hMi, hBM⟩ := exists_conj_SU h
    (Bm := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hν hBP hPG hgr hgG hgdet
  set Mm : Matrix (Fin n) (Fin n) K := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMmdef
  set Mi : Matrix (Fin n) (Fin n) K :=
    (((M⁻¹ : SUid h.barEquiv n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMidef
  obtain ⟨hcomm, hne, hne'⟩ := conj_lift_props hμ hAP hgX hXX' hX'ne hgg hMm hMi
  have hMiM : Mi * Mm = 1 := by
    rw [hMidef, hMmdef, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      Units.val_one]
  have hMMi : Mm * Mi = 1 := by
    rw [hMidef, hMmdef, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hA'2 : Mm * Am * Mi * (Mm * Am * Mi) = Am * Am := by
    calc Mm * Am * Mi * (Mm * Am * Mi) = Mm * (Am * (Mi * Mm) * Am) * Mi := by
          simp only [Matrix.mul_assoc]
      _ = Am * Am := by
          rw [hMiM, Matrix.mul_one, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hMMi]
  have hA'u : ((Mm * Am * Mi).map h.barEquiv)ᵀ * (Mm * Am * Mi) = 1 := by
    have hMu : conjTr h.barEquiv Mm * Mm = 1 := M.2.2
    have hMiu : conjTr h.barEquiv Mi * Mi = 1 := (M⁻¹).2.2
    have hAu' : conjTr h.barEquiv Am * Am = 1 := hAu
    change conjTr h.barEquiv (Mm * Am * Mi) * (Mm * Am * Mi) = 1
    rw [conjTr_mul, conjTr_mul]
    calc conjTr h.barEquiv Mi * (conjTr h.barEquiv Am * conjTr h.barEquiv Mm) * (Mm * Am * Mi)
        = conjTr h.barEquiv Mi * (conjTr h.barEquiv Am * (conjTr h.barEquiv Mm * Mm) * Am) *
            Mi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hMu, Matrix.mul_one, hAu', Matrix.mul_one, hMiu]
  have hB1 : primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
      ⟨B, φ⟩ ≠ 1 := by
    intro hb
    have hr : φ = RingEquiv.refl K := ((primeFormPsi_eq_one_iff h
      CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one hn ⟨B, φ⟩).mp hb).1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    apply hc
    rw [← hφ c, hr]
    rfl
  have hαr : h.bar α = α := by
    have h1 := congrArg (fun Y : Matrix (Fin n) (Fin n) K => Y.map h.bar) hX2
    simp only [Matrix.map_mul, hXr] at h1
    rw [hX2] at h1
    have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h2.symm
  have hbμ : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ
  rw [UnitaryFieldData.norm] at hNα
  by_cases hsq : ∃ s : K, h.bar s = s ∧ α = s * s
  · obtain ⟨s, hs, hαs⟩ := hsq
    refine planeGen_of_top h hφ hAE hA1 hBE hB1 M hBM (A' := Mm * Am * Mi) rfl
      fun H hH => ?_
    refine eq_top_of_comm_unitary_conj h hp hn (σ := h.barEquiv) (fun c => rfl)
      (l := s * μ⁻¹) ?_ hAu hA'u ?_ ?_ hcomm hne hne' hH
    · rw [UnitaryFieldData.barEquiv_apply, map_mul, map_inv₀, hs]
      field_simp
      linear_combination hαs.symm.trans hNα.symm
    · rw [hAA, hαs]
      congr 1
      ring
    · rw [hA'2, hAA, hαs]
      congr 1
      ring
  · obtain ⟨c, hc⟩ := h.normHom_surjective ⟨α, h.mem_fixedField.mpr hαr⟩
    have hcα : h.norm c = α := congrArg Subtype.val hc
    obtain ⟨θ, hθ⟩ : IsSquare α := by
      have h1 := USeitz.isSquare_norm (σ := h.barEquiv) c
      have h2 : h.barEquiv c * c = α := by
        rw [← hcα, UnitaryFieldData.norm, UnitaryFieldData.barEquiv_apply, mul_comm]
      rwa [h2] at h1
    have hθb : h.bar θ = -θ := by
      have h1 : h.bar θ * h.bar θ = θ * θ := by rw [← map_mul, ← hθ, hαr]
      have h2 : (h.bar θ - θ) * (h.bar θ + θ) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd ⟨θ, sub_eq_zero.mp h3, hθ⟩ hsq
      · linear_combination h3
    have hdetX : X.det * X.det = α ^ n := by
      rw [← det_mul, hX2, det_smul, det_one, mul_one, Fintype.card_fin]
    have hdetr : h.bar X.det = X.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hXr]
    have hn4' : n = 4 := by
      by_contra hn4'
      have hn3 : n = 3 := by omega
      apply hsq
      refine ⟨X.det * α⁻¹, by rw [map_mul, map_inv₀, hdetr, hαr], ?_⟩
      have h1 : X.det * α⁻¹ * (X.det * α⁻¹) = X.det * X.det * (α⁻¹ * α⁻¹) := by ring
      rw [h1, hdetX, hn3]
      field_simp
    subst hn4'
    refine planeGen_of_top h hφ hAE hA1 hBE hB1 M hBM (A' := Mm * Am * Mi) rfl
      fun H hH => ?_
    refine eq_top_of_comm_anti_conj h.isUnitaryInvolution_barEquiv h2K (l := θ * μ⁻¹) ?_ hAu
      hA'u ?_ ?_ hcomm hne hne' hH
    · rw [UnitaryFieldData.barEquiv_apply, map_mul, map_inv₀, hθb]
      field_simp
      linear_combination hθ + hNα
    · rw [hAA, hθ]
      congr 1
      ring
    · rw [hA'2, hAA, hθ]
      congr 1
      ring

theorem seitzFourOuter_psu :
    SeitzFourOuter fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f :=
  seitzFourOuter_psu_of_graphAniso seitzFourUGraphAniso_holds

end CFSG.LocalAnalysis.WeakClosure81
