module

public import CFSG.Quasithin.Background.SmithB45HM22Class
public import Certificates.Certificate260415
public import Certificates.Certificate260416
public import Certificates.Certificate260417

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

theorem hm22_flag_checks :
    flagCheck3a = true ∧ flagCheck3b = true ∧ flagCheck9 = true :=
  Certificates.certificate260415

theorem hm22_norton_checks :
    norCheck6 = true ∧ norCheck15 = true ∧ norCheck45 = true ∧ norCheck45c = true ∧
      norCheck84 = true :=
  Certificates.certificate260416

theorem hm22_hnorton_checks :
    hnorCheck3a = true ∧ hnorCheck3b = true ∧ hnorCheck9 = true ∧ hnorCheck24a = true ∧
      hnorCheck24b = true ∧ hTraceCheck = true :=
  Certificates.certificate260417

@[expose] noncomputable def pairOf (n : ℕ) (A B : PM) :
    Bool → ((Fin n → FieldFour) →ₗ[FieldFour] (Fin n → FieldFour)) :=
  fun b => Matrix.toLin' (if b then PM.toMat n n B else PM.toMat n n A)

theorem irredFam_std6 : IrredFam (pairOf 6 n1P n2P) :=
  irredFam_of_nortonOK (d := nor6) hm22_norton_checks.1

theorem irredFam_std15 :
    IrredFam (pairOf 15 std15A std15B) :=
  irredFam_of_nortonOK (d := nor15) hm22_norton_checks.2.1

theorem irredFam_std45 :
    IrredFam (pairOf 45 std45A std45B) :=
  irredFam_of_nortonOK (d := nor45) hm22_norton_checks.2.2.1

theorem irredFam_std45c :
    IrredFam (pairOf 45 std45cA std45cB) :=
  irredFam_of_nortonOK (d := nor45c) hm22_norton_checks.2.2.2.1

theorem irredFam_std84 :
    IrredFam (pairOf 84 std84A std84B) :=
  irredFam_of_nortonOK (d := nor84) hm22_norton_checks.2.2.2.2

theorem isLetters_hAW : IsLetters hAW := by
  unfold IsLetters
  decide

theorem isLetters_hBW : IsLetters hBW := by
  unfold IsLetters
  decide

theorem hAW_mem : wordΓ hAW ∈ hatH :=
  CFSG.Quasithin.HM22.wordΓ_mem_hatH isLetters_hAW (by decide +kernel)

theorem hBW_mem : wordΓ hBW ∈ hatH :=
  CFSG.Quasithin.HM22.wordΓ_mem_hatH isLetters_hBW (by decide +kernel)

@[expose] def hA : ↥hatH := Blk.hOf hAW_mem

@[expose] def hB : ↥hatH := Blk.hOf hBW_mem

theorem isIrreducible_rep3a {K : Type*} [Field K]
    (φ : FieldFour →+* K) : (matrixBaseChange φ rep3a).IsIrreducible :=
  SpinData.isIrreducible_of_check φ rep3a (a := hA) (b := hB)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk3a hAW_mem)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk3a hBW_mem) _ hm22_hnorton_checks.1

theorem isIrreducible_rep3b {K : Type*} [Field K]
    (φ : FieldFour →+* K) : (matrixBaseChange φ rep3b).IsIrreducible :=
  SpinData.isIrreducible_of_check φ rep3b (a := hA) (b := hB)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk3b hAW_mem)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk3b hBW_mem) _ hm22_hnorton_checks.2.1

theorem isIrreducible_rep9 {K : Type*} [Field K]
    (φ : FieldFour →+* K) : (matrixBaseChange φ rep9).IsIrreducible :=
  SpinData.isIrreducible_of_check φ rep9 (a := hA) (b := hB)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk9 hAW_mem)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk9 hBW_mem) _ hm22_hnorton_checks.2.2.1

theorem isIrreducible_rep24a {K : Type*} [Field K]
    (φ : FieldFour →+* K) : (matrixBaseChange φ rep24a).IsIrreducible :=
  SpinData.isIrreducible_of_check φ rep24a (a := hA) (b := hB)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk24a hAW_mem)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk24a hBW_mem) _ hm22_hnorton_checks.2.2.2.1

theorem isIrreducible_rep24b {K : Type*} [Field K]
    (φ : FieldFour →+* K) : (matrixBaseChange φ rep24b).IsIrreducible :=
  SpinData.isIrreducible_of_check φ rep24b (a := hA) (b := hB)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk24b hAW_mem)
    (by rw [PM.untab_unpack]; exact Blk.toMat_blk24b hBW_mem) _
    hm22_hnorton_checks.2.2.2.2.1

theorem hABW_mem : wordΓ (hAW ++ hBW) ∈ hatH := by
  rw [wordΓ_append]
  exact hatH.mul_mem hAW_mem hBW_mem

theorem hAABW_mem : wordΓ (hAW ++ hAW ++ hBW) ∈ hatH := by
  rw [wordΓ_append, wordΓ_append]
  exact hatH.mul_mem (hatH.mul_mem hAW_mem hAW_mem) hBW_mem

theorem trace_rep3a_ne :
    Matrix.trace (rep3a (Blk.hOf hABW_mem)) ≠ Matrix.trace (rep3b (Blk.hOf hABW_mem)) := by
  have h := hm22_hnorton_checks.2.2.2.2.2
  simp only [hTraceCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rw [← Blk.toMat_blk3a hABW_mem, ← Blk.toMat_blk3b hABW_mem, ← PM.trace_eq, ← PM.trace_eq]
  exact h.1

theorem trace_rep24a_ne :
    Matrix.trace (rep24a (Blk.hOf hAABW_mem)) ≠ Matrix.trace (rep24b (Blk.hOf hAABW_mem)) := by
  have h := hm22_hnorton_checks.2.2.2.2.2
  simp only [hTraceCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rw [← Blk.toMat_blk24a hAABW_mem, ← Blk.toMat_blk24b hAABW_mem, ← PM.trace_eq, ← PM.trace_eq]
  exact h.2

end CFSG.Quasithin.HM22
