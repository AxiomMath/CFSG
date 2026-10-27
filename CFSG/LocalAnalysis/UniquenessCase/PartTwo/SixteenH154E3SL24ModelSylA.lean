module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ModelNA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.GH74.KGroups CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

@[expose] def s16h_orth3Q (v : Orth3) : GF4 :=
  (Multiplicative.toAdd v).1 * (Multiplicative.toAdd v).2.1 +
    (Multiplicative.toAdd v).2.2 ^ 2

theorem s16h_gf4_char_two : CharP GF4 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)

theorem s16h_orth3Q_scal (μ : GF4) (hμ : μ ≠ 0) (v : Orth3) :
    s16h_orth3Q (orth3Scal μ hμ v) = μ ^ 2 * s16h_orth3Q v := by
  have h : orth3Scal μ hμ v = Multiplicative.ofAdd
      (μ * (Multiplicative.toAdd v).1, μ * (Multiplicative.toAdd v).2.1,
        μ * (Multiplicative.toAdd v).2.2) := rfl
  rw [h]
  simp only [s16h_orth3Q, toAdd_ofAdd]
  ring

theorem s16h_orth3Q_phi (v : Orth3) :
    s16h_orth3Q (orth3Phi v) = s16h_orth3Q v ^ 2 := by
  haveI := s16h_gf4_char_two
  have h : orth3Phi v = Multiplicative.ofAdd
      ((Multiplicative.toAdd v).1 ^ 2, (Multiplicative.toAdd v).2.1 ^ 2,
        (Multiplicative.toAdd v).2.2 ^ 2) := rfl
  rw [h]
  simp only [s16h_orth3Q, toAdd_ofAdd]
  have h2 : (2 : GF4) = 0 := CharP.cast_eq_zero GF4 2
  ring_nf
  simp [h2]

theorem s16h_orth3Q_actM :
    ∀ (A : Matrix (Fin 2) (Fin 2) GF4), A.det = 1 → ∀ v : GF4 × GF4 × GF4,
      s16h_orth3Q (Multiplicative.ofAdd (s16h_orth3ActM A v)) =
        s16h_orth3Q (Multiplicative.ofAdd v) := by
  decide +kernel

theorem s16h_orth3Q_act (γ : ↥(StatedSL 2 GF4)) (v : Orth3) :
    s16h_orth3Q (Multiplicative.ofAdd
      (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4) (Multiplicative.toAdd v))) =
      s16h_orth3Q v := by
  rw [s16h_orth3Act_eq]
  exact s16h_orth3Q_actM _ (s16h_det_mem_statedSL γ) _

@[expose] def s16h_orth3Sing : Finset Orth3 :=
  Finset.univ.filter (fun v => v ≠ 1 ∧ s16h_orth3Q v = 0)

theorem s16h_mem_orth3Sing {v : Orth3} :
    v ∈ s16h_orth3Sing ↔ v ≠ 1 ∧ s16h_orth3Q v = 0 := by
  simp [s16h_orth3Sing]

theorem s16h_orth3Sing_card : s16h_orth3Sing.card = 15 := by
  decide +kernel

theorem s16h_orth3Sing_not_mem_Z {v : Orth3} (hv : v ∈ s16h_orth3Sing) : v ∉ orth3Z := by
  rw [s16h_mem_orth3Sing] at hv
  intro hZ
  apply hv.1
  apply Multiplicative.toAdd.injective
  have h1 : (Multiplicative.toAdd v).1 = 0 := hZ.1
  have h2 : (Multiplicative.toAdd v).2.1 = 0 := hZ.2
  have hQ : s16h_orth3Q v = 0 := hv.2
  have hz : (Multiplicative.toAdd v).2.2 = 0 := by
    have h : (Multiplicative.toAdd v).2.2 ^ 2 = 0 := by
      simpa [s16h_orth3Q, h1, h2] using hQ
    exact sq_eq_zero_iff.mp h
  ext <;> simp [h1, h2, hz]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
