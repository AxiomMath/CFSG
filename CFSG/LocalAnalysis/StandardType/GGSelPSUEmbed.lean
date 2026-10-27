module

public import CFSG.LieType.Universal.Unitary.Basic
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.SelectedRoot.SelPSU

open Matrix CFSG.LieType.Universal.Unitary

variable {F : Type*} [Field F] {n : ℕ}

@[expose] def inclM (ι : Fin 2 → Fin n) : Matrix (Fin n) (Fin 2) F :=
  Matrix.of fun x r => if x = ι r then (1 : F) else 0

@[expose] def embM (ι : Fin 2 → Fin n) (B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin n) (Fin n) F :=
  1 + inclM (F := F) ι * (B - 1) * (inclM (F := F) ι)ᵀ

variable {ι : Fin 2 → Fin n}

theorem inclM_transpose_mul (hι : Function.Injective ι) :
    (inclM (F := F) ι)ᵀ * inclM (F := F) ι = 1 := by
  ext b b'
  simp only [inclM, mul_apply, transpose_apply, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (ι b'), ite_eq_left (Finset.mem_univ _), one_apply]
  by_cases h : b = b'
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (hι h'.symm)), ite_eq_right h]

theorem embM_one : embM (F := F) ι (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [embM]

theorem embM_mul (hι : Function.Injective ι) (g h : Matrix (Fin 2) (Fin 2) F) :
    embM ι (g * h) = embM ι g * embM ι h := by
  simp only [embM]
  set P := inclM (F := F) ι
  have hPP : Pᵀ * P = 1 := inclM_transpose_mul hι
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * ((g - 1) * (h - 1)) * Pᵀ := by
    calc P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * (g - 1) * (Pᵀ * P) * (h - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((g - 1) * (h - 1)) * Pᵀ := by
          rw [hPP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : P * (g * h - 1) * Pᵀ = P * (g - 1) * Pᵀ + P * (h - 1) * Pᵀ +
      P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem det_embM (hι : Function.Injective ι) (g : Matrix (Fin 2) (Fin 2) F) :
    (embM ι g).det = g.det := by
  set P := inclM (F := F) ι
  have hPP : Pᵀ * P = 1 := inclM_transpose_mul hι
  rw [embM, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hPP,
    Matrix.mul_one, add_sub_cancel]

@[expose] def embGL (hι : Function.Injective ι) : GL (Fin 2) F →* GL (Fin n) F where
  toFun g :=
    { val := embM ι (g : Matrix (Fin 2) (Fin 2) F)
      inv := embM ι ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      val_inv := by rw [← embM_mul hι, Units.mul_inv, embM_one]
      inv_val := by rw [← embM_mul hι, Units.inv_mul, embM_one] }
  map_one' := Units.ext embM_one
  map_mul' g h := Units.ext (embM_mul hι (g : Matrix (Fin 2) (Fin 2) F) h)

theorem inclM_mul_apply_image (hι : Function.Injective ι)
    (M : Matrix (Fin 2) (Fin 2) F) (x b : Fin 2) :
    (inclM (F := F) ι * M) (ι x) b = M x b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · simp [inclM]
  · intro u _ hu
    rw [inclM, of_apply, ite_eq_right_iff.mpr (fun h => absurd (hι h).symm hu), zero_mul]
  · simp

theorem mul_inclM_transpose_apply_image (hι : Function.Injective ι)
    (M : Matrix (Fin n) (Fin 2) F) (a : Fin n) (y : Fin 2) :
    (M * (inclM (F := F) ι)ᵀ) a (ι y) = M a y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · simp [inclM]
  · intro v _ hv
    rw [transpose_apply, inclM, of_apply, ite_eq_right_iff.mpr (fun h => absurd (hι h).symm hv),
      mul_zero]
  · simp

theorem embM_apply_image (hι : Function.Injective ι)
    (g : Matrix (Fin 2) (Fin 2) F) (x y : Fin 2) :
    embM ι g (ι x) (ι y) = g x y := by
  rw [embM, Matrix.add_apply, mul_inclM_transpose_apply_image hι, inclM_mul_apply_image hι,
    Matrix.sub_apply]
  have : (1 : Matrix (Fin n) (Fin n) F) (ι x) (ι y) = (1 : Matrix (Fin 2) (Fin 2) F) x y := by
    simp [Matrix.one_apply, hι.eq_iff]
  rw [this]
  ring

theorem embM_apply_of_not_mem
    (g : Matrix (Fin 2) (Fin 2) F) {a b : Fin n}
    (h : ¬(a ∈ Set.range ι ∧ b ∈ Set.range ι)) :
    embM ι g a b = (1 : Matrix (Fin n) (Fin n) F) a b := by
  rw [embM, Matrix.add_apply]
  suffices h0 : ((inclM (F := F) ι * (g - 1) * (inclM (F := F) ι)ᵀ :
      Matrix (Fin n) (Fin n) F)) a b = 0 by
    rw [h0, add_zero]
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  rcases not_and_or.1 h with ha | hb
  · have : ((inclM (F := F) ι * (g - 1) : Matrix (Fin n) (Fin 2) F)) a v = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [inclM, of_apply, ite_eq_right_iff.mpr (fun h' => absurd ⟨u, h'.symm⟩ ha), zero_mul]
    rw [this, zero_mul]
  · rw [transpose_apply, inclM, of_apply,
      ite_eq_right_iff.mpr (fun h' => absurd ⟨v, h'.symm⟩ hb), mul_zero]

theorem eq_embM_of_entries (hι : Function.Injective ι) (g : Matrix (Fin 2) (Fin 2) F)
    (M : Matrix (Fin n) (Fin n) F) (h1 : ∀ r s, M (ι r) (ι s) = g r s)
    (h2 : ∀ x y, ¬(x ∈ Set.range ι ∧ y ∈ Set.range ι) →
      M x y = (1 : Matrix (Fin n) (Fin n) F) x y) :
    M = embM ι g := by
  ext x y
  by_cases hxy : x ∈ Set.range ι ∧ y ∈ Set.range ι
  · obtain ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩ := hxy
    rw [h1, embM_apply_image hι]
  · rw [h2 x y hxy, embM_apply_of_not_mem g hxy]

theorem antidiag_mul_apply {m p : ℕ} (M : Matrix (Fin m) (Fin p) F) (x : Fin m) (r : Fin p) :
    ((antidiag m : Matrix (Fin m) (Fin m) F) * M) x r = M (Fin.rev x) r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev x)]
  · simp [antidiag]
  · intro y _ hy
    simp [antidiag, hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_antidiag_apply {m p : ℕ} (M : Matrix (Fin p) (Fin m) F) (x : Fin p) (r : Fin m) :
    (M * (antidiag m : Matrix (Fin m) (Fin m) F)) x r = M x (Fin.rev r) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev r)]
  · simp [antidiag]
  · intro s _ hs
    have hrs : ¬(r = Fin.rev s) := fun h => hs (by rw [h, Fin.rev_rev])
    simp [antidiag, hrs]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem antidiag_mul_inclM (hrev : ∀ r, ι (Fin.rev r) = Fin.rev (ι r)) :
    (antidiag n : Matrix (Fin n) (Fin n) F) * inclM (F := F) ι =
      inclM (F := F) ι * (antidiag 2 : Matrix (Fin 2) (Fin 2) F) := by
  ext x r
  rw [antidiag_mul_apply, mul_antidiag_apply]
  simp only [inclM, of_apply]
  exact if_congr (by rw [hrev]; exact Fin.rev_eq_iff) rfl rfl

theorem inclM_transpose_antidiag (hrev : ∀ r, ι (Fin.rev r) = Fin.rev (ι r)) :
    (inclM (F := F) ι)ᵀ * (antidiag n : Matrix (Fin n) (Fin n) F) =
      (antidiag 2 : Matrix (Fin 2) (Fin 2) F) * (inclM (F := F) ι)ᵀ := by
  ext r y
  rw [mul_antidiag_apply, antidiag_mul_apply]
  simp only [inclM, transpose_apply, of_apply]
  exact if_congr (by rw [hrev]; exact Fin.rev_eq_iff) rfl rfl

theorem conjTr_embM (hι : Function.Injective ι) (σ : F ≃+* F) (B : Matrix (Fin 2) (Fin 2) F) :
    conjTr σ (embM ι B) = embM ι (conjTr σ B) := by
  ext x y
  by_cases hxy : x ∈ Set.range ι ∧ y ∈ Set.range ι
  · obtain ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩ := hxy
    rw [embM_apply_image hι]
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
    rw [embM_apply_image hι]
  · have hyx : ¬(y ∈ Set.range ι ∧ x ∈ Set.range ι) := fun h => hxy ⟨h.2, h.1⟩
    rw [embM_apply_of_not_mem _ hxy]
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
    rw [embM_apply_of_not_mem _ hyx]
    by_cases hxy' : x = y
    · subst hxy'
      simp
    · have hyx' : y ≠ x := fun h => hxy' h.symm
      simp [Matrix.one_apply, hxy', hyx']

theorem embM_isometry (hι : Function.Injective ι) (hrev : ∀ r, ι (Fin.rev r) = Fin.rev (ι r))
    (σ : F ≃+* F) {B : Matrix (Fin 2) (Fin 2) F}
    (hB : conjTr σ B * (antidiag 2 : Matrix (Fin 2) (Fin 2) F) * B = antidiag 2) :
    conjTr σ (embM ι B) * (antidiag n : Matrix (Fin n) (Fin n) F) * embM ι B = antidiag n := by
  set P := inclM (F := F) ι
  set J : Matrix (Fin n) (Fin n) F := antidiag n
  set J' : Matrix (Fin 2) (Fin 2) F := antidiag 2
  have hPP : Pᵀ * P = 1 := inclM_transpose_mul hι
  have hJP : J * P = P * J' := antidiag_mul_inclM hrev
  have hPJ : Pᵀ * J = J' * Pᵀ := inclM_transpose_antidiag hrev
  have hkey : (conjTr σ B - 1) * J' + J' * (B - 1) + (conjTr σ B - 1) * J' * (B - 1) = 0 := by
    have : (conjTr σ B - 1) * J' + J' * (B - 1) + (conjTr σ B - 1) * J' * (B - 1) =
        conjTr σ B * J' * B - J' := by noncomm_ring
    rw [this, hB, sub_self]
  have htr : conjTr σ (embM ι B) = 1 + P * (conjTr σ B - 1) * Pᵀ :=
    (conjTr_embM hι σ B).trans rfl
  rw [htr, embM]
  calc (1 + P * (conjTr σ B - 1) * Pᵀ) * J * (1 + P * (B - 1) * Pᵀ) =
      J + P * (conjTr σ B - 1) * (Pᵀ * J) + (J * P) * (B - 1) * Pᵀ +
        P * (conjTr σ B - 1) * (Pᵀ * J) * P * (B - 1) * Pᵀ := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J + P * ((conjTr σ B - 1) * J' + J' * (B - 1) + (conjTr σ B - 1) * J' * (B - 1)) * Pᵀ := by
        rw [hPJ, hJP]
        have e : P * (conjTr σ B - 1) * (J' * Pᵀ) * P * (B - 1) * Pᵀ =
            P * ((conjTr σ B - 1) * J' * (B - 1)) * Pᵀ := by
          calc P * (conjTr σ B - 1) * (J' * Pᵀ) * P * (B - 1) * Pᵀ =
              P * (conjTr σ B - 1) * J' * (Pᵀ * P) * (B - 1) * Pᵀ := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [e]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
    _ = J := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul, add_zero]

end CFSG.StandardType.SelectedRoot.SelPSU

end
