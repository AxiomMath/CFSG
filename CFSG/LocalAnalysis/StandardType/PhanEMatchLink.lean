module

public import CFSG.LieType.RootSystem.Form

import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open CFSG.LieType.RootSystem

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)

private lemma plh_form_single_single (m l : Fin n) :
    form hA (Pi.single m 1) (Pi.single l 1) = symmetrizer hA m * (A m l : ℚ) := by
  rw [form_single_left, Finset.sum_eq_single l]
  · simp
  · intro k _ hk
    simp [Pi.single_apply, hk]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem adj_iff_of_weylAction {v : (coxeterMatrix hA).Group} {i j i' j' : Fin n}
    (hi : weylAction hA v (Pi.single i 1) = Pi.single i' 1)
    (hj : weylAction hA v (Pi.single j 1) = Pi.single j' 1) :
    A i' j' ≠ 0 ↔ A i j ≠ 0 := by
  have h := form_weylAction hA v (Pi.single i 1) (Pi.single j 1)
  rw [hi, hj, toRat_single, toRat_single, toRat_single, toRat_single] at h
  rw [plh_form_single_single hA i' j', plh_form_single_single hA i j] at h
  have hdi' := symmetrizer_pos hA i'
  have hdi := symmetrizer_pos hA i
  constructor
  · intro hne hij
    apply hne
    have hz : (A i' j' : ℚ) = 0 := by
      rw [hij, Int.cast_zero, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hdi')
    exact_mod_cast hz
  · intro hne hij
    apply hne
    have hz : (A i j : ℚ) = 0 := by
      rw [hij, Int.cast_zero, mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hdi)
    exact_mod_cast hz

theorem adj_iff_of_conj {w₀ : (coxeterMatrix hA).Group} {op : Fin n → Fin n} (hw₀ : w₀ * w₀ = 1)
    (hop : ∀ k, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple k * w₀ =
      (coxeterMatrix hA).toCoxeterSystem.simple (op k))
    {i j : Fin n} (hij : i ≠ j) : A (op i) (op j) ≠ 0 ↔ A i j ≠ 0 := by
  let cs := (coxeterMatrix hA).toCoxeterSystem
  have hop_ne : op i ≠ op j := by
    intro h
    refine hij (cs.simple_injective ?_)
    have h1 : cs.simple (op i) = cs.simple (op j) := by rw [h]
    rw [← hop i, ← hop j] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hw₀inv : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀
  have hci : cs.simple (op i) = MulAut.conj w₀ (cs.simple i) := by
    rw [← hop i, MulAut.conj_apply, hw₀inv]
  have hcj : cs.simple (op j) = MulAut.conj w₀ (cs.simple j) := by
    rw [← hop j, MulAut.conj_apply, hw₀inv]
  have horder : orderOf (cs.simple (op i) * cs.simple (op j)) =
      orderOf (cs.simple i * cs.simple j) := by
    rw [hci, hcj, ← (MulAut.conj w₀).map_mul]
    exact MulEquiv.orderOf_eq (MulAut.conj w₀) (cs.simple i * cs.simple j)
  have hM : (coxeterMatrix hA) (op i) (op j) = (coxeterMatrix hA) i j := by
    rw [← cs.orderOf_simple_mul_simple (op i) (op j), horder,
      cs.orderOf_simple_mul_simple i j]
  have h1 : A (op i) (op j) = 0 ↔ (coxeterMatrix hA) (op i) (op j) = 2 :=
    (TauCeti.coxeterMatrixOfCartanMatrix_apply_eq_two_iff A hA.apply_self
      (fun _ _ h => hA.apply_mul_apply_mem_of_ne h) (fun _ _ h => hA.apply_eq_zero_symm h)
      hop_ne).symm
  have h2 : A i j = 0 ↔ (coxeterMatrix hA) i j = 2 :=
    (TauCeti.coxeterMatrixOfCartanMatrix_apply_eq_two_iff A hA.apply_self
      (fun _ _ h => hA.apply_mul_apply_mem_of_ne h) (fun _ _ h => hA.apply_eq_zero_symm h)
      hij).symm
  exact not_congr (by rw [h1, hM, ← h2])

theorem adj_iff_pi {w₀ v : (coxeterMatrix hA).Group} {op π : Fin n → Fin n} {I : Set (Fin n)}
    (hw₀ : w₀ * w₀ = 1)
    (hop : ∀ k, w₀ * (coxeterMatrix hA).toCoxeterSystem.simple k * w₀ =
      (coxeterMatrix hA).toCoxeterSystem.simple (op k))
    (hπ : ∀ i ∈ I, weylAction hA v (Pi.single (op i) 1) = Pi.single (π i) 1)
    {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    A (π i) (π j) ≠ 0 ↔ A i j ≠ 0 := by
  exact (adj_iff_of_weylAction hA (hπ i hi) (hπ j hj)).trans
    (adj_iff_of_conj hA hw₀ hop hij)

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
