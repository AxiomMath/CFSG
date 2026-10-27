module

public import CFSG.Permutation.FiveTransitive.ThreeSwapTwoGroup

public section

namespace CFSG

namespace FiveTransitive.ThreeSwapNormalizerConjugators

theorem conjugate_swap {F : Type*} [DecidableEq F] (g : Equiv.Perm F) (a b : F) :
    g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b) := by
  rw [Equiv.mul_swap_eq_swap_mul, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_conjugators {F : Type*} [DecidableEq F] (e : Fin 6 ↪ F) :
    let t0 := Equiv.swap (e 0) (e 1)
    let t1 := Equiv.swap (e 2) (e 3)
    let t2 := Equiv.swap (e 4) (e 5)
    ∃ a b c : Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)),
      a.val * t0 * a.val⁻¹ = t1 ∧ b.val * t0 * b.val⁻¹ = t2 ∧
      c.val * (t0 * t1) * c.val⁻¹ = t0 * t2 ∧
      b.val * (t0 * t1) * b.val⁻¹ = t1 * t2 := by
  let t0 := Equiv.swap (e 0) (e 1)
  let t1 := Equiv.swap (e 2) (e 3)
  let t2 := Equiv.swap (e 4) (e 5)
  let a := Equiv.swap (e 0) (e 2) * Equiv.swap (e 1) (e 3)
  let b := Equiv.swap (e 0) (e 4) * Equiv.swap (e 1) (e 5)
  let c := Equiv.swap (e 2) (e 4) * Equiv.swap (e 3) (e 5)
  have ha0 : a * t0 * a⁻¹ = t1 := by
    rw [conjugate_swap]
    simp [a, t1, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have ha1 : a * t1 * a⁻¹ = t0 := by
    rw [conjugate_swap]
    simp [a, t0, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have ha2 : a * t2 * a⁻¹ = t2 := by
    rw [conjugate_swap]
    simp [a, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hb0 : b * t0 * b⁻¹ = t2 := by
    rw [conjugate_swap]
    simp [b, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hb1 : b * t1 * b⁻¹ = t1 := by
    rw [conjugate_swap]
    simp [b, t1, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hb2 : b * t2 * b⁻¹ = t0 := by
    rw [conjugate_swap]
    simp [b, t0, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hc0 : c * t0 * c⁻¹ = t0 := by
    rw [conjugate_swap]
    simp [c, t0, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hc1 : c * t1 * c⁻¹ = t2 := by
    rw [conjugate_swap]
    simp [c, t2, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hc2 : c * t2 * c⁻¹ = t1 := by
    rw [conjugate_swap]
    simp [c, t1, Equiv.Perm.mul_apply, Equiv.swap_apply_def, e.injective.eq_iff]
  have hnorm (g : Equiv.Perm F)
      (hset : (MulAut.conj g) '' ({t0, t1, t2} : Set (Equiv.Perm F)) = {t0, t1, t2}) :
      g ∈ Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)) := by
    apply Subgroup.normalizer_le_normalizer_closure
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mpr hset
  have ha : a ∈ Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)) := by
    apply hnorm
    simp only [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, ha0, ha1, ha2]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hb : b ∈ Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)) := by
    apply hnorm
    simp only [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, hb0, hb1, hb2]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hc : c ∈ Subgroup.normalizer (ThreeSwapTwoGroup.subgroup e : Set (Equiv.Perm F)) := by
    apply hnorm
    simp only [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, hc0, hc1, hc2]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have h12 : Commute t1 t2 := (Equiv.Perm.disjoint_swap_swap (by
    have h : ([2, 3, 4, 5] : List (Fin 6)).Nodup := by decide
    simpa only [List.map_cons, List.map_nil] using h.map e.injective)).commute
  refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ha0, hb0, ?_, ?_⟩
  · change MulAut.conj c (t0 * t1) = t0 * t2
    rw [map_mul]
    exact congrArg₂ (· * ·) hc0 hc1
  · change MulAut.conj b (t0 * t1) = t1 * t2
    rw [map_mul]
    exact (congrArg₂ (· * ·) hb0 hb1).trans h12.eq.symm

end FiveTransitive.ThreeSwapNormalizerConjugators

end CFSG
