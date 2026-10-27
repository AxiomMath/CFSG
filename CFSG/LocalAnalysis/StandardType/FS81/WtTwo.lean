module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem wt_two_ite {n : ℕ} {i j : Fin n} (hij : i ≠ j) {a b : ZMod 3}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    wt (fun k => if k = i then a else if k = j then b else 0) = 2 := by
  rw [wt]
  have hf : (Finset.univ.filter fun k =>
      (if k = i then a else if k = j then b else 0) ≠ 0) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hki : k = i
    · simp [hki, ha]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki, hb]
      · simp [hki, hkj]
  rw [hf, Finset.card_pair hij]

theorem wt_single_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) {a b : ZMod 3}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    wt ((Pi.single i a + Pi.single j b : Fin n → ZMod 3)) = 2 := by
  have hite : (Pi.single i a + Pi.single j b : Fin n → ZMod 3) =
      fun k => if k = i then a else if k = j then b else 0 := by
    funext k
    by_cases hki : k = i
    · subst hki
      rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero, if_pos rfl]
    · rw [Pi.add_apply, Pi.single_eq_of_ne hki, zero_add, if_neg hki]
      by_cases hkj : k = j
      · subst hkj
        rw [Pi.single_eq_same, if_pos rfl]
      · rw [Pi.single_eq_of_ne hkj, if_neg hkj]
  rw [hite, wt_two_ite hij ha hb]

theorem wt_single_sub_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) {a b : ZMod 3}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    wt ((Pi.single i a - Pi.single j b : Fin n → ZMod 3)) = 2 := by
  have hneg : (Pi.single i a - Pi.single j b : Fin n → ZMod 3) =
      Pi.single i a + Pi.single j (-b) := by
    rw [sub_eq_add_neg]
    congr 1
    exact (Pi.single_neg (f := fun _ : Fin n => ZMod 3) j b).symm
  rw [hneg, wt_single_add_single hij ha (neg_ne_zero.mpr hb)]

end CFSG.StandardType.FrameRoute.FS81

end
