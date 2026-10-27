module

public import CFSG.Quasithin.Vol2.Ch10SecQ4C1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem entries_of_sq_eq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (a b c d : F)
    (e00 : a * a + b * c = 1) (e01 : a * b + b * d = 0) (e10 : c * a + d * c = 0)
    (hdet : a * d - b * c = 1) : b = 0 ∧ c = 0 ∧ d = a ∧ (a = 1 ∨ a = -1) := by
  have had : a + d ≠ 0 := by
    intro h
    apply h2
    have hd : d = -a := by linear_combination h
    subst hd
    linear_combination -hdet - e00
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right had
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right had
  subst hb hc
  have ha2 : a * a = 1 := by linear_combination e00
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha2; simp at ha2
  have hda : d = a := by
    have : a * (d - a) = 0 := by linear_combination hdet - ha2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  refine ⟨rfl, rfl, hda, ?_⟩
  have : (a - 1) * (a + 1) = 0 := by linear_combination ha2
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem sl2_eq_neg_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hx : x ^ 2 = 1) (hx1 : x ≠ 1) : x = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h'
    exact hp2 this
  have hdet := x.2
  have hm : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) * x = 1 := by
    have := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (y : Matrix (Fin 2) (Fin 2) (ZMod p))) hx
    simpa [sq] using this
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10
  obtain ⟨hb, hc, hda, ha⟩ := entries_of_sq_eq_one h2 _ _ _ _ e00 e01 e10 hdet
  have hxm : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hda]
  rcases ha with h | h
  · exfalso
    apply hx1
    ext i j
    rw [hxm, h, one_smul]
    rfl
  · ext i j
    rw [hxm, h, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    simp

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
