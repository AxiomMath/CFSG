module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Vec
public import CFSG.Quasithin.Vol2.GoldschmidtH11Fix

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} {h : Nat.card F = 2 ^ (2 * a)}

@[expose] noncomputable def rkOne (a : ℕ) (u w : F) : Matrix (Fin 2) (Fin 2) F :=
  !![u * sg a u, u * sg a w; w * sg a u, w * sg a w]

@[expose] noncomputable def e11 (h : Nat.card F = 2 ^ (2 * a)) : HV F a :=
  hermV a h 1 0 0 (map_one _) (map_zero _)

theorem hm_e11 (h : Nat.card F = 2 ^ (2 * a)) : hm a (e11 h) = !![1, 0; 0, 0] := by
  simp [e11, hm_hermV]

theorem hm_actHom_e11 (h : Nat.card F = 2 ^ (2 * a)) (γ : SL(2, F)) :
    hm a (actHom a h γ (e11 h)) = rkOne a ((γ : Matrix (Fin 2) (Fin 2) F) 0 0)
      ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  rw [hm_actHom, hm_e11]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rkOne, frobPow_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem orbit_mem (h : Nat.card F = 2 ^ (2 * a)) (S : Subgroup (HV F a))
    (hS : ∀ γ : SL(2, F), actHom a h γ (e11 h) ∈ S) (u w : F) :
    ∃ v ∈ S, hm a v = rkOne a u w := by
  by_cases hz : u = 0 ∧ w = 0
  · refine ⟨1, S.one_mem, ?_⟩
    rw [hm_one, hz.1, hz.2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [rkOne]
  · have hv : (![u, w] : Fin 2 → F) ≠ 0 := fun hv => hz ⟨by simpa using congrFun hv 0,
      by simpa using congrFun hv 1⟩
    refine ⟨actHom a h (colSL _ hv) (e11 h), hS _, ?_⟩
    rw [hm_actHom_e11]
    have e1 := colSL_mulVec_e1 _ hv
    have h0 := congrFun e1 0
    have h1 := congrFun e1 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    rw [h0, h1]

theorem herm_mem (h : Nat.card F = 2 ^ (2 * a)) (S : Subgroup (HV F a))
    (hS : ∀ γ : SL(2, F), actHom a h γ (e11 h) ∈ S) (ha : 0 < a) (x c y : F) (hx : sg a x = x)
    (hy : sg a y = y) : ∃ v ∈ S, hm a v = !![x, c; sg a c, y] := by
  obtain ⟨θ, hθ⟩ := exists_trace_one a ha h
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨v1, m1, e1⟩ := orbit_mem h S hS 1 (sg a c)
  obtain ⟨v2, m2, e2⟩ := orbit_mem h S hS 1 0
  obtain ⟨v3, m3, e3⟩ := orbit_mem h S hS 0 (sg a c)
  obtain ⟨v4, m4, e4⟩ := orbit_mem h S hS (1 + x * θ) 0
  obtain ⟨v5, m5, e5⟩ := orbit_mem h S hS (x * θ) 0
  obtain ⟨v7, m7, e7⟩ := orbit_mem h S hS 0 (1 + y * θ)
  obtain ⟨v8, m8, e8⟩ := orbit_mem h S hS 0 (y * θ)
  obtain ⟨v9, m9, e9⟩ := orbit_mem h S hS 0 1
  refine ⟨v1 * v2 * v3 * v4 * v5 * v2 * v7 * v8 * v9, ?_, ?_⟩
  · exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem
      (S.mul_mem m1 m2) m3) m4) m5) m2) m7) m8) m9
  · simp only [hm_mul, e1, e2, e3, e4, e5, e7, e8, e9]
    ext i j
    have hxθ : sg a (x * θ) = x * sg a θ := by rw [map_mul, hx]
    have hyθ : sg a (y * θ) = y * sg a θ := by rw [map_mul, hy]
    fin_cases i <;> fin_cases j <;>
      simp [rkOne, map_add, map_one, map_zero, sg_sg a h, hxθ, hyθ]
    · linear_combination x * hθ + (2 + x ^ 2 * θ * sg a θ) * h2
    · linear_combination y * hθ + (1 + sg a c * c + y ^ 2 * θ * sg a θ) * h2

theorem schur (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) (c : MulAut (HV F a))
    (hc : ∀ (γ : SL(2, F)) (v : HV F a), c (actHom a h γ v) = actHom a h γ (c v)) :
    ∃ k : F, sg a k = k ∧ ∀ v : HV F a, hm a (c v) = k • hm a v := by
  obtain ⟨θ, hθ⟩ := exists_trace_one a ha h
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hfixw : ∀ d : F, actHom a h (uSL d) (c (e11 h)) = c (e11 h) := by
    intro d
    rw [← hc]
    congr 1
    exact (actHom_uSL_fix_iff a h (e11 h) d).mpr (by simp [hm_e11])
  have f1 := (actHom_uSL_fix_iff a h (c (e11 h)) 1).mp (hfixw 1)
  have f2 := (actHom_uSL_fix_iff a h (c (e11 h)) θ).mp (hfixw θ)
  set w := c (e11 h) with hw
  have hy0 : hm a w 1 1 = 0 := by simpa using f1.1
  have hc1 : sg a (hm a w 0 1) = hm a w 0 1 := by
    have := f1.2
    simp only [one_mul, map_one, mul_one] at this
    linear_combination this - hm a w 0 1 * h2
  have hc0 : hm a w 0 1 = 0 := by
    have := f2.2
    rw [hc1] at this
    linear_combination this - hm a w 0 1 * hθ
  obtain ⟨k, hkd⟩ : ∃ k, hm a w 0 0 = k := ⟨_, rfl⟩
  have hk : sg a k = k := hkd ▸ hm_entry a w 0 0
  have hMw : hm a w = k • hm a (e11 h) := by
    rw [hm_eq a w, hm_e11, hy0, hc0, map_zero, hkd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨k, hk, ?_⟩
  let S : Subgroup (HV F a) :=
    { carrier := {v | hm a (c v) = k • hm a v}
      one_mem' := by simp [hm_one]
      mul_mem' := fun {v u} hv hu => by
        simp only [Set.mem_ofPred_eq] at hv hu ⊢
        rw [map_mul, hm_mul, hm_mul, hv, hu, smul_add]
      inv_mem' := fun {v} hv => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_inv, hm_inv, hm_inv, hv, smul_neg] }
  have hS : ∀ γ : SL(2, F), actHom a h γ (e11 h) ∈ S := by
    intro γ
    show hm a (c (actHom a h γ (e11 h))) = k • hm a (actHom a h γ (e11 h))
    rw [hc, hm_actHom, hm_actHom, hMw]
    simp
  intro v
  obtain ⟨v', hv', hvv'⟩ := herm_mem h S hS ha (hm a v 0 0) (hm a v 0 1) (hm a v 1 1)
    (hm_entry a v 0 0) (hm_entry a v 1 1)
  have : v' = v := hm_injective a (by rw [hvv']; exact (hm_eq a v).symm)
  rw [this] at hv'
  exact hv'

end CFSG.Quasithin.H11
