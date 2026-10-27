module

public import CFSG.Quasithin.MS93.S37RPts
public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin.JonesParshall

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

@[expose] noncomputable def sd (t : F × F × F) : Fin 2 → F := ![sqrtF t.1, sqrtF t.2.2]

omit [Fintype F] [CharP F 2] in
theorem mv_smul_right (t : F × F × F) (c : F) (x : Fin 2 → F) : mv t (c • x) = c • mv t x := by
  funext i
  fin_cases i <;> simp [mv] <;> ring

theorem vec2_ext {α : Type*} {v w : Fin 2 → α} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

omit [Fintype F] [CharP F 2] in
theorem eq_of_linear {T : (Fin 2 → F) →+ (Fin 2 → F)} (hT : ∀ (l : F) v, T (l • v) = l • T v)
    (v : Fin 2 → F) : T v = v 0 • T ![1, 0] + v 1 • T ![0, 1] := by
  have e : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [e]
  rw [map_add, hT, hT]

omit [Fintype F] in
theorem det_ne_zero_of_linear {T : (Fin 2 → F) →+ (Fin 2 → F)}
    (hT : ∀ (l : F) v, T (l • v) = l • T v) (hinj : Function.Injective T) :
    T ![1, 0] 0 * T ![0, 1] 1 + T ![0, 1] 0 * T ![1, 0] 1 ≠ 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set a := T ![1, 0] 0
  set b := T ![0, 1] 0
  set c := T ![1, 0] 1
  set d := T ![0, 1] 1
  intro hdet
  have hz : ∀ v : Fin 2 → F, T v = 0 → v = 0 := fun v hv => hinj (by rw [hv, map_zero])
  have hval : ∀ v : Fin 2 → F, T v = ![v 0 * a + v 1 * b, v 0 * c + v 1 * d] := fun v => by
    rw [eq_of_linear hT v]
    funext i
    fin_cases i <;> simp [a, b, c, d]
  by_cases hab : a = 0 ∧ b = 0
  · by_cases hcd : c = 0 ∧ d = 0
    · have := hz ![1, 0] (by rw [hval]; simp [hab.1, hab.2, hcd.1, hcd.2])
      exact one_ne_zero (congrFun this 0)
    · have hv := hz ![d, c] (by
        rw [hval]
        refine vec2_ext ?_ ?_
        · simp [hab.1, hab.2]
        · show d * c + c * d = 0
          linear_combination c * d * h2)
      exact hcd ⟨by simpa using congrFun hv 1, by simpa using congrFun hv 0⟩
  · have hv := hz ![b, a] (by
      rw [hval]
      refine vec2_ext ?_ ?_
      · show b * a + a * b = 0
        linear_combination a * b * h2
      · show b * c + a * d = 0
        linear_combination hdet)
    exact hab ⟨by simpa using congrFun hv 1, by simpa using congrFun hv 0⟩

theorem eq_zero_of_semilin (hq : 2 < Fintype.card F) (Φ : (Fin 2 → F) →+ F × F × F)
    (Φ' : (Fin 2 → F) → F × F × F) (Θ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (h1 : ∀ x y, Θ (mv (Φ' x) y) = mv (Φ y) x) {x₀ : Fin 2 → F}
    (hx₀ : ∀ a, ∃ y, mv (Φ y) x₀ = a) (hline : ∀ w : F × F × F, ∃ y, ∀ c : F, Φ y ≠ c • w)
    {B : F} {C'' : F × F × F} (hB : ∀ y, Θ (mv C'' y) = B • sd (Φ y)) : B = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_contra hB0
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one' (F := F)
    (by rw [Nat.card_eq_fintype_card]; exact hq)
  let T : (Fin 2 → F) →+ (Fin 2 → F) :=
    { toFun := fun v => Θ (μ • Θ.symm v)
      map_zero' := by simp
      map_add' := fun v w => by simp [smul_add] }
  have hTv : ∀ v, T v = Θ (μ • Θ.symm v) := fun _ => rfl
  have hTΦ : ∀ x y, T (mv (Φ y) x) = mv (Φ (μ • y)) x := fun x y => by
    rw [hTv, ← h1 x y, AddEquiv.symm_apply_apply, ← mv_smul_right, h1]
  have hTlin : ∀ (l : F) v, T (l • v) = l • T v := fun l v => by
    obtain ⟨y, rfl⟩ := hx₀ v
    rw [← mv_smul_right, hTΦ, hTΦ, mv_smul_right]
  have hTinj : Function.Injective T := fun v w h => by
    rw [hTv, hTv] at h
    have h' := smul_right_injective _ hμ0 (Θ.injective h)
    exact Θ.symm.injective h'
  have hdet := det_ne_zero_of_linear hTlin hTinj
  set a := T ![1, 0] 0
  set b := T ![0, 1] 0
  set c := T ![1, 0] 1
  set d := T ![0, 1] 1
  have hval : ∀ v : Fin 2 → F, T v = ![v 0 * a + v 1 * b, v 0 * c + v 1 * d] := fun v => by
    rw [eq_of_linear hTlin v]
    exact vec2_ext (by simp [a, b]) (by simp [c, d])
  have hS : ∀ s ∈ Set.range Φ, c * s.1 + (a + d) * s.2.1 + b * s.2.2 = 0 ∧
      (a + a ^ 2) * s.1 + b * s.2.1 + b ^ 2 * s.2.2 = 0 ∧
      c ^ 2 * s.1 + c * s.2.1 + (d + d ^ 2) * s.2.2 = 0 := by
    rintro _ ⟨y, rfl⟩
    set C := Φ y
    set C' := Φ (μ • y)
    have k0 := hTΦ ![1, 0] y
    have k1 := hTΦ ![0, 1] y
    rw [hval] at k0 k1
    have e00 : C'.1 = a * C.1 + b * C.2.1 := by
      have := congrFun k0 0
      simp [mv] at this
      linear_combination -this
    have e01 : C'.2.1 = c * C.1 + d * C.2.1 := by
      have := congrFun k0 1
      simp [mv] at this
      linear_combination -this
    have e10 : C'.2.1 = a * C.2.1 + b * C.2.2 := by
      have := congrFun k1 0
      simp [mv] at this
      linear_combination -this
    have e11 : C'.2.2 = c * C.2.1 + d * C.2.2 := by
      have := congrFun k1 1
      simp [mv] at this
      linear_combination -this
    have hsd : sd C' = T (sd C) := by
      have k := hB (μ • y)
      rw [show mv C'' (μ • y) = μ • mv C'' y from mv_smul_right _ _ _,
        show Θ (μ • mv C'' y) = T (Θ (mv C'' y)) by rw [hTv, AddEquiv.symm_apply_apply], hB y,
        hTlin] at k
      exact (smul_right_injective _ hB0 k).symm
    rw [hval] at hsd
    have q0 : sqrtF C'.1 = sqrtF C.1 * a + sqrtF C.2.2 * b := congrFun hsd 0
    have q1 : sqrtF C'.2.2 = sqrtF C.1 * c + sqrtF C.2.2 * d := congrFun hsd 1
    have r0 : C'.1 = C.1 * a ^ 2 + C.2.2 * b ^ 2 := by
      have := congrArg (· ^ 2) q0
      simp only [sqrtF_sq] at this
      rw [this, add_sq, mul_pow, mul_pow, sqrtF_sq, sqrtF_sq]
      linear_combination sqrtF C.1 * a * (sqrtF C.2.2 * b) * h2
    have r1 : C'.2.2 = C.1 * c ^ 2 + C.2.2 * d ^ 2 := by
      have := congrArg (· ^ 2) q1
      simp only [sqrtF_sq] at this
      rw [this, add_sq, mul_pow, mul_pow, sqrtF_sq, sqrtF_sq]
      linear_combination sqrtF C.1 * c * (sqrtF C.2.2 * d) * h2
    refine ⟨?_, ?_, ?_⟩
    · linear_combination e10 - e01 + (a * C.2.1 + b * C.2.2) * h2
    · linear_combination r0 - e00 + (a ^ 2 * C.1 + b ^ 2 * C.2.2) * h2
    · linear_combination r1 - e11 + (c ^ 2 * C.1 + d ^ 2 * C.2.2) * h2
  obtain ⟨ha, hb, hc, hd⟩ := eq_one_of_forms hdet hS (fun w => by
    obtain ⟨y, hy⟩ := hline w
    exact ⟨Φ y, ⟨y, rfl⟩, hy⟩)
  have hid : T ![1, 0] = ![1, 0] := by
    rw [hval]
    exact vec2_ext (by simp [ha]) (by simp [hc])
  rw [hTv] at hid
  have h3 := congrArg Θ.symm hid
  rw [AddEquiv.symm_apply_apply] at h3
  set w := Θ.symm ![1, 0]
  have hw : w ≠ 0 := fun h0 => by
    have : (![1, 0] : Fin 2 → F) = Θ 0 := by rw [← h0]; simp [w]
    rw [map_zero] at this
    exact one_ne_zero (congrFun this 0)
  have : (μ - 1) • w = 0 := by rw [sub_smul, one_smul, h3, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact hμ1 (sub_eq_zero.1 h)
  · exact hw h

end CFSG.Quasithin.MS93.S37R
