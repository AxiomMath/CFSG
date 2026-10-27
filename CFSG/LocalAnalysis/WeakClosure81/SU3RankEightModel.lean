module

public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.LocalAnalysis.WeakClosure81.SU3RankModel
import CFSG.LocalAnalysis.WeakClosure81.SU3RankInvert
import CFSG.LocalAnalysis.WeakClosure81.SU3RankEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

theorem six_le_modCommRank_permSU_swap_of_center {F₀ : Type} [Field F₀] [CharP F₀ 2]
    {ζ : rootsOfUnity (2 ^ 3 + 1) F₀} (hζ : orderOf ζ = 9) {F : Type} [AddCommGroup F]
    [Module (ZMod 2) F] [Finite F] (σ : ↥(StatedSU 3 (2 ^ 3) F₀) →* LGL 2 F)
    (hσ : ∀ x, σ x = 1 → (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀)
    (hZ : ∀ a : rootsOfUnity (2 ^ 3 + 1) F₀, a ^ 3 = 1 → σ (diagSU 3 F₀ (a, a)) = 1) :
    6 ≤ modCommRank (σ (permSU 3 F₀ (Equiv.swap 0 1))) := by
  classical
  let f : rootsOfUnity (2 ^ 3 + 1) F₀ × rootsOfUnity (2 ^ 3 + 1) F₀ →* LGL 2 F :=
    σ.comp (diagSU 3 F₀)
  let a : rootsOfUnity (2 ^ 3 + 1) F₀ := ζ ^ 3
  let b : rootsOfUnity (2 ^ 3 + 1) F₀ := (ζ⁻¹) ^ 3
  let s : LGL 2 F := f (ζ, ζ⁻¹)
  let y : LGL 2 F := s ^ 3
  let x : LGL 2 F := f (ζ, ζ)
  let t : LGL 2 F := σ (permSU 3 F₀ (Equiv.swap 0 1))
  let c : LGL 2 F := σ (permSU 3 F₀ (finRotate 3))
  have hζ9 : ζ ^ 9 = 1 := by
    apply Subtype.ext
    change (ζ : F₀ˣ) ^ 9 = 1
    have h := (mem_rootsOfUnity (2 ^ 3 + 1) (ζ : F₀ˣ)).1 ζ.2
    norm_num at h
    exact h
  have ha3 : a ^ 3 = 1 := by
    rw [show a = ζ ^ 3 from rfl, ← pow_mul, show 3 * 3 = 9 by norm_num, hζ9]
  have hb : b = a⁻¹ := by
    rw [show b = (ζ⁻¹) ^ 3 from rfl, show a = ζ ^ 3 from rfl, inv_pow]
  have hab : a * b = 1 := by rw [hb, mul_inv_cancel]
  have hy_eq : y = f (a, b) := by
    dsimp only [y, s]
    rw [← map_pow, Prod.pow_mk]
  have hy_inv : y⁻¹ = f (b, a) := by
    have h2 : b⁻¹ = a := by rw [hb, inv_inv]
    have h : (a, b)⁻¹ = (b, a) := Prod.ext hb.symm h2
    rw [hy_eq, ← map_inv, h]
  have h6a : (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 6 = a * a := by
    rw [show a = ζ ^ 3 from rfl, ← pow_add]
  have ha6 : a * (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 6 = 1 := by
    rw [show a = ζ ^ 3 from rfl, ← pow_add, show 3 + 6 = 9 by norm_num, hζ9]
  have hb6 : b * (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 6 = a := by
    rw [hb, h6a]
    group
  have hpair_cy : (1, a) = (a, b) * (ζ ^ 6, ζ ^ 6) :=
    Prod.ext ha6.symm hb6.symm
  have h7 : (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 7 = (ζ * ζ)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_two, ← pow_add]
    norm_num
    exact hζ9
  have h73 : (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 7 = ζ * ζ ^ 3 * ζ ^ 3 := by
    rw [show (7 : ℕ) = 1 + 3 + 3 by norm_num, pow_add, pow_add, pow_one]
  have hc1 : (ζ * ζ)⁻¹ = ζ * a * ζ ^ 3 := by
    rw [h7.symm, h73]
  have hc2 : ζ = ζ * b * ζ ^ 3 := by
    rw [hb, show a = ζ ^ 3 from rfl]
    group
  have hpair_cx : ((ζ * ζ)⁻¹, ζ) = (ζ, ζ) * (a, b) * (ζ ^ 3, ζ ^ 3) :=
    Prod.ext hc1 hc2
  have hζ6cubed : (ζ ^ 6 : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 3 = 1 := by
    rw [← pow_mul, show 6 * 3 = 18 by norm_num, show (18 : ℕ) = 9 + 9 by norm_num,
      pow_add, hζ9, one_mul]
  have hker3 : f (ζ ^ 3, ζ ^ 3) = 1 := by
    exact hZ a ha3
  have hker6 : f (ζ ^ 6, ζ ^ 6) = 1 := by
    exact hZ (ζ ^ 6) hζ6cubed
  have h1ab : f (1, a) = f (a, b) := by
    calc f (1, a) = f ((a, b) * (ζ ^ 6, ζ ^ 6)) := by rw [hpair_cy]
      _ = f (a, b) * f (ζ ^ 6, ζ ^ 6) := by rw [map_mul]
      _ = f (a, b) * 1 := by rw [hker6]
      _ = f (a, b) := by rw [mul_one]
  have hconj_swap (p q : rootsOfUnity (2 ^ 3 + 1) F₀) :
      t * f (p, q) * t⁻¹ = f (q, p) := by
    have h := congrArg σ (permSU_swap_mul_diagSU_mul_inv (n := 3) (F₀ := F₀) p q)
    change σ (permSU 3 F₀ (Equiv.swap 0 1)) * σ (diagSU 3 F₀ (p, q)) *
      (σ (permSU 3 F₀ (Equiv.swap 0 1)))⁻¹ = σ (diagSU 3 F₀ (q, p))
    simpa only [map_mul, map_inv] using h
  have hconj_rot (p q : rootsOfUnity (2 ^ 3 + 1) F₀) :
      c * f (p, q) * c⁻¹ = f ((p * q)⁻¹, p) := by
    have h := congrArg σ (permSU_finRotate_mul_diagSU_mul_inv (n := 3) (F₀ := F₀) p q)
    change σ (permSU 3 F₀ (finRotate 3)) * σ (diagSU 3 F₀ (p, q)) *
      (σ (permSU 3 F₀ (finRotate 3)))⁻¹ = σ (diagSU 3 F₀ ((p * q)⁻¹, p))
    simpa only [map_mul, map_inv] using h
  have hty : t * y * t⁻¹ = y⁻¹ := by
    calc t * y * t⁻¹ = t * f (a, b) * t⁻¹ := by rw [hy_eq]
      _ = f (b, a) := hconj_swap a b
      _ = y⁻¹ := hy_inv.symm
  have htx : t * x * t⁻¹ = x := by
    dsimp only [x]
    exact hconj_swap ζ ζ
  have hcy : c * y * c⁻¹ = y := by
    calc c * y * c⁻¹ = c * f (a, b) * c⁻¹ := by rw [hy_eq]
      _ = f ((a * b)⁻¹, a) := hconj_rot a b
      _ = f (1, a) := by rw [hab, inv_one]
      _ = f (a, b) := h1ab
      _ = y := hy_eq.symm
  have hcx : c * x * c⁻¹ = x * y ∨ c * x * c⁻¹ = x * y⁻¹ := by
    left
    calc c * x * c⁻¹ = c * f (ζ, ζ) * c⁻¹ := by simp only [x]
      _ = f ((ζ * ζ)⁻¹, ζ) := hconj_rot ζ ζ
      _ = f ((ζ, ζ) * (a, b) * (ζ ^ 3, ζ ^ 3)) := by rw [hpair_cx]
      _ = (f (ζ, ζ) * f (a, b)) * f (ζ ^ 3, ζ ^ 3) := by rw [map_mul, map_mul]
      _ = (f (ζ, ζ) * f (a, b)) * 1 := by rw [hker3]
      _ = f (ζ, ζ) * f (a, b) := by rw [mul_one]
      _ = x * y := by simp only [x, hy_eq]
  have hy3 : y ^ 3 = 1 := by
    have hb3 : b ^ 3 = 1 := by rw [hb, inv_pow, ha3, inv_one]
    rw [hy_eq, ← map_pow, Prod.pow_mk, ← map_one f]
    exact congrArg f (Prod.ext ha3 hb3)
  have hx3 : x ^ 3 = 1 := by
    dsimp only [x]
    rw [← map_pow, Prod.pow_mk]
    exact hZ a ha3
  have hxs : x * s = s * x := by
    dsimp only [x, s]
    simp only [← map_mul]
    exact congrArg f (mul_comm (ζ, ζ) (ζ, ζ⁻¹))
  have hperm : permSU 3 F₀ (Equiv.swap 0 1) * permSU 3 F₀ (Equiv.swap 0 1) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self 0 1, map_one]
  have ht2 : t * t = 1 := by
    dsimp only [t]
    rw [← map_mul, hperm, map_one]
  have hy1 : y ≠ 1 := by
    intro hy
    rw [hy_eq] at hy
    have hscal : (diagSU 3 F₀ (a, b) : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀ :=
      hσ (diagSU 3 F₀ (a, b)) hy
    rw [diagSU_mem_statedScalars_iff] at hscal
    have hainv : a = a⁻¹ := by
      rw [← hb]
      exact hscal.1
    have haa : a * a = 1 := (eq_inv_iff_mul_eq_one).mp hainv
    have h6 : (ζ : rootsOfUnity (2 ^ 3 + 1) F₀) ^ 6 = 1 := by
      rw [h6a, haa]
    have hdvd : 9 ∣ 6 := by
      rw [← hζ]
      exact orderOf_dvd_of_pow_eq_one h6
    exact absurd hdvd (by norm_num)
  have hy_dvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have hy_ne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have hy_eq3 : orderOf y = 3 := by
    rcases (Nat.dvd_prime (show Nat.Prime 3 by norm_num)).mp hy_dvd with h | h
    · exact absurd h hy_ne1
    · exact h
  have hy_odd : Odd (orderOf y) := by rw [hy_eq3]; norm_num
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hty' : t * y * t = y⁻¹ := by
    calc t * y * t = t * y * t⁻¹ := by rw [htinv]
      _ = y⁻¹ := hty
  have h12 := twelve_le_finrank_range_sub_of_cube (F := F) (y := y) (s := s) (x := x)
    (t := t) (c := c) hy1 hy3 rfl hx3 hxs hty htx hcy hcx
  have hle := finrank_range_sub_le_two_mul_modCommRank (F := F) (t := t) (y := y)
    ht2 hty' hy_odd
  change 6 ≤ modCommRank t
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
