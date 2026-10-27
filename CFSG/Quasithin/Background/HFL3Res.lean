module

public import CFSG.Quasithin.Background.HFL3Quad
public import CFSG.Quasithin.Background.HFL3Cent
public import CFSG.Quasithin.Background.HFL3Four
public import CFSG.Quasithin.Background.HFL3Six

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.H.SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem fix_entries_Q1 (hK : Nat.card K = (2 ^ n) ^ 2) {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx12 : (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    {Y : HMod n K} (hY : rho hK x Y = Y) :
    (x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 1 +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 1 = 0 ∧
      (x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 2 +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 2 = 0 ∧
      ((x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 0 +
          (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 0) +
        bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 0 +
          (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 0) = 0 := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  have h := congrArg mat hY
  rw [mat_rho] at h
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e00 := congrFun (congrFun h 0) 0
  simp only [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.map_apply, x00, x11, x22, x10, x20, x21, hx12, map_zero, map_one, mul_zero, mul_one,
    one_mul, add_zero, zero_add] at e01 e02 e00
  have h01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 1 +
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 1 = 0 := by linear_combination e01
  have h02 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 * mat Y 1 2 +
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 2 = 0 := by linear_combination e02
  refine ⟨h01, h02, ?_⟩
  have hY01 : mat Y 0 1 = bar n (mat Y 1 0) := (herm_apply Y 0 1).symm
  have hY02 : mat Y 0 2 = bar n (mat Y 2 0) := (herm_apply Y 0 2).symm
  rw [map_add, map_mul, map_mul]
  rw [hY01, hY02] at e00
  linear_combination e00 - bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 1) * h01 -
    bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 2) * h02

omit [CharP K 2] in
theorem card_le_of_lin_Q1 {P : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hPU : P ≤ unitriangular 3 K) (hP12 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    {α β : K} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hrel : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 * α +
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 * β = 0) : Nat.card P ≤ Nat.card K := by
  have hinj : ∀ x y : ↥P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = (y : Matrix (Fin 3) (Fin 3) K) 0 1 →
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 = (y : Matrix (Fin 3) (Fin 3) K) 0 2 → x = y :=
    fun x y h1 h2 => Subtype.ext (eq_of_Q1 (hPU x.2) (hPU y.2) (hP12 x x.2) (hP12 y y.2) h1 h2)
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := hαβ.resolve_right (not_not.mpr hβ)
    have h0 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := fun x hx => by
      have := hrel x hx
      rw [hβ, mul_zero, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hα
    refine Nat.card_le_card_of_injective (fun x : ↥P => (x : Matrix (Fin 3) (Fin 3) K) 0 2)
      fun x y h => hinj x y (by rw [h0 x x.2, h0 y y.2]) h
  · refine Nat.card_le_card_of_injective (fun x : ↥P => (x : Matrix (Fin 3) (Fin 3) K) 0 1)
      fun x y h => hinj x y h ?_
    have h1 := hrel x x.2
    have h2 := hrel y y.2
    have h3 : ((x : Matrix (Fin 3) (Fin 3) K) 0 2 - (y : Matrix (Fin 3) (Fin 3) K) 0 2) * β =
        0 := by
      have h' : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = (y : Matrix (Fin 3) (Fin 3) K) 0 1 := h
      linear_combination h1 - h2 - α * h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hβ)

theorem card_le_of_tr_Q1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hP12 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) {α β : K} (hαβ : α ≠ 0 ∨ β ≠ 0)
    (hrel : ∀ x ∈ P, bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 1 * α +
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 * β) = (x : Matrix (Fin 3) (Fin 3) K) 0 1 * α +
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 * β) :
    Nat.card P ≤ Nat.card K * 2 ^ n := by
  have hinj : ∀ x y : ↥P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = (y : Matrix (Fin 3) (Fin 3) K) 0 1 →
      (x : Matrix (Fin 3) (Fin 3) K) 0 2 = (y : Matrix (Fin 3) (Fin 3) K) 0 2 → x = y :=
    fun x y h1 h2 => Subtype.ext (eq_of_Q1 (hPU x.2) (hPU y.2) (hP12 x x.2) (hP12 y y.2) h1 h2)
  rw [← card_fixed hn hK, ← Nat.card_prod]
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := hαβ.resolve_right (not_not.mpr hβ)
    refine Nat.card_le_card_of_injective (fun x : ↥P => ((x : Matrix (Fin 3) (Fin 3) K) 0 2,
      ⟨(x : Matrix (Fin 3) (Fin 3) K) 0 1 * α, by
        have := hrel x x.2
        rwa [hβ, mul_zero, add_zero] at this⟩)) fun x y h => ?_
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact hinj x y (mul_right_cancel₀ hα h.2) h.1
  · refine Nat.card_le_card_of_injective (fun x : ↥P => ((x : Matrix (Fin 3) (Fin 3) K) 0 1,
      ⟨(x : Matrix (Fin 3) (Fin 3) K) 0 1 * α + (x : Matrix (Fin 3) (Fin 3) K) 0 2 * β,
        hrel x x.2⟩)) fun x y h => ?_
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    refine hinj x y h.1 ?_
    have h3 : ((x : Matrix (Fin 3) (Fin 3) K) 0 2 - (y : Matrix (Fin 3) (Fin 3) K) 0 2) * β =
        0 := by
      linear_combination h.2 - α * h.1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hβ)

theorem card_fixV_le_of_Q1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hP12 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (hcard : 2 ^ (3 * n) < Nat.card P) :
    Nat.card ↥(fixV (P.map (rho hK))) ≤ 2 ^ n := by
  have hK2 : Nat.card K < Nat.card P := by
    rw [hK, ← pow_mul]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard
  have hK3 : Nat.card K * 2 ^ n < Nat.card P := by
    rw [hK, ← pow_mul, ← pow_add]
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard
  have key : ∀ Y ∈ fixV (P.map (rho hK)), mat Y 1 1 = 0 ∧ mat Y 2 1 = 0 ∧ mat Y 1 2 = 0 ∧
      mat Y 2 2 = 0 ∧ mat Y 1 0 = 0 ∧ mat Y 2 0 = 0 := by
    intro Y hY
    have hE := fun x (hx : x ∈ P) => fix_entries_Q1 hK (hPU hx) (hP12 x hx) (hY _ ⟨x, hx, rfl⟩)
    have h1 : mat Y 1 1 = 0 ∧ mat Y 2 1 = 0 := by
      by_contra h
      have hne : mat Y 1 1 ≠ 0 ∨ mat Y 2 1 ≠ 0 := by tauto
      exact absurd (card_le_of_lin_Q1 hPU hP12 hne fun x hx => (hE x hx).1) (not_le.mpr hK2)
    have h2 : mat Y 1 2 = 0 ∧ mat Y 2 2 = 0 := by
      by_contra h
      have hne : mat Y 1 2 ≠ 0 ∨ mat Y 2 2 ≠ 0 := by tauto
      exact absurd (card_le_of_lin_Q1 hPU hP12 hne fun x hx => (hE x hx).2.1) (not_le.mpr hK2)
    have h3 : mat Y 1 0 = 0 ∧ mat Y 2 0 = 0 := by
      by_contra h
      have hne : mat Y 1 0 ≠ 0 ∨ mat Y 2 0 ≠ 0 := by tauto
      refine absurd (card_le_of_tr_Q1 hn hK hPU hP12 hne fun x hx => ?_) (not_le.mpr hK3)
      have := (hE x hx).2.2
      rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
      exact this
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩
  let f : ↥(fixV (P.map (rho hK))) → {c : K // bar n c = c} := fun Y =>
    ⟨mat (Y : HMod n K) 0 0, herm_apply (Y : HMod n K) 0 0⟩
  have hf : Function.Injective f := by
    intro Y Y' h
    have h00 : mat (Y : HMod n K) 0 0 = mat (Y' : HMod n K) 0 0 := congrArg Subtype.val h
    obtain ⟨a11, a21, a12, a22, a10, a20⟩ := key Y Y.2
    obtain ⟨b11, b21, b12, b22, b10, b20⟩ := key Y' Y'.2
    have a01 : mat (Y : HMod n K) 0 1 = 0 := by rw [← herm_apply, a10, map_zero]
    have a02 : mat (Y : HMod n K) 0 2 = 0 := by rw [← herm_apply, a20, map_zero]
    have b01 : mat (Y' : HMod n K) 0 1 = 0 := by rw [← herm_apply, b10, map_zero]
    have b02 : mat (Y' : HMod n K) 0 2 = 0 := by rw [← herm_apply, b20, map_zero]
    apply Subtype.ext
    apply mat_injective
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, a11, a21, a12, a22, a10, a20, a01, a02, b11, b21,
      b12, b22, b10, b20, b01, b02]
  have := Nat.card_le_card_of_injective f hf
  rwa [card_fixed hn hK] at this

theorem fix_entries_Q2 (hK : Nat.card K = (2 ^ n) ^ 2) {x : SpecialLinearGroup (Fin 3) K}
    (hx : x ∈ unitriangular 3 K) (hx01 : (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    {Y : HMod n K} (hY : rho hK x Y = Y) :
    (x : Matrix (Fin 3) (Fin 3) K) 0 2 * mat Y 2 2 = 0 ∧
      (x : Matrix (Fin 3) (Fin 3) K) 1 2 * mat Y 2 2 = 0 ∧
      (mat Y 2 2 = 0 →
        mat Y 0 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 0 2) +
            (x : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n (mat Y 0 2) = 0 ∧
          mat Y 1 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 1 2) +
            (x : Matrix (Fin 3) (Fin 3) K) 1 2 * bar n (mat Y 1 2) = 0 ∧
          mat Y 0 2 * bar n ((x : Matrix (Fin 3) (Fin 3) K) 1 2) +
            (x : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n (mat Y 1 2) = 0) := by
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hx
  have h := congrArg mat hY
  rw [mat_rho] at h
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  have e01 := congrFun (congrFun h 0) 1
  simp only [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
    Matrix.map_apply, x00, x11, x22, x10, x20, x21, hx01, map_zero, map_one, mul_zero, mul_one,
    one_mul, add_zero, zero_add] at e02 e12 e00 e11 e01
  have hY20 : mat Y 2 0 = bar n (mat Y 0 2) := (herm_apply Y 2 0).symm
  have hY21 : mat Y 2 1 = bar n (mat Y 1 2) := (herm_apply Y 2 1).symm
  refine ⟨by linear_combination e02, by linear_combination e12, fun h22 => ?_⟩
  rw [hY20, h22] at e00
  rw [hY21, h22] at e11
  rw [hY21, h22] at e01
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e00
  · linear_combination e11
  · linear_combination e01

theorem fixV_eq_blkW_of_Q2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {P : Subgroup (SpecialLinearGroup (Fin 3) K)} (hPU : P ≤ unitriangular 3 K)
    (hP01 : ∀ x ∈ P, (x : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) (hcard : 2 ^ n < Nat.card P) :
    fixV (P.map (rho hK)) = blkW n K := by
  classical
  refine le_antisymm ?_ fun X hX => ?_
  · intro Y hY
    have hE := fun x (hx : x ∈ P) => fix_entries_Q2 hK (hPU hx) (hP01 x hx) (hY _ ⟨x, hx, rfl⟩)
    have hinj : ∀ x y : ↥P,
        (x : Matrix (Fin 3) (Fin 3) K) 0 2 = (y : Matrix (Fin 3) (Fin 3) K) 0 2 →
        (x : Matrix (Fin 3) (Fin 3) K) 1 2 = (y : Matrix (Fin 3) (Fin 3) K) 1 2 → x = y :=
      fun x y h1 h2 => Subtype.ext (eq_of_Q2 (hPU x.2) (hPU y.2) (hP01 x x.2) (hP01 y y.2) h1 h2)
    have h22 : mat Y 2 2 = 0 := by
      by_contra h
      have h0 : ∀ x : ↥P, x = 1 := fun x => hinj x 1
        (by
          have := (hE x x.2).1
          rw [(mul_eq_zero.mp this).resolve_right h]
          simp)
        (by
          have := (hE x x.2).2.1
          rw [(mul_eq_zero.mp this).resolve_right h]
          simp)
      have : Nat.card P ≤ 1 := by
        have : Subsingleton ↥P := ⟨fun x y => (h0 x).trans (h0 y).symm⟩
        exact Finite.card_le_one_iff_subsingleton.2 this
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    have h2 : mat Y 0 2 = 0 ∧ mat Y 1 2 = 0 := by
      by_contra h
      have hne : mat Y 0 2 ≠ 0 ∨ mat Y 1 2 ≠ 0 := by tauto
      have hμ : ∀ x : ↥P, ∃ μ : K, bar n μ = μ ∧
          (x : Matrix (Fin 3) (Fin 3) K) 0 2 = μ * mat Y 0 2 ∧
          (x : Matrix (Fin 3) (Fin 3) K) 1 2 = μ * mat Y 1 2 := by
        intro x
        obtain ⟨e1, e2, e3⟩ := (hE x x.2).2.2 h22
        exact eq_smul_of_quad_entries hK hne e1 e2 e3
      choose μ hμfix hμ1 hμ2 using hμ
      have hf : Function.Injective fun x : ↥P => (⟨μ x, hμfix x⟩ : {c : K // bar n c = c}) := by
        intro x y hxy
        have h' : μ x = μ y := congrArg Subtype.val hxy
        exact hinj x y (by rw [hμ1, hμ1, h']) (by rw [hμ2, hμ2, h'])
      have := Nat.card_le_card_of_injective _ hf
      rw [card_fixed hn hK] at this
      omega
    exact ⟨h2.1, h2.2, h22⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact blkW_le_fixV ⟨hPU hx, hP01 x hx⟩ hK hX

theorem blkW_le_fixV_of_card (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {D : GL (Fin 3) K}
    (hcard : 2 ^ (3 * n) < Nat.card ↥(fixV (Subgroup.zpowers (rhoT hK D)) ⊓ blkW n K)) :
    blkW n K ≤ fixV (Subgroup.zpowers (rhoT hK D)) := by
  set W := fixV (Subgroup.zpowers (rhoT hK D)) ⊓ blkW n K with hW
  have hWsm : ∀ (c : K) (hc : bar n c = c), ∀ X ∈ W, smulH hc X ∈ W := by
    intro c hc X hX
    refine ⟨mem_fixV_zpowers_iff.mpr ?_, smulH_mem_blkW hc hX.2⟩
    rw [rhoT_smulH, mem_fixV_zpowers_iff.mp hX.1]
  intro X hX
  by_contra hXW
  have hXW' : X ∉ W := fun h => hXW h.1
  have h := card_mul_le_of_smulH hn hK (U := blkW n K) (W := W) inf_le_right
    (fun c hc Y hY => smulH_mem_blkW hc hY) hX (fun c hc hc0 hcX => hXW' (by
      have hc' : bar n c⁻¹ = c⁻¹ := by rw [map_inv₀, hc]
      have := hWsm c⁻¹ hc' _ hcX
      have e : smulH hc' (smulH hc X) = X := mat_injective (by
        rw [mat_smulH, mat_smulH, smul_smul, inv_mul_cancel₀ hc0, one_smul])
      rwa [e] at this))
  rw [card_blkW hn hK, hK] at h
  have h4 : ((2 ^ n) ^ 2) ^ 2 = 2 ^ n * 2 ^ (3 * n) := by ring
  rw [h4] at h
  have := Nat.le_of_mul_le_mul_left h (Nat.two_pow_pos n)
  omega

omit [Finite K] [CharP K 2] in
theorem exists_blk_pow (α a b c : K) (k : ℕ) :
    ∃ s : K, !![α, 0, a; 0, α, b; 0, 0, c] ^ k =
      !![α ^ k, 0, a * s; 0, α ^ k, b * s; 0, 0, c ^ k] := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, Matrix.one_fin_three]
    simp
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨α ^ k + s * c, ?_⟩
    rw [pow_succ, hs, Matrix.mul_fin_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

theorem pow_eq_one_of_fix_blkW (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {z : MulAut (HMod n K)} (hz : z ∈ norm hK) (hfix : ∀ X ∈ blkW n K, z X = X) :
    z ^ (2 * (Nat.card K - 1)) = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set p₁ : Fin 3 → K := Pi.single 0 1 with hp₁
  set p₂ : Fin 3 → K := Pi.single 1 1 with hp₂
  have hli : LinearIndependent K ![p₁, p₂] := by
    refine LinearIndependent.pair_iff.mpr fun s t h => ?_
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [hp₁, hp₂] at h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨D, α, rfl, hD₁, hD₂, hα⟩ := eq_rhoT_of_fix_line hn hK hz hli
    (fun c => hfix _ (pt_mem_blkW hK (by simp [hp₁, hp₂])))
    (hfix _ (pt_mem_blkW hK (by simp [hp₂])))
  set M := (D : Matrix (Fin 3) (Fin 3) K) with hM
  have hc₁ : ∀ i, M i 0 = α * p₁ i := by
    intro i
    have := congrFun hD₁ i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp₁] using this
  have hc₂ : ∀ i, M i 1 = α * p₂ i := by
    intro i
    have := congrFun hD₂ i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hp₂] using this
  have hMeta : M = !![α, 0, M 0 2; 0, α, M 1 2; 0, 0, M 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc₁, hc₂, hp₁, hp₂]
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hα
    exact zero_ne_one hα
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp (Units.isUnit D)).ne_zero
  have hc0 : M 2 2 ≠ 0 := by
    intro h0
    apply hdet
    rw [hMeta, Matrix.det_fin_three]
    simp [h0]
  have hQ : Nat.card K - 1 = Fintype.card K - 1 := by rw [Nat.card_eq_fintype_card]
  have hαq : α ^ (Nat.card K - 1) = 1 := by rw [hQ]; exact FiniteField.pow_card_sub_one_eq_one α hα0
  have hcq : M 2 2 ^ (Nat.card K - 1) = 1 := by
    rw [hQ]
    exact FiniteField.pow_card_sub_one_eq_one _ hc0
  obtain ⟨s, hs⟩ := exists_blk_pow α (M 0 2) (M 1 2) (M 2 2) (Nat.card K - 1)
  rw [hαq, hcq] at hs
  have hD : D ^ (2 * (Nat.card K - 1)) = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, ← hM, mul_comm, pow_mul, hMeta, hs, sq, Matrix.mul_fin_three,
      Units.val_one, Matrix.one_fin_three]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination (_ * s) * h2
  rw [← map_pow, hD, map_one]

theorem pow_eq_one_of_large (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ img hK) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ (3 * n) < Nat.card A) {x : MulAut (HMod n K)} (hx : x ∈ norm hK)
    {Z : Subgroup (HMod n K)} (hZA : Z ≤ fixV A) (hZx : Z ≤ fixV (Subgroup.zpowers x))
    (hZ : 2 ^ (3 * n) < Nat.card Z) : x ^ (2 * n * (2 * (Nat.card K - 1))) = 1 := by
  obtain ⟨g, P, hPU, -, hinj, hmap⟩ :=
    exists_conj_uni3 hK (hA.trans (img_le_linImg hK)) (IsElemAbelian2.isPGroup hAe)
  set c := rho hK g with hc
  rw [conj_eq_congrHom] at hmap
  have hAe' := (isElemAbelian2_map_congrHom c).2 hAe
  have hmem : ∀ y ∈ P, rho hK y ∈ A.map (congrHom c) := fun y hy => hmap ▸ ⟨y, hy, rfl⟩
  have hc' : ∀ y ∈ P, ∀ y' ∈ P, y * y' = y' * y := by
    intro y hy y' hy'
    have h1 : rho hK (y * y' * (y' * y)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hAe'.1 _ (hmem y hy) _ (hmem y' hy'),
        mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ (P.mul_mem (P.mul_mem hy hy') (P.inv_mem (P.mul_mem hy' hy)))
      h1)
  have hs : ∀ y ∈ P, y * y = 1 := by
    intro y hy
    refine hinj _ (P.mul_mem hy hy) ?_
    rw [map_mul, ← sq]
    exact hAe'.2 _ (hmem y hy)
  have hcP : Nat.card P = Nat.card A := by
    rw [← card_map_rho_of_inj hK hinj, hmap, card_map_congrHom]
  set Z' := Z.map c.toMonoidHom with hZ'
  have hcZ' : Nat.card Z' = Nat.card Z := Subgroup.card_map_of_injective c.injective
  have hZ'A : Z' ≤ fixV (P.map (rho hK)) := by
    rw [hmap, fixV_map_congrHom]
    exact Subgroup.map_mono hZA
  rcases uni3_cases hPU hc' hs with hQ | hQ
  · have h1 := card_fixV_le_of_Q1 hn hK hPU hQ (hcP ▸ hcard)
    have h2 := (Subgroup.card_le_of_le hZ'A).trans h1
    rw [hcZ'] at h2
    have : 2 ^ n ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hfix := fixV_eq_blkW_of_Q2 hn hK hPU hQ (by
      rw [hcP]
      exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hcard)
    set y := (c * x * c⁻¹) ^ (2 * n) with hy
    have hcN : c ∈ norm hK := Subgroup.le_normalizer ⟨g, rfl⟩
    have hxN : c * x * c⁻¹ ∈ norm hK := mul_mem (mul_mem hcN hx) (inv_mem hcN)
    obtain ⟨D, hD⟩ := pow_mem_linImg hn hK hxN
    have hZ'y : Z' ≤ fixV (Subgroup.zpowers y) := by
      rintro _ ⟨v, hv, rfl⟩
      refine mem_fixV_zpowers_iff.mpr ?_
      have h1 : x v = v := mem_fixV_zpowers_iff.mp (hZx hv)
      have h2 : (c * x * c⁻¹) (c v) = c v := by
        show c (x (c⁻¹ (c v))) = c v
        rw [MulAut.inv_apply_self, h1]
      show ((c * x * c⁻¹) ^ (2 * n)) (c v) = c v
      clear hy hD
      induction (2 * n) with
      | zero => rfl
      | succ j ih => rw [pow_succ, MulAut.mul_apply, h2, ih]
    have hble : blkW n K ≤ fixV (Subgroup.zpowers (rhoT hK D)) := by
      refine blkW_le_fixV_of_card hn hK ?_
      rw [hD]
      have hle : Z' ≤ fixV (Subgroup.zpowers y) ⊓ blkW n K := le_inf hZ'y (hfix ▸ hZ'A)
      exact lt_of_lt_of_le (hcZ' ▸ hZ) (Subgroup.card_le_of_le hle)
    have hyN : y ∈ norm hK := by
      rw [hy]
      exact pow_mem hxN _
    have hy2 := pow_eq_one_of_fix_blkW hn hK hyN fun X hX => by
      have := mem_fixV_zpowers_iff.mp (hble hX)
      rwa [hD] at this
    rw [hy, ← pow_mul, conj_pow, conj_eq_one_iff] at hy2
    exact hy2

end CFSG.Quasithin.H.L3Nine
