module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

section GGSL9J7c

variable {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3)

private theorem ggSL9_units_pow_eight (u : (GaloisField 2 3)ˣ) : u ^ 8 = u := by
  rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, ggSL9_units_pow_seven, one_mul, pow_one]

private theorem ggSL9_exp_mul_neg (e : ZMod 3) :
    2 ^ e.val * 2 ^ (-e).val = 8 ∨ 2 ^ e.val * 2 ^ (-e).val = 1 := by
  revert e
  decide

private theorem ggSL9_pow_two_pow_mul_neg (e : ZMod 3) (x : GaloisField 2 3) :
    (x ^ 2 ^ e.val) ^ 2 ^ (-e).val = x := by
  rw [← pow_mul]
  rcases ggSL9_exp_mul_neg e with h | h
  · rw [h, ggSL9_pow_eight]
  · rw [h, pow_one]

private theorem ggSL9_units_pow_two_pow_mul_neg (e : ZMod 3) (u : (GaloisField 2 3)ˣ) :
    (u ^ 2 ^ e.val) ^ 2 ^ (-e).val = u := by
  rw [← pow_mul]
  rcases ggSL9_exp_mul_neg e with h | h
  · rw [h, ggSL9_units_pow_eight]
  · rw [h, pow_one]

private theorem ggSL9_exp_mul_neg' (e : ZMod 3) :
    2 ^ (-e).val * 2 ^ e.val = 8 ∨ 2 ^ (-e).val * 2 ^ e.val = 1 := by
  revert e
  decide

private theorem ggSL9_pow_two_pow_mul_neg' (e : ZMod 3) (x : GaloisField 2 3) :
    (x ^ 2 ^ (-e).val) ^ 2 ^ e.val = x := by
  rw [← pow_mul]
  rcases ggSL9_exp_mul_neg' e with h | h
  · rw [h, ggSL9_pow_eight]
  · rw [h, pow_one]

private theorem ggSL9_fin3_cases {k l : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    l = i ∨ l = j ∨ l = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all

private theorem ggSL9_decomp {k : Fin 3} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (v : GGSL9V) : v = Pi.single i (v i) + Pi.single j (v j) + Pi.single k (v k) := by
  funext l
  rcases ggSL9_fin3_cases hij hki hkj (l := l) with rfl | rfl | rfl
  · simp [Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hki.symm]
  · simp [Pi.single_eq_same, Pi.single_eq_of_ne hij.symm, Pi.single_eq_of_ne hkj.symm]
  · simp [Pi.single_eq_same, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

private theorem ggSL9_exists_third {i j : Fin 3} (hij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> simp_all <;> decide

private noncomputable def ggSL9D1 (i j : Fin 3) (e : ZMod 3) (x : (GaloisField 2 3)ˣ) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  ggSL9Diag (fun l => if l = i then x else if l = j then x ^ 2 ^ e.val else 1)

private noncomputable def ggSL9D2 (k : Fin 3) (y : (GaloisField 2 3)ˣ) :
    GGSL9V ≃ₗ[ZMod 2] GGSL9V :=
  ggSL9Diag (Pi.mulSingle k y)

private theorem ggSL9W_mul_diag_mul_W {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (t : Fin 3 → (GaloisField 2 3)ˣ) :
    ggSL9W i j hij e * ggSL9Diag t * ggSL9W i j hij e =
      ggSL9Diag (fun l => if l = i then t j ^ 2 ^ (-e).val
        else if l = j then t i ^ 2 ^ e.val else t l) := by
  apply LinearEquiv.ext
  intro v
  funext l
  rcases ggSL9_fin3_cases hij hki hkj (l := l) with h | h | h <;> rw [h] <;>
    simp [ggSL9W_apply, ggSL9Diag_apply, mul_pow, ggSL9_pow_two_pow_mul_neg,
      ggSL9_pow_two_pow_mul_neg', Units.val_pow_eq_pow_val, neg_neg, hij, hij.symm,
      hki, hki.symm, hkj, hkj.symm]

private theorem ggSL9W_mul_diag_mul_W_self {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (t : Fin 3 → (GaloisField 2 3)ˣ) (ht : t j = t i ^ 2 ^ e.val) :
    ggSL9W i j hij e * ggSL9Diag t = ggSL9Diag t * ggSL9W i j hij e := by
  have h := ggSL9W_mul_diag_mul_W hij e hki hkj t
  have ht' : (fun l => if l = i then t j ^ 2 ^ (-e).val
      else if l = j then t i ^ 2 ^ e.val else t l) = t := by
    funext l
    rcases ggSL9_fin3_cases hij hki hkj (l := l) with h | h | h
    · rw [h, if_pos rfl, ht]
      exact ggSL9_units_pow_two_pow_mul_neg e (t i)
    · rw [h, if_neg (Ne.symm hij), if_pos rfl, ht]
    · rw [h, if_neg hki, if_neg hkj]
  rw [ht'] at h
  calc ggSL9W i j hij e * ggSL9Diag t
      = ggSL9W i j hij e * ggSL9Diag t * 1 := (mul_one _).symm
    _ = ggSL9W i j hij e * ggSL9Diag t * (ggSL9W i j hij e * ggSL9W i j hij e) := by
          rw [ggSL9W_mul_self]
    _ = (ggSL9W i j hij e * ggSL9Diag t * ggSL9W i j hij e) * ggSL9W i j hij e := by
          group
    _ = ggSL9Diag t * ggSL9W i j hij e := by rw [h]

private theorem ggSL9W_mul_D1 {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (x : (GaloisField 2 3)ˣ) :
    ggSL9W i j hij e * ggSL9D1 i j e x = ggSL9D1 i j e x * ggSL9W i j hij e :=
  ggSL9W_mul_diag_mul_W_self hij e hki hkj
    (fun l => if l = i then x else if l = j then x ^ 2 ^ e.val else 1) (by
      rw [if_neg (Ne.symm hij), if_pos rfl, if_pos rfl])

private theorem ggSL9W_mul_D2 {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (y : (GaloisField 2 3)ˣ) :
    ggSL9W i j hij e * ggSL9D2 k y = ggSL9D2 k y * ggSL9W i j hij e :=
  ggSL9W_mul_diag_mul_W_self hij e hki hkj (Pi.mulSingle k y) (by
    rw [Pi.mulSingle_eq_of_ne (Ne.symm hkj), Pi.mulSingle_eq_of_ne (Ne.symm hki), one_pow])

private theorem ggSL9Diag_mem_torus (t : Fin 3 → (GaloisField 2 3)ˣ) :
    ggSL9Diag t ∈ ggSL9Torus :=
  MonoidHom.mem_range.mpr ⟨t, rfl⟩

private theorem ggSL9D1_mem_E {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (x : (GaloisField 2 3)ˣ) :
    ggSL9D1 i j e x ∈
      {y | y ∈ ggSL9Torus ∧ ggSL9W i j hij e * y = y * ggSL9W i j hij e} :=
  ⟨ggSL9Diag_mem_torus _, ggSL9W_mul_D1 hij e hki hkj x⟩

private theorem ggSL9D2_mem_E {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (y : (GaloisField 2 3)ˣ) :
    ggSL9D2 k y ∈
      {y' | y' ∈ ggSL9Torus ∧ ggSL9W i j hij e * y' = y' * ggSL9W i j hij e} :=
  ⟨ggSL9Diag_mem_torus _, ggSL9W_mul_D2 hij e hki hkj y⟩

private noncomputable def ggSL9E (i j : Fin 3) (hij : i ≠ j) (e : ZMod 3) :
    Subgroup (GGSL9V ≃ₗ[ZMod 2] GGSL9V) :=
  Subgroup.centralizer
    {x | x ∈ ggSL9Torus ∧ ggSL9W i j hij e * x = x * ggSL9W i j hij e}

private theorem ggSL9Zeta_ne_one : ggSL9Zeta ≠ 1 := by
  intro h
  have hord := orderOf_ggSL9Zeta
  rw [h, orderOf_one] at hord
  norm_num at hord

private theorem ggSL9_unit_add_one_ne_zero {y : (GaloisField 2 3)ˣ} (hy : y ≠ 1) :
    (y : GaloisField 2 3) + 1 ≠ 0 := by
  intro h
  exact hy (Units.ext (CharTwo.add_eq_zero.mp h))

private theorem ggSL9_units_mul_inv_pow_val (u : (GaloisField 2 3)ˣ) (n : ℕ) :
    (u : GaloisField 2 3) ^ n * (((u⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ n = 1 := by
  rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]

private theorem ggSL9_scalar_e_mul (u : (GaloisField 2 3)ˣ) (μ : GaloisField 2 3) :
    ((u ^ 2 ^ e.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) *
      (((u⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ 2 ^ e.val * μ = μ := by
  rw [Units.val_pow_eq_pow_val, ggSL9_units_mul_inv_pow_val, one_mul]

private theorem ggSL9_units_cancel (u : (GaloisField 2 3)ˣ) :
    u * ((u ^ 2 ^ e.val)⁻¹) ^ 2 ^ (-e).val = 1 := by
  rw [inv_pow, ggSL9_units_pow_two_pow_mul_neg, mul_inv_cancel]

private theorem ggSL9_scalar_e'_mul (u : (GaloisField 2 3)ˣ) (μ : GaloisField 2 3) :
    (u : GaloisField 2 3) *
      ((((u ^ 2 ^ e.val)⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ 2 ^ (-e).val * μ = μ := by
  have hcoe : (u : GaloisField 2 3) *
      ((((u ^ 2 ^ e.val)⁻¹ : (GaloisField 2 3)ˣ) : GaloisField 2 3)) ^ 2 ^ (-e).val = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ggSL9_units_cancel (e := e), Units.val_one]
  rw [hcoe, one_mul]

private theorem ggSL9_mem_E_diag {y : GGSL9V ≃ₗ[ZMod 2] GGSL9V}
    (hy : y ∈ {x | x ∈ ggSL9Torus ∧ ggSL9W i j hij e * x = x * ggSL9W i j hij e}) :
    ∃ s : Fin 3 → (GaloisField 2 3)ˣ, y = ggSL9Diag s ∧ s j = s i ^ 2 ^ e.val := by
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hy.1
  refine ⟨s, hs.symm, ?_⟩
  have h : ggSL9W i j hij e * ggSL9Diag s = ggSL9Diag s * ggSL9W i j hij e := by
    have hy2 := hy.2
    rw [← hs, ggSL9DiagHom_apply] at hy2
    exact hy2
  have h1 := congrArg (fun (g : GGSL9V ≃ₗ[ZMod 2] GGSL9V) => g (Pi.single i 1) j) h
  simp [ggSL9W_apply, ggSL9Diag_apply, Pi.single_eq_same, Pi.single_eq_of_ne, hij,
    hij.symm] at h1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  exact h1.symm

private theorem ggSL9_root_comm {r : GGSL9V ≃ₗ[ZMod 2] GGSL9V}
    (hr : r ∈ ggSL9RootSet i j e.val ∪ ggSL9RootSet j i (-e).val) : r ∈ ggSL9E i j hij e := by
  unfold ggSL9E
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨s, hys, hs⟩ := ggSL9_mem_E_diag hij e hy
  subst hys
  rcases hr with hr | hr
  · obtain ⟨h', μ, hr⟩ := hr
    subst hr
    have hc := ggSL9Diag_conj_root s h' e.val μ
    rw [hs, ggSL9_scalar_e_mul] at hc
    calc ggSL9Diag s * ggSL9Root i j h' e.val μ
        = ggSL9Diag s * ggSL9Root i j h' e.val μ * 1 := (mul_one _).symm
      _ = ggSL9Diag s * ggSL9Root i j h' e.val μ * ((ggSL9Diag s)⁻¹ * ggSL9Diag s) := by
            rw [inv_mul_cancel]
      _ = (ggSL9Diag s * ggSL9Root i j h' e.val μ * (ggSL9Diag s)⁻¹) * ggSL9Diag s := by
            group
      _ = ggSL9Root i j h' e.val μ * ggSL9Diag s := by rw [hc]
  · obtain ⟨h', μ, hr⟩ := hr
    subst hr
    have hc := ggSL9Diag_conj_root s h' (-e).val μ
    rw [hs, ggSL9_scalar_e'_mul] at hc
    calc ggSL9Diag s * ggSL9Root j i h' (-e).val μ
        = ggSL9Diag s * ggSL9Root j i h' (-e).val μ * 1 := (mul_one _).symm
      _ = ggSL9Diag s * ggSL9Root j i h' (-e).val μ * ((ggSL9Diag s)⁻¹ * ggSL9Diag s) := by
            rw [inv_mul_cancel]
      _ = (ggSL9Diag s * ggSL9Root j i h' (-e).val μ * (ggSL9Diag s)⁻¹) * ggSL9Diag s := by
            group
      _ = ggSL9Root j i h' (-e).val μ * ggSL9Diag s := by rw [hc]

private theorem ggSL9J_le_E : ggSL9J i j e ≤ ggSL9E i j hij e := by
  unfold ggSL9J
  rw [Subgroup.closure_le]
  intro r hr
  exact ggSL9_root_comm hij e hr

private theorem ggSL9_fun_ext3 (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) {f g : GGSL9V}
    (hi : f i = g i) (hj : f j = g j) (hk : f k = g k) : f = g := by
  funext l
  rcases ggSL9_fin3_cases hij hki hkj (l := l) with h | h | h <;> rw [h]
  · exact hi
  · exact hj
  · exact hk

private theorem ggSL9D2_single {k : Fin 3} (y : (GaloisField 2 3)ˣ) (t : GaloisField 2 3) :
    ggSL9D2 k y (Pi.single k t) = Pi.single k ((y : GaloisField 2 3) * t) := by
  funext l
  by_cases hl : l = k
  · subst hl
    rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_same, Pi.single_eq_same, Pi.single_eq_same]
  · rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hl, Units.val_one, one_mul,
      Pi.single_eq_of_ne hl, Pi.single_eq_of_ne hl]

private theorem ggSL9D1_apply (x : (GaloisField 2 3)ˣ) (v : GGSL9V) (l : Fin 3) :
    ggSL9D1 i j e x v l =
      if l = i then (x : GaloisField 2 3) * v l
      else if l = j then ((x ^ 2 ^ e.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * v l
      else v l := by
  rw [ggSL9D1, ggSL9Diag_apply]
  by_cases hli : l = i
  · simp only [if_pos hli]
  · by_cases hlj : l = j
    · simp only [if_neg hli, if_pos hlj]
    · simp only [if_neg hli, if_neg hlj, Units.val_one, one_mul]

private theorem ggSL9D1_single_i (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (x : (GaloisField 2 3)ˣ) (s : GaloisField 2 3) :
    ggSL9D1 i j e x (Pi.single i s) = Pi.single i ((x : GaloisField 2 3) * s) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9D1_apply, if_pos rfl, Pi.single_eq_same, Pi.single_eq_same]
  · rw [ggSL9D1_apply, if_neg (Ne.symm hij), if_pos rfl, Pi.single_eq_of_ne (Ne.symm hij),
      Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
  · rw [ggSL9D1_apply, if_neg hki, if_neg hkj, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hki]

private theorem ggSL9D1_single_j (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (x : (GaloisField 2 3)ˣ) (s : GaloisField 2 3) :
    ggSL9D1 i j e x (Pi.single j s) = Pi.single j
      (((x ^ 2 ^ e.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) * s) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9D1_apply, if_pos rfl, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, mul_zero]
  · rw [ggSL9D1_apply, if_neg (Ne.symm hij), if_pos rfl, Pi.single_eq_same, Pi.single_eq_same]
  · rw [ggSL9D1_apply, if_neg hki, if_neg hkj, Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj]

private theorem ggSL9_eq_single_of_block_zero (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) {v : GGSL9V} (hvi : v i = 0) (hvj : v j = 0) : v = Pi.single k (v k) := by
  funext l
  by_cases hl : l = k
  · subst hl; rw [Pi.single_eq_same]
  · rcases ggSL9_fin3_cases hij hki hkj (l := l) with h | h | h
    · rw [h, hvi, Pi.single_eq_of_ne (Ne.symm hki)]
    · rw [h, hvj, Pi.single_eq_of_ne (Ne.symm hkj)]
    · exact absurd h hl

private theorem ggSL9D2_add_self_of_line {k : Fin 3} (y : (GaloisField 2 3)ˣ)
    (t : GaloisField 2 3) :
    ggSL9D2 k y (Pi.single k t) + Pi.single k t = Pi.single k ((y : GaloisField 2 3) * t + t) := by
  rw [ggSL9D2_single, ← Pi.single_add]

private theorem ggSL9_comm_D1_of_mem {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (x : (GaloisField 2 3)ˣ) :
    c * ggSL9D1 i j e x = ggSL9D1 i j e x * c := by
  unfold ggSL9E at hc
  exact ((Subgroup.mem_centralizer_iff.mp hc) (ggSL9D1 i j e x)
    (ggSL9D1_mem_E hij e hki hkj x)).symm

private theorem ggSL9_comm_D2_of_mem {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (y : (GaloisField 2 3)ˣ) :
    c * ggSL9D2 k y = ggSL9D2 k y * c := by
  unfold ggSL9E at hc
  exact ((Subgroup.mem_centralizer_iff.mp hc) (ggSL9D2 k y)
    (ggSL9D2_mem_E hij e hki hkj y)).symm

private theorem ggSL9_c_apply_of_H {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) {v : GGSL9V} (hv : v k = 0) : (c v) k = 0 := by
  have hcomm := ggSL9_comm_D2_of_mem hij e hc hki hkj ggSL9Zeta
  have hDv : ggSL9D2 k ggSL9Zeta v = v := by
    funext l
    by_cases hl : l = k
    · subst hl; rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_same, hv, mul_zero]
    · rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hl, Units.val_one, one_mul]
  have hcv : c v = ggSL9D2 k ggSL9Zeta (c v) := by
    calc c v = c (ggSL9D2 k ggSL9Zeta v) := by rw [hDv]
      _ = (c * ggSL9D2 k ggSL9Zeta) v := (LinearEquiv.mul_apply c _ v).symm
      _ = (ggSL9D2 k ggSL9Zeta * c) v := by rw [hcomm]
      _ = ggSL9D2 k ggSL9Zeta (c v) := LinearEquiv.mul_apply _ c v
  have hk : (c v) k = (ggSL9Zeta : GaloisField 2 3) * (c v) k := by
    have := congrArg (fun w : GGSL9V => w k) hcv
    simpa [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_same] using this
  have hzero : ((ggSL9Zeta : GaloisField 2 3) - 1) * (c v) k = 0 := by
    rw [sub_mul, one_mul, ← hk, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (Units.ext (sub_eq_zero.mp h)) ggSL9Zeta_ne_one
  · exact h

private theorem ggSL9_c_apply_of_L {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) {v : GGSL9V} (hvi : v i = 0) (hvj : v j = 0) :
    (c v) i = 0 ∧ (c v) j = 0 := by
  have hy := ggSL9_unit_add_one_ne_zero ggSL9Zeta_ne_one
  have hcomm := ggSL9_comm_D2_of_mem hij e hc hki hkj ggSL9Zeta
  set t : GaloisField 2 3 := ((ggSL9Zeta : GaloisField 2 3) + 1)⁻¹ * v k with ht
  have ht' : ((ggSL9Zeta : GaloisField 2 3) + 1) * t = v k := by
    rw [ht, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
  have hv'_sum : ggSL9D2 k ggSL9Zeta (Pi.single k t) + Pi.single k t = Pi.single k (v k) := by
    rw [ggSL9D2_add_self_of_line]
    congr 1
    rw [← ht']
    ring
  have hv_eq : v = Pi.single k (v k) := ggSL9_eq_single_of_block_zero hij hki hkj hvi hvj
  have hv'_eq : ggSL9D2 k ggSL9Zeta (Pi.single k t) + Pi.single k t = v :=
    hv'_sum.trans hv_eq.symm
  have hcv : c v = ggSL9D2 k ggSL9Zeta (c (Pi.single k t)) + c (Pi.single k t) := by
    calc c v = c (ggSL9D2 k ggSL9Zeta (Pi.single k t) + Pi.single k t) := by rw [hv'_eq]
      _ = c (ggSL9D2 k ggSL9Zeta (Pi.single k t)) + c (Pi.single k t) := by rw [map_add]
      _ = (c * ggSL9D2 k ggSL9Zeta) (Pi.single k t) + c (Pi.single k t) := by
            rw [LinearEquiv.mul_apply]
      _ = (ggSL9D2 k ggSL9Zeta * c) (Pi.single k t) + c (Pi.single k t) := by rw [hcomm]
      _ = ggSL9D2 k ggSL9Zeta (c (Pi.single k t)) + c (Pi.single k t) := by
            rw [LinearEquiv.mul_apply]
  constructor
  · have := congrArg (fun w : GGSL9V => w i) hcv
    simpa [Pi.add_apply, ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne (Ne.symm hki), one_mul,
      CharTwo.add_self_eq_zero] using this
  · have := congrArg (fun w : GGSL9V => w j) hcv
    simpa [Pi.add_apply, ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne (Ne.symm hkj), one_mul,
      CharTwo.add_self_eq_zero] using this

private theorem ggSL9D1_c_ei {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (u : (GaloisField 2 3)ˣ) :
    ggSL9D1 i j e u (c (Pi.single i 1)) =
      Pi.single i ((u : GaloisField 2 3) * (c (Pi.single i 1)) i) +
      Pi.single j (((u ^ 2 ^ e.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) *
        (c (Pi.single i 1)) j) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9D1_apply, if_pos rfl, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      add_zero]
  · rw [ggSL9D1_apply, if_neg (Ne.symm hij), if_pos rfl, Pi.add_apply,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add]
  · rw [ggSL9D1_apply, if_neg hki, if_neg hkj, Pi.add_apply, Pi.single_eq_of_ne hki,
      Pi.single_eq_of_ne hkj, add_zero]
    exact ggSL9_c_apply_of_H hij e hc hki hkj (v := Pi.single i 1) (Pi.single_eq_of_ne hki 1)

private theorem ggSL9D1_c_ej {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (u : (GaloisField 2 3)ˣ) :
    ggSL9D1 i j e u (c (Pi.single j 1)) =
      Pi.single i ((u : GaloisField 2 3) * (c (Pi.single j 1)) i) +
      Pi.single j (((u ^ 2 ^ e.val : (GaloisField 2 3)ˣ) : GaloisField 2 3) *
        (c (Pi.single j 1)) j) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9D1_apply, if_pos rfl, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      add_zero]
  · rw [ggSL9D1_apply, if_neg (Ne.symm hij), if_pos rfl, Pi.add_apply,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add]
  · rw [ggSL9D1_apply, if_neg hki, if_neg hkj, Pi.add_apply, Pi.single_eq_of_ne hki,
      Pi.single_eq_of_ne hkj, add_zero]
    exact ggSL9_c_apply_of_H hij e hc hki hkj (v := Pi.single j 1) (Pi.single_eq_of_ne hkj 1)

private theorem ggSL9_c_single_i {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (s : GaloisField 2 3) :
    c (Pi.single i s) = Pi.single i (s * (c (Pi.single i 1)) i) +
      Pi.single j (s ^ 2 ^ e.val * (c (Pi.single i 1)) j) := by
  by_cases hs : s = 0
  · subst hs; simp [Pi.single_zero]
  · have hcomm := ggSL9_comm_D1_of_mem hij e hc hki hkj (Units.mk0 s hs)
    have hD1 : ggSL9D1 i j e (Units.mk0 s hs) (Pi.single i 1) = Pi.single i s := by
      rw [ggSL9D1_single_i (e := e) (hij := hij) (hki := hki) (hkj := hkj), mul_one,
        Units.val_mk0]
    calc c (Pi.single i s)
        = c (ggSL9D1 i j e (Units.mk0 s hs) (Pi.single i 1)) := by rw [hD1]
      _ = (c * ggSL9D1 i j e (Units.mk0 s hs)) (Pi.single i 1) :=
            (LinearEquiv.mul_apply c _ _).symm
      _ = (ggSL9D1 i j e (Units.mk0 s hs) * c) (Pi.single i 1) := by rw [hcomm]
      _ = ggSL9D1 i j e (Units.mk0 s hs) (c (Pi.single i 1)) := LinearEquiv.mul_apply _ c _
      _ = Pi.single i (s * (c (Pi.single i 1)) i) +
            Pi.single j (s ^ 2 ^ e.val * (c (Pi.single i 1)) j) := by
            rw [ggSL9D1_c_ei hij e hc hki hkj, Units.val_pow_eq_pow_val, Units.val_mk0]

private theorem ggSL9_c_single_j {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (s : GaloisField 2 3) :
    c (Pi.single j s) = Pi.single i (s ^ 2 ^ (-e).val * (c (Pi.single j 1)) i) +
      Pi.single j (s * (c (Pi.single j 1)) j) := by
  by_cases hs : s = 0
  · subst hs; simp [Pi.single_zero]
  · have hcomm := ggSL9_comm_D1_of_mem hij e hc hki hkj ((Units.mk0 s hs) ^ 2 ^ (-e).val)
    have hu : ((((Units.mk0 s hs) ^ 2 ^ (-e).val) ^ 2 ^ e.val :
        (GaloisField 2 3)ˣ) : GaloisField 2 3) = s := by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul]
      rcases ggSL9_exp_mul_neg' e with h | h
      · rw [h, ggSL9_pow_eight, Units.val_mk0]
      · rw [h, pow_one, Units.val_mk0]
    have hu' : (((Units.mk0 s hs) ^ 2 ^ (-e).val : (GaloisField 2 3)ˣ) :
        GaloisField 2 3) = s ^ 2 ^ (-e).val := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    have hD1 : ggSL9D1 i j e ((Units.mk0 s hs) ^ 2 ^ (-e).val) (Pi.single j 1) =
        Pi.single j s := by
      rw [ggSL9D1_single_j (e := e) (hij := hij) (hki := hki) (hkj := hkj), mul_one, hu]
    calc c (Pi.single j s)
        = c (ggSL9D1 i j e ((Units.mk0 s hs) ^ 2 ^ (-e).val) (Pi.single j 1)) := by rw [hD1]
      _ = (c * ggSL9D1 i j e ((Units.mk0 s hs) ^ 2 ^ (-e).val)) (Pi.single j 1) :=
            (LinearEquiv.mul_apply c _ _).symm
      _ = (ggSL9D1 i j e ((Units.mk0 s hs) ^ 2 ^ (-e).val) * c) (Pi.single j 1) := by
            rw [hcomm]
      _ = ggSL9D1 i j e ((Units.mk0 s hs) ^ 2 ^ (-e).val) (c (Pi.single j 1)) :=
            LinearEquiv.mul_apply _ c _
      _ = Pi.single i (s ^ 2 ^ (-e).val * (c (Pi.single j 1)) i) +
            Pi.single j (s * (c (Pi.single j 1)) j) := by
            rw [ggSL9D1_c_ej hij e hc hki hkj, hu', hu]

private theorem ggSL9_c_single_k {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (s : GaloisField 2 3) :
    c (Pi.single k s) = Pi.single k (s * (c (Pi.single k 1)) k) := by
  by_cases hs : s = 0
  · subst hs; simp [Pi.single_zero]
  · have hL := ggSL9_c_apply_of_L hij e hc hki hkj (v := Pi.single k 1)
      (Pi.single_eq_of_ne hki.symm 1) (Pi.single_eq_of_ne hkj.symm 1)
    have hcomm := ggSL9_comm_D2_of_mem hij e hc hki hkj (Units.mk0 s hs)
    have hD2 : ggSL9D2 k (Units.mk0 s hs) (Pi.single k 1) = Pi.single k s := by
      rw [ggSL9D2_single, mul_one, Units.val_mk0]
    calc c (Pi.single k s)
        = c (ggSL9D2 k (Units.mk0 s hs) (Pi.single k 1)) := by rw [hD2]
      _ = (c * ggSL9D2 k (Units.mk0 s hs)) (Pi.single k 1) :=
            (LinearEquiv.mul_apply c _ _).symm
      _ = (ggSL9D2 k (Units.mk0 s hs) * c) (Pi.single k 1) := by rw [hcomm]
      _ = ggSL9D2 k (Units.mk0 s hs) (c (Pi.single k 1)) := LinearEquiv.mul_apply _ c _
      _ = ggSL9D2 k (Units.mk0 s hs) (Pi.single k ((c (Pi.single k 1)) k)) := by
            conv_lhs => rw [ggSL9_eq_single_of_block_zero hij hki hkj hL.1 hL.2]
      _ = Pi.single k (s * (c (Pi.single k 1)) k) := by
            rw [ggSL9D2_single, Units.val_mk0]

private theorem ggSL9BlockFun_apply_i (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
    (v : GGSL9V) :
    ggSL9BlockFun i j e M v i = M 0 0 * v i + M 0 1 * v j ^ 2 ^ (-e).val := by
  simp [ggSL9BlockFun]

private theorem ggSL9BlockFun_apply_j (hij : i ≠ j) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
    (v : GGSL9V) :
    ggSL9BlockFun i j e M v j = (M 1 0 * v i + M 1 1 * v j ^ 2 ^ (-e).val) ^ 2 ^ e.val := by
  simp [ggSL9BlockFun, hij, hij.symm]

private theorem ggSL9BlockFun_apply_k {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j)
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (v : GGSL9V) :
    ggSL9BlockFun i j e M v k = v k := by
  simp [ggSL9BlockFun, hki, hkj]

private theorem ggSL9_c_eq_block {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) :
    ∃ (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (lam : (GaloisField 2 3)ˣ),
      ∀ v : GGSL9V, c v = ggSL9BlockFun i j e N (ggSL9Diag (Pi.mulSingle k lam) v) := by
  have hL := ggSL9_c_apply_of_L hij e hc hki hkj (v := Pi.single k 1)
    (Pi.single_eq_of_ne hki.symm 1) (Pi.single_eq_of_ne hkj.symm 1)
  set lf : GaloisField 2 3 := (c (Pi.single k 1)) k with hlf
  have hεk : c (Pi.single k 1) = Pi.single k lf := by
    rw [hlf]
    exact ggSL9_eq_single_of_block_zero hij hki hkj hL.1 hL.2
  have hlne : lf ≠ 0 := by
    intro h0
    have hz : c (Pi.single k (1 : GaloisField 2 3)) = 0 := by rw [hεk, h0, Pi.single_zero]
    have hεne : (Pi.single k (1 : GaloisField 2 3) : GGSL9V) ≠ 0 := by
      intro h
      have h1 := congrArg (fun w : GGSL9V => w k) h
      rw [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    exact hεne (c.injective (by rw [hz, map_zero]))
  let lu : (GaloisField 2 3)ˣ := Units.mk0 lf hlne
  have hlu : (lu : GaloisField 2 3) = lf := Units.val_mk0 hlne
  let N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3) :=
    !![(c (Pi.single i 1)) i, (c (Pi.single j 1)) i;
       ((c (Pi.single i 1)) j) ^ 2 ^ (-e).val, ((c (Pi.single j 1)) j) ^ 2 ^ (-e).val]
  have hN00 : N 0 0 = (c (Pi.single i 1)) i := rfl
  have hN01 : N 0 1 = (c (Pi.single j 1)) i := rfl
  have hN10 : N 1 0 = ((c (Pi.single i 1)) j) ^ 2 ^ (-e).val := rfl
  have hN11 : N 1 1 = ((c (Pi.single j 1)) j) ^ 2 ^ (-e).val := rfl
  refine ⟨N, lu, fun v => ?_⟩
  have hci := ggSL9_c_single_i hij e hc hki hkj (v i)
  have hcj := ggSL9_c_single_j hij e hc hki hkj (v j)
  have hck := ggSL9_c_single_k hij e hc hki hkj (v k)
  have hsq : (((c (Pi.single i 1)) j) ^ 2 ^ (-e).val * v i +
      ((c (Pi.single j 1)) j) ^ 2 ^ (-e).val * (v j) ^ 2 ^ (-e).val) ^ 2 ^ e.val =
      (c (Pi.single i 1)) j * (v i) ^ 2 ^ e.val + (c (Pi.single j 1)) j * v j := by
    rw [add_pow_char_pow]
    simp only [mul_pow, ggSL9_pow_two_pow_mul_neg' e]
  have hwi : (ggSL9Diag (Pi.mulSingle k lu) v) i = v i := by
    rw [ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hki.symm, Units.val_one, one_mul]
  have hwj : (ggSL9Diag (Pi.mulSingle k lu) v) j = v j := by
    rw [ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hkj.symm, Units.val_one, one_mul]
  have hwk : (ggSL9Diag (Pi.mulSingle k lu) v) k = lf * v k := by
    rw [ggSL9Diag_apply, Pi.mulSingle_eq_same, hlu]
  have hcv : c v =
      ((Pi.single i (v i * (c (Pi.single i 1)) i) +
          Pi.single j ((v i) ^ 2 ^ e.val * (c (Pi.single i 1)) j)) +
        (Pi.single i ((v j) ^ 2 ^ (-e).val * (c (Pi.single j 1)) i) +
          Pi.single j (v j * (c (Pi.single j 1)) j))) +
        Pi.single k (v k * lf) := by
    conv_lhs => rw [ggSL9_decomp hij hki hkj v]
    rw [map_add, map_add, hci, hcj, hck, ← hlf]
  rw [hcv]
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9BlockFun_apply_i, hwi, hwj]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hki.symm,
      Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj.symm, add_zero, zero_add,
      hN00, hN01, hN10, hN11]
    ring
  · rw [ggSL9BlockFun_apply_j e hij, hwi, hwj]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hki.symm,
      Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj.symm, add_zero, zero_add,
      hN00, hN01, hN10, hN11]
    rw [hsq]
    ring
  · rw [ggSL9BlockFun_apply_k e hki hkj, hwk]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
      Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hki.symm,
      Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne hkj.symm, add_zero, zero_add]
    ring

private theorem ggSL9D2_apply_i {k : Fin 3} (hki : k ≠ i) (y : (GaloisField 2 3)ˣ) (u : GGSL9V) :
    (ggSL9D2 k y u) i = u i := by
  rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hki.symm, Units.val_one, one_mul]

private theorem ggSL9D2_apply_j {k : Fin 3} (hkj : k ≠ j) (y : (GaloisField 2 3)ˣ) (u : GGSL9V) :
    (ggSL9D2 k y u) j = u j := by
  rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hkj.symm, Units.val_one, one_mul]

private theorem ggSL9D2_apply_k {k : Fin 3} (y : (GaloisField 2 3)ˣ) (u : GGSL9V) :
    (ggSL9D2 k y u) k = (y : GaloisField 2 3) * u k := by
  rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_same]

private theorem ggSL9D2_BlockFun (e : ZMod 3) (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) (y : (GaloisField 2 3)ˣ) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3))
    (v : GGSL9V) :
    ggSL9D2 k y (ggSL9BlockFun i j e M v) = ggSL9BlockFun i j e M (ggSL9D2 k y v) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · rw [ggSL9D2_apply_i hki, ggSL9BlockFun_apply_i, ggSL9BlockFun_apply_i, ggSL9D2_apply_i hki,
      ggSL9D2_apply_j hkj]
  · rw [ggSL9D2_apply_j hkj, ggSL9BlockFun_apply_j e hij, ggSL9BlockFun_apply_j e hij,
      ggSL9D2_apply_i hki, ggSL9D2_apply_j hkj]
  · rw [ggSL9D2_apply_k, ggSL9BlockFun_apply_k e hki hkj, ggSL9BlockFun_apply_k e hki hkj,
      ggSL9D2_apply_k]

private theorem ggSL9D2_BlockGL (e : ZMod 3) (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) (y : (GaloisField 2 3)ˣ) (M : GL (Fin 2) (GaloisField 2 3)) :
    ggSL9D2 k y * ggSL9BlockGL i j hij e M = ggSL9BlockGL i j hij e M * ggSL9D2 k y := by
  apply LinearEquiv.ext; intro v
  exact ggSL9D2_BlockFun e hij hki hkj y (M : Matrix _ _ _) v

private theorem ggSL9D2_single_i {k : Fin 3} (hki : k ≠ i) (y : (GaloisField 2 3)ˣ) :
    ggSL9D2 k y (Pi.single i 1) = Pi.single i 1 := by
  funext l
  by_cases hl : l = k
  · subst hl
    rw [ggSL9D2_apply_k, Pi.single_eq_of_ne hki, mul_zero]
  · rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hl, Units.val_one, one_mul]

private theorem ggSL9D2_single_j {k : Fin 3} (hkj : k ≠ j) (y : (GaloisField 2 3)ˣ) :
    ggSL9D2 k y (Pi.single j 1) = Pi.single j 1 := by
  funext l
  by_cases hl : l = k
  · subst hl
    rw [ggSL9D2_apply_k, Pi.single_eq_of_ne hkj, mul_zero]
  · rw [ggSL9D2, ggSL9Diag_apply, Pi.mulSingle_eq_of_ne hl, Units.val_one, one_mul]

private theorem ggSL9BlockFun_single_i (e : ZMod 3) (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single i 1) =
      Pi.single i (M 0 0) + Pi.single j ((M 1 0) ^ 2 ^ e.val) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · simp [ggSL9BlockFun_apply_i, Pi.single_eq_of_ne, hij, hij.symm]
  · simp [ggSL9BlockFun_apply_j e hij, Pi.single_eq_of_ne, hij, hij.symm]
  · simp [ggSL9BlockFun_apply_k e hki hkj, Pi.single_eq_of_ne, hki, hkj]

private theorem ggSL9BlockFun_single_j (e : ZMod 3) (hij : i ≠ j) {k : Fin 3} (hki : k ≠ i)
    (hkj : k ≠ j) (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ggSL9BlockFun i j e M (Pi.single j 1) =
      Pi.single i (M 0 1) + Pi.single j ((M 1 1) ^ 2 ^ e.val) := by
  apply ggSL9_fun_ext3 hij hki hkj
  · simp [ggSL9BlockFun_apply_i, Pi.single_eq_of_ne, hij, hij.symm]
  · simp [ggSL9BlockFun_apply_j e hij, Pi.single_eq_of_ne, hij, hij.symm]
  · simp [ggSL9BlockFun_apply_k e hki hkj, Pi.single_eq_of_ne, hki, hkj]

private theorem ggSL9_det_isUnit {c : GGSL9V ≃ₗ[ZMod 2] GGSL9V} (hc : c ∈ ggSL9E i j hij e)
    {k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) :
    ∃ (N : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (lam : (GaloisField 2 3)ˣ),
      IsUnit N.det ∧
        ∀ v : GGSL9V, c v = ggSL9BlockFun i j e N (ggSL9Diag (Pi.mulSingle k lam) v) := by
  obtain ⟨N₁, lu₁, h₁⟩ := ggSL9_c_eq_block hij e hc hki hkj
  obtain ⟨N₂, lu₂, h₂⟩ := ggSL9_c_eq_block hij e (Subgroup.inv_mem _ hc) hki hkj
  have h₂i : c⁻¹ (Pi.single i 1) = ggSL9BlockFun i j e N₂ (Pi.single i 1) := by
    have h := h₂ (Pi.single i 1)
    rwa [show ggSL9Diag (Pi.mulSingle k lu₂) (Pi.single i 1) = Pi.single i 1 from
      ggSL9D2_single_i hki lu₂] at h
  have h₂j : c⁻¹ (Pi.single j 1) = ggSL9BlockFun i j e N₂ (Pi.single j 1) := by
    have h := h₂ (Pi.single j 1)
    rwa [show ggSL9Diag (Pi.mulSingle k lu₂) (Pi.single j 1) = Pi.single j 1 from
      ggSL9D2_single_j hkj lu₂] at h
  have hfixi : Pi.single i 1 = ggSL9BlockFun i j e (N₁ * N₂) (Pi.single i 1) := by
    calc Pi.single i 1 = c (c⁻¹ (Pi.single i 1)) := by simp
      _ = c (ggSL9BlockFun i j e N₂ (Pi.single i 1)) := by rw [h₂i]
      _ = ggSL9BlockFun i j e N₁ (ggSL9Diag (Pi.mulSingle k lu₁)
            (ggSL9BlockFun i j e N₂ (Pi.single i 1))) := h₁ _
      _ = ggSL9BlockFun i j e N₁ (ggSL9BlockFun i j e N₂
            (ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single i 1))) := by
            rw [show ggSL9Diag (Pi.mulSingle k lu₁)
                (ggSL9BlockFun i j e N₂ (Pi.single i 1)) =
                ggSL9BlockFun i j e N₂ (ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single i 1)) from
                ggSL9D2_BlockFun e hij hki hkj lu₁ N₂ (Pi.single i 1)]
      _ = ggSL9BlockFun i j e N₁ (ggSL9BlockFun i j e N₂ (Pi.single i 1)) := by
            rw [show ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single i 1) = Pi.single i 1 from
              ggSL9D2_single_i hki lu₁]
      _ = ggSL9BlockFun i j e (N₁ * N₂) (Pi.single i 1) :=
            (ggSL9BlockFun_mul hij e N₁ N₂ (Pi.single i 1)).symm
  have hfixj : Pi.single j 1 = ggSL9BlockFun i j e (N₁ * N₂) (Pi.single j 1) := by
    calc Pi.single j 1 = c (c⁻¹ (Pi.single j 1)) := by simp
      _ = c (ggSL9BlockFun i j e N₂ (Pi.single j 1)) := by rw [h₂j]
      _ = ggSL9BlockFun i j e N₁ (ggSL9Diag (Pi.mulSingle k lu₁)
            (ggSL9BlockFun i j e N₂ (Pi.single j 1))) := h₁ _
      _ = ggSL9BlockFun i j e N₁ (ggSL9BlockFun i j e N₂
            (ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single j 1))) := by
            rw [show ggSL9Diag (Pi.mulSingle k lu₁)
                (ggSL9BlockFun i j e N₂ (Pi.single j 1)) =
                ggSL9BlockFun i j e N₂ (ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single j 1)) from
                ggSL9D2_BlockFun e hij hki hkj lu₁ N₂ (Pi.single j 1)]
      _ = ggSL9BlockFun i j e N₁ (ggSL9BlockFun i j e N₂ (Pi.single j 1)) := by
            rw [show ggSL9Diag (Pi.mulSingle k lu₁) (Pi.single j 1) = Pi.single j 1 from
              ggSL9D2_single_j hkj lu₁]
      _ = ggSL9BlockFun i j e (N₁ * N₂) (Pi.single j 1) :=
            (ggSL9BlockFun_mul hij e N₁ N₂ (Pi.single j 1)).symm
  have h00 : (N₁ * N₂) 0 0 = 1 := by
    have h := congrArg (fun w : GGSL9V => w i)
      (hfixi.trans (ggSL9BlockFun_single_i e hij hki hkj (N₁ * N₂)))
    simpa [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
      add_zero] using h.symm
  have h10 : (N₁ * N₂) 1 0 = 0 := by
    have h := congrArg (fun w : GGSL9V => w j)
      (hfixi.trans (ggSL9BlockFun_single_i e hij hki hkj (N₁ * N₂)))
    have h2 : ((N₁ * N₂) 1 0) ^ 2 ^ e.val = 0 := by
      simpa [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        zero_add] using h.symm
    have hp := congrArg (fun x : GaloisField 2 3 => x ^ 2 ^ (-e).val) h2
    simpa [ggSL9_pow_two_pow_mul_neg] using hp
  have h01 : (N₁ * N₂) 0 1 = 0 := by
    have h := congrArg (fun w : GGSL9V => w i)
      (hfixj.trans (ggSL9BlockFun_single_j e hij hki hkj (N₁ * N₂)))
    simpa [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
      add_zero] using h.symm
  have h11 : (N₁ * N₂) 1 1 = 1 := by
    have h := congrArg (fun w : GGSL9V => w j)
      (hfixj.trans (ggSL9BlockFun_single_j e hij hki hkj (N₁ * N₂)))
    have h2 : ((N₁ * N₂) 1 1) ^ 2 ^ e.val = 1 := by
      simpa [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
        zero_add] using h.symm
    have hp := congrArg (fun x : GaloisField 2 3 => x ^ 2 ^ (-e).val) h2
    simpa [ggSL9_pow_two_pow_mul_neg] using hp
  have hmul : N₁ * N₂ = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.one_apply, h00, h01, h10, h11]
  exact ⟨N₁, lu₁, Matrix.isUnit_det_of_right_inverse hmul, h₁⟩

end GGSL9J7c

theorem isComponentOf_ggSL9J {i j : Fin 3} (hij : i ≠ j) (e : ZMod 3) :
    CFSG.Assembly.IsComponentOf (ggSL9J i j e) (Subgroup.centralizer
      {x | x ∈ ggSL9Torus ∧ ggSL9W i j hij e * x = x * ggSL9W i j hij e}) := by
  change CFSG.Assembly.IsComponentOf (ggSL9J i j e) (ggSL9E i j hij e)
  obtain ⟨k, hki, hkj⟩ := ggSL9_exists_third hij
  have hle : ggSL9J i j e ≤ ggSL9E i j hij e := ggSL9J_le_E hij e
  have hnorm : ((ggSL9J i j e).subgroupOf (ggSL9E i j hij e)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h c hh hc
    obtain ⟨N, lam, hNunit, hNform⟩ := ggSL9_det_isUnit hij e hc hki hkj
    let N₀ : GL (Fin 2) (GaloisField 2 3) := Matrix.GeneralLinearGroup.mk'' N hNunit
    have hN₀ : (N₀ : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) = N :=
      Matrix.GeneralLinearGroup.val_mk'' N hNunit
    have hc_eq : c = ggSL9BlockGL i j hij e N₀ * ggSL9Diag (Pi.mulSingle k lam) := by
      apply LinearEquiv.ext; intro v
      rw [LinearEquiv.mul_apply, ggSL9BlockGL_apply, hN₀]
      exact hNform v
    obtain ⟨Y, hY⟩ := MonoidHom.mem_range.mp (by
      rw [range_ggSL9BlockGL_comp_toGL hij e]; exact hh)
    have hYb : ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y) = h := hY
    let X : GL (Fin 2) (GaloisField 2 3) := N₀ * Matrix.SpecialLinearGroup.toGL Y * N₀⁻¹
    have hXdet : Matrix.GeneralLinearGroup.det X = 1 := by
      dsimp only [X]
      rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det Y]
      group
    have hXrange : X ∈ Set.range (Matrix.SpecialLinearGroup.toGL (n := Fin 2)
        (R := GaloisField 2 3)) := by
      rw [Matrix.SpecialLinearGroup.range_toGL]
      simpa using hXdet
    obtain ⟨Y', hY'⟩ := hXrange
    have hconj : c * h * c⁻¹ =
        ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y') := by
      calc c * h * c⁻¹
          = (ggSL9BlockGL i j hij e N₀ * ggSL9Diag (Pi.mulSingle k lam)) *
              ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y) *
              (ggSL9BlockGL i j hij e N₀ * ggSL9Diag (Pi.mulSingle k lam))⁻¹ := by
              rw [hc_eq, hYb]
        _ = ggSL9BlockGL i j hij e N₀ * (ggSL9Diag (Pi.mulSingle k lam) *
              ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y)) *
              ((ggSL9Diag (Pi.mulSingle k lam))⁻¹ *
                (ggSL9BlockGL i j hij e N₀)⁻¹) := by
              rw [mul_inv_rev]; group
        _ = ggSL9BlockGL i j hij e N₀ * (ggSL9BlockGL i j hij e
              (Matrix.SpecialLinearGroup.toGL Y) * ggSL9Diag (Pi.mulSingle k lam)) *
              ((ggSL9Diag (Pi.mulSingle k lam))⁻¹ *
                (ggSL9BlockGL i j hij e N₀)⁻¹) := by
              rw [show ggSL9Diag (Pi.mulSingle k lam) * ggSL9BlockGL i j hij e
                    (Matrix.SpecialLinearGroup.toGL Y) =
                  ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y) *
                    ggSL9Diag (Pi.mulSingle k lam) from
                  ggSL9D2_BlockGL e hij hki hkj lam (Matrix.SpecialLinearGroup.toGL Y)]
        _ = ggSL9BlockGL i j hij e N₀ * ggSL9BlockGL i j hij e
              (Matrix.SpecialLinearGroup.toGL Y) * (ggSL9BlockGL i j hij e N₀)⁻¹ := by
              group
        _ = ggSL9BlockGL i j hij e (N₀ * Matrix.SpecialLinearGroup.toGL Y * N₀⁻¹) := by
              rw [map_mul, map_mul, map_inv]
        _ = ggSL9BlockGL i j hij e X := rfl
        _ = ggSL9BlockGL i j hij e (Matrix.SpecialLinearGroup.toGL Y') := by rw [← hY']
    rw [hconj, ← range_ggSL9BlockGL_comp_toGL hij e]
    exact MonoidHom.mem_range.mpr ⟨Y', rfl⟩
  refine ⟨hle, ?_, isQuasisimple_ggSL9J hij e⟩
  exact IsSubnormal.step hle hnorm (IsSubnormal.refl _)

end CFSG.StandardType

end
