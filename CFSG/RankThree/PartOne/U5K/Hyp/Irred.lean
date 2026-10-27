module

public import CFSG.RankThree.PartOne.U5K.Hyp.Coord

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def hermM (y₁ y₂ b : K) : Matrix (Fin 2) (Fin 2) K := !![y₁, b; hK.bar b, y₂]

section Alg

variable {hK}

theorem hermM_add (y₁ y₂ b y₁' y₂' b' : K) :
    hermM hK y₁ y₂ b + hermM hK y₁' y₂' b' = hermM hK (y₁ + y₁') (y₂ + y₂') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermM]

theorem hermM_isHerm {y₁ y₂ b : K} (h₁ : hK.bar y₁ = y₁) (h₂ : hK.bar y₂ = y₂) :
    IsHerm hK (hermM hK y₁ y₂ b) := by
  rw [isHerm_iff]
  simp [hermM, h₁, h₂]

theorem eq_hermM {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm hK Y) :
    Y = hermM hK (Y 0 0) (Y 1 1) (Y 0 1) := by
  have := (isHerm_iff.1 hY).2.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermM, this]

theorem hermM_conj_unip (t y₁ y₂ b : K) (h₂ : hK.bar y₂ = y₂) :
    !![1, t; 0, 1] * hermM hK y₁ y₂ b * ((!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).map hK.bar)ᵀ =
      hermM hK (y₁ + t * hK.bar b + hK.bar t * b + t * hK.bar t * y₂) y₂ (b + t * y₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermM, Matrix.mul_apply, Fin.sum_univ_two, h₂] <;> ring

theorem hermM_conj_diag (m y₁ y₂ b : K) :
    !![m, 0; 0, 1] * hermM hK y₁ y₂ b * ((!![m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).map hK.bar)ᵀ =
      hermM hK (m * hK.bar m * y₁) y₂ (m * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem hermM_conj_swap (y₁ y₂ b : K) :
    !![0, 1; 1, 0] * hermM hK y₁ y₂ b * ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).map hK.bar)ᵀ =
      hermM hK y₂ y₁ (hK.bar b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermM, Matrix.mul_apply, Fin.sum_univ_two, hK.bar_bar]

theorem isUnit_det_unip (t : K) : IsUnit (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
  simp [Matrix.det_fin_two]

theorem isUnit_det_diag {m : K} (hm : m ≠ 0) :
    IsUnit (!![m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K).det := by
  simp [Matrix.det_fin_two, hm]

theorem isUnit_det_swap : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det := by
  simp [Matrix.det_fin_two]

end Alg

@[expose] def InR (R : Subgroup (hypSU hK 2 1)) (Y : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ v ∈ R, mat v = oddUni hK 0 Y

section InR

variable {hK} {R : Subgroup (hypSU hK 2 1)}

theorem InR.zero : InR hK R 0 := ⟨1, one_mem _, by rw [mat_one, oddUni_zero]⟩

theorem InR.add {Y Y' : Matrix (Fin 2) (Fin 2) K} (h : InR hK R Y) (h' : InR hK R Y') :
    InR hK R (Y + Y') := by
  obtain ⟨v, hv, hvm⟩ := h
  obtain ⟨v', hv', hvm'⟩ := h'
  refine ⟨v * v', mul_mem hv hv', ?_⟩
  rw [mat_mul, hvm, hvm', oddUni_mul]
  simp

theorem InR.conj (hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R,
    lev A hA * r * (lev A hA)⁻¹ ∈ R) {Y : Matrix (Fin 2) (Fin 2) K} (h : InR hK R Y)
    {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnit A.det) :
    InR hK R (A * Y * (A.map hK.bar)ᵀ) := by
  obtain ⟨v, hv, hvm⟩ := h
  refine ⟨lev A hA * v * (lev A hA)⁻¹, hL A hA v hv, ?_⟩
  have := lev_conj A hA hvm
  simpa using this

theorem InR.congr {Y Y' : Matrix (Fin 2) (Fin 2) K} (h : InR hK R Y) (e : Y = Y') :
    InR hK R Y' := e ▸ h

theorem herm_of_InR {Y : Matrix (Fin 2) (Fin 2) K} (h : InR hK R Y) : IsHerm hK Y := by
  obtain ⟨v, -, hv⟩ := h
  exact herm_of_mem_Vsub hv

theorem hermM_zero : hermM hK 0 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermM]

theorem exists_trace_one : ∃ c : K, c + hK.bar c = 1 := trace_surj (by simp)

variable (hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R,
    lev A hA * r * (lev A hA)⁻¹ ∈ R)
include hL

theorem stepA1 {y₁ y₂ b : K} (h₂ : hK.bar y₂ = y₂) (h : InR hK R (hermM hK y₁ y₂ b)) :
    InR hK R (hermM hK y₂ 0 0) := by
  have h2 : ∀ a : K, a + a = 0 := fun a => by
    have := hK.charP
    exact CharTwo.add_self_eq_zero a
  have h20 : (2 : K) = 0 := by
    have := hK.charP
    exact CharTwo.two_eq_zero
  obtain ⟨c₀, hc₀⟩ := exists_trace_one (hK := hK)
  have W : ∀ t : K, InR hK R (hermM hK (t * hK.bar b + hK.bar t * b + t * hK.bar t * y₂) 0
      (t * y₂)) := by
    intro t
    have h1 := (h.conj hL (isUnit_det_unip t)).add h
    rw [hermM_conj_unip t y₁ y₂ b h₂, hermM_add] at h1
    refine h1.congr ?_
    congr 1
    · linear_combination h2 y₁
    · exact h2 y₂
    · linear_combination h2 b
  have hsum := ((W 1).add (W c₀)).add (W (1 + c₀))
  rw [hermM_add, hermM_add] at hsum
  refine hsum.congr ?_
  congr 1
  · simp only [map_add, map_one, one_mul, mul_one]
    linear_combination y₂ * hc₀ + (y₂ * (1 + c₀ * hK.bar c₀) + hK.bar b * (1 + c₀) +
      b * (1 + hK.bar c₀)) * h20
  · simp [h2 0]
  · linear_combination (y₂ * (1 + c₀)) * h20

theorem stepA2 {b : K} (hb : b ≠ 0) (h : InR hK R (hermM hK 0 0 b)) :
    InR hK R (hermM hK 1 0 0) := by
  have h2 : ∀ a : K, a + a = 0 := fun a => by
    have := hK.charP
    exact CharTwo.add_self_eq_zero a
  obtain ⟨c₀, hc₀⟩ := exists_trace_one (hK := hK)
  have hb' : hK.bar b ≠ 0 := (map_ne_zero hK.bar).mpr hb
  have h1 := (h.conj hL (isUnit_det_unip (c₀ / hK.bar b))).add h
  rw [hermM_conj_unip _ 0 0 b (by simp), hermM_add] at h1
  refine h1.congr ?_
  congr 1
  · have e1 : c₀ / hK.bar b * hK.bar b = c₀ := div_mul_cancel₀ _ hb'
    have e2 : hK.bar (c₀ / hK.bar b) * b = hK.bar c₀ := by
      rw [map_div₀, hK.bar_bar, div_mul_cancel₀ _ hb]
    linear_combination e1 + e2 + hc₀
  · simp
  · linear_combination h2 b

theorem stepB {c : K} (hc : hK.bar c = c) (hc0 : c ≠ 0) (h : InR hK R (hermM hK c 0 0)) {c' : K}
    (hc' : hK.bar c' = c') : InR hK R (hermM hK c' 0 0) := by
  by_cases h0 : c' = 0
  · rw [h0, hermM_zero]
    exact InR.zero
  · have hmem : c' / c ∈ hK.fixedField := by
      refine hK.mem_fixedField.mpr ?_
      rw [map_div₀, hc, hc']
    obtain ⟨m, hm⟩ := hK.normHom_surjective ⟨c' / c, hmem⟩
    have hm' : m * hK.bar m = c' / c := congrArg Subtype.val hm
    have hne : c' / c ≠ 0 := div_ne_zero h0 hc0
    have hm0 : m ≠ 0 := fun h' => hne (by rw [← hm', h']; simp)
    have h1 := h.conj hL (isUnit_det_diag hm0)
    rw [hermM_conj_diag] at h1
    refine h1.congr ?_
    congr 1
    · rw [hm']
      exact div_mul_cancel₀ _ hc0
    · simp

theorem stepC {c : K} (h : InR hK R (hermM hK c 0 0)) : InR hK R (hermM hK 0 c 0) := by
  have h1 := h.conj hL (isUnit_det_swap)
  rw [hermM_conj_swap] at h1
  refine h1.congr ?_
  simp

theorem stepD (h : InR hK R (hermM hK 0 1 0)) (hB : ∀ c' : K, hK.bar c' = c' →
    InR hK R (hermM hK c' 0 0)) (t : K) : InR hK R (hermM hK 0 0 t) := by
  have h2 : ∀ a : K, a + a = 0 := fun a => by
    have := hK.charP
    exact CharTwo.add_self_eq_zero a
  have h1 := (h.conj hL (isUnit_det_unip t)).add h
  rw [hermM_conj_unip t 0 1 0 (by simp), hermM_add] at h1
  have hN : hK.bar (t * hK.bar t) = t * hK.bar t := by rw [map_mul, hK.bar_bar, mul_comm]
  have h3 := h1.add (hB (t * hK.bar t) hN)
  rw [hermM_add] at h3
  refine h3.congr ?_
  congr 1
  · simp
    linear_combination h2 (t * hK.bar t)
  · simp [h2 1]
  · simp

theorem InR_all {Y : Matrix (Fin 2) (Fin 2) K} (hY : InR hK R Y) (hne : Y ≠ 0)
    {Y' : Matrix (Fin 2) (Fin 2) K} (hY' : IsHerm hK Y') : InR hK R Y' := by
  have hH := herm_of_InR hY
  obtain ⟨y₁, y₂, b, hy₁, hy₂, rfl⟩ : ∃ y₁ y₂ b : K, hK.bar y₁ = y₁ ∧ hK.bar y₂ = y₂ ∧
      Y = hermM hK y₁ y₂ b :=
    ⟨Y 0 0, Y 1 1, Y 0 1, (isHerm_iff.1 hH).1, (isHerm_iff.1 hH).2.1, eq_hermM hH⟩
  have key : ∃ c : K, c ≠ 0 ∧ hK.bar c = c ∧ InR hK R (hermM hK c 0 0) := by
    by_cases h2 : y₂ = 0
    · by_cases h1 : y₁ = 0
      · have hb : b ≠ 0 := fun hb => hne (by rw [h1, h2, hb, hermM_zero])
        rw [h1, h2] at hY
        exact ⟨1, one_ne_zero, by simp, stepA2 hL hb hY⟩
      · have hsw := hY.conj hL isUnit_det_swap
        rw [hermM_conj_swap] at hsw
        exact ⟨y₁, h1, hy₁, stepA1 hL hy₁ hsw⟩
    · exact ⟨y₂, h2, hy₂, stepA1 hL hy₂ hY⟩
  obtain ⟨c, hc0, hc, hcR⟩ := key
  have hB : ∀ c' : K, hK.bar c' = c' → InR hK R (hermM hK c' 0 0) := fun c' hc' =>
    stepB hL hc hc0 hcR hc'
  have hC1 : InR hK R (hermM hK 0 1 0) := stepC hL (hB 1 (by simp))
  have hD := stepD hL hC1 hB
  have hH' := isHerm_iff.1 hY'
  rw [eq_hermM hY']
  have a1 := hB (Y' 0 0) hH'.1
  have a2 := stepC hL (hB (Y' 1 1) hH'.2.1)
  have a3 := hD (Y' 0 1)
  have h3 := (a1.add a2).add a3
  rw [hermM_add, hermM_add] at h3
  refine h3.congr ?_
  congr 1 <;> simp

end InR

section Trans

variable {hK}

theorem exists_col {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) K, M.det = 1 ∧ M *ᵥ ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨!![0, -(v 1)⁻¹; v 1, 0], ?_, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, h0]
  · refine ⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]

theorem exists_sl2_smul {x y : Fin 2 → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, A.det = 1 ∧ A *ᵥ x = y := by
  obtain ⟨Mx, hMx, hx'⟩ := exists_col hx
  obtain ⟨My, hMy, hy'⟩ := exists_col hy
  refine ⟨My * Mx.adjugate, by rw [Matrix.det_mul, hMy, Matrix.det_adjugate, hMx]; simp, ?_⟩
  calc (My * Mx.adjugate) *ᵥ x = My *ᵥ (Mx.adjugate *ᵥ x) :=
        (Matrix.mulVec_mulVec x My Mx.adjugate).symm
    _ = My *ᵥ (Mx.adjugate *ᵥ (Mx *ᵥ ![1, 0])) := by rw [hx']
    _ = My *ᵥ (((Mx.adjugate * Mx) *ᵥ ![1, 0])) := by
        rw [Matrix.mulVec_mulVec ![1, 0] Mx.adjugate Mx]
    _ = My *ᵥ ![1, 0] := by rw [Matrix.adjugate_mul, hMx]; simp
    _ = y := hy'

end Trans

section Comm

variable {hK}

theorem comm_Ssub {r r' : hypSU hK 2 1} {x y : Fin 2 → K} {C C' : Matrix (Fin 2) (Fin 2) K}
    (hr : mat r = oddUni hK x C) (hr' : mat r' = oddUni hK y C') :
    mat (r * r' * r⁻¹ * r'⁻¹) = oddUni hK 0
      (vecMulVec y (fun j => hK.bar (x j)) - vecMulVec x (fun j => hK.bar (y j))) := by
  have h1 : mat (r * r') = oddUni hK 0
      (vecMulVec y (fun j => hK.bar (x j)) - vecMulVec x (fun j => hK.bar (y j))) *
        mat (r' * r) := by
    rw [mat_mul, mat_mul, hr, hr', oddUni_mul, oddUni_mul, oddUni_mul]
    congr 1
    · simp [add_comm]
    · ext i j; simp [vecMulVec]; ring
  have h2 : mat (r' * r) * mat (r' * r)⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have h3 : r * r' * r⁻¹ * r'⁻¹ = r * r' * (r' * r)⁻¹ := by group
  rw [h3, mat_mul, h1, Matrix.mul_assoc, h2, Matrix.mul_one]

end Comm

section Irr

variable {hK} {R : Subgroup (hypSU hK 2 1)}

theorem mat_inv_of_oddUni {g : hypSU hK 2 1} {x : Fin 2 → K} {C : Matrix (Fin 2) (Fin 2) K}
    (hg : mat g = oddUni hK x C) :
    mat g⁻¹ = oddUni hK (-x) (-C - vecMulVec x fun j => hK.bar (x j)) := by
  apply mat_inv_eq
  rw [hg, oddUni_mul]
  have : (-C - vecMulVec x (fun j => hK.bar (x j)) + C -
      vecMulVec (-x) fun j => hK.bar (x j)) = 0 := by
    ext i j; simp [vecMulVec]; ring
  rw [this, neg_add_cancel, oddUni_zero]

theorem exists_mem_R_coord (hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R,
    lev A hA * r * (lev A hA)⁻¹ ∈ R) {r : hypSU hK 2 1} (hr : r ∈ R) {x : Fin 2 → K}
    {C : Matrix (Fin 2) (Fin 2) K} (hrm : mat r = oddUni hK x C) (hx : x ≠ 0) {y : Fin 2 → K}
    (hy : y ≠ 0) : ∃ r' ∈ R, ∃ C' : Matrix (Fin 2) (Fin 2) K, mat r' = oddUni hK y C' := by
  obtain ⟨A, hdet, hAx⟩ := exists_sl2_smul hx hy
  have hA : IsUnit A.det := by rw [hdet]; exact isUnit_one
  refine ⟨lev A hA * r * (lev A hA)⁻¹, hL A hA r hr, A * C * (A.map hK.bar)ᵀ, ?_⟩
  rw [lev_conj A hA hrm]
  simp [hdet, hAx]

theorem irreducible_Ssub (hR : R ≤ Ssub hK)
    (hL : ∀ (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det), ∀ r ∈ R,
      lev A hA * r * (lev A hA)⁻¹ ∈ R) : R = ⊥ ∨ R = Vsub hK ∨ R = Ssub hK := by
  have hVR : (∃ Y : Matrix (Fin 2) (Fin 2) K, Y ≠ 0 ∧ InR hK R Y) → Vsub hK ≤ R := by
    rintro ⟨Y, hYne, hY⟩ g hg
    obtain ⟨-, Y', hY'⟩ := hg
    obtain ⟨v, hv, hvm⟩ := InR_all hL hY hYne (herm_of_mem_Vsub hY')
    have : v = g := mat_injective (hvm.trans hY'.symm)
    exact this ▸ hv
  by_cases hV : R ≤ Vsub hK
  · by_cases hbot : R = ⊥
    · exact Or.inl hbot
    · right; left
      obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
      obtain ⟨-, Y, hY⟩ := hV r.2
      have hYne : Y ≠ 0 := by
        rintro rfl
        apply hr1
        apply Subtype.ext
        apply mat_injective
        rw [hY, oddUni_zero]
        rfl
      exact le_antisymm hV (hVR ⟨Y, hYne, r.1, r.2, hY⟩)
  · right; right
    obtain ⟨r, hrR, hrV⟩ : ∃ r ∈ R, r ∉ Vsub hK := by
      by_contra hcon
      push Not at hcon
      exact hV hcon
    obtain ⟨-, x, C, hrm⟩ := hR hrR
    have hx : x ≠ 0 := fun h0 => hrV (mem_Vsub_of_mat (by rw [hrm, h0]))
    have he0 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
    have he1 : (![0, 1] : Fin 2 → K) ≠ 0 := fun h0 => by
      have := congrFun h0 1
      simp at this
    obtain ⟨r₀, hr₀, C₀, hr₀m⟩ := exists_mem_R_coord hL hrR hrm hx he0
    obtain ⟨r₁, hr₁, C₁, hr₁m⟩ := exists_mem_R_coord hL hrR hrm hx he1
    have hz := comm_Ssub hr₀m hr₁m
    have hzR : r₀ * r₁ * r₀⁻¹ * r₁⁻¹ ∈ R :=
      mul_mem (mul_mem (mul_mem hr₀ hr₁) (inv_mem hr₀)) (inv_mem hr₁)
    have hW : vecMulVec (![0, 1] : Fin 2 → K) (fun j => hK.bar ((![1, 0] : Fin 2 → K) j)) -
        vecMulVec (![1, 0] : Fin 2 → K) (fun j => hK.bar ((![0, 1] : Fin 2 → K) j)) ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 1) 0
      simp [vecMulVec] at this
    have hVle := hVR ⟨_, hW, _, hzR, hz⟩
    refine le_antisymm hR (fun s hs => ?_)
    obtain ⟨-, y, C₂, hsm⟩ := hs
    by_cases hy : y = 0
    · exact hVle (mem_Vsub_of_mat (by rw [hsm, hy]))
    · obtain ⟨r', hr', C', hr'm⟩ := exists_mem_R_coord hL hrR hrm hx hy
      have hinv := mat_inv_of_oddUni hr'm
      have hsV : s * r'⁻¹ ∈ Vsub hK := by
        refine mem_Vsub_of_mat (Y := C₂ + (-C' - vecMulVec y (fun j => hK.bar (y j))) -
          vecMulVec y (fun j => hK.bar ((-y) j))) ?_
        rw [mat_mul, hsm, hinv, oddUni_mul]
        simp
      have := mul_mem (hVle hsV) hr'
      simpa using this

end Irr

section Center

variable {hK}

theorem exists_mem_Ssub_coord (y : Fin 2 → K) :
    ∃ s ∈ Ssub hK, ∃ C : Matrix (Fin 2) (Fin 2) K, mat s = oddUni hK y C := by
  have h2 : ∀ a : K, a + a = 0 := fun a => by
    have := hK.charP
    exact CharTwo.add_self_eq_zero a
  have hfix : ∀ i, hK.bar (y i * hK.bar (y i)) = y i * hK.bar (y i) := fun i => by
    rw [map_mul, hK.bar_bar, mul_comm]
  choose c hc using fun i => trace_surj (hK := hK) (hfix i)
  have hC : (Matrix.of fun i j => if i = j then c i else if i = 0 then y 0 * hK.bar (y 1) else 0 :
      Matrix (Fin 2) (Fin 2) K) + ((Matrix.of fun i j => if i = j then c i else
        if i = 0 then y 0 * hK.bar (y 1) else 0 : Matrix (Fin 2) (Fin 2) K).map hK.bar)ᵀ =
      -vecMulVec y fun j => hK.bar (y j) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec, hK.bar_bar]
    · linear_combination hc 0 + h2 (y 0 * hK.bar (y 0))
    · linear_combination h2 (y 0 * hK.bar (y 1))
    · linear_combination h2 (hK.bar (y 0) * y 1)
    · linear_combination hc 1 + h2 (y 1 * hK.bar (y 1))
  obtain ⟨s, hs, hsm⟩ := exists_mem_Ssub hC
  exact ⟨s, hs, _, hsm⟩

theorem central_Ssub_iff {g : hypSU hK 2 1} (hg : g ∈ Ssub hK) :
    (∀ s ∈ Ssub hK, s * g = g * s) ↔ g ∈ Vsub hK := by
  constructor
  · intro h
    obtain ⟨-, x, C, hgm⟩ := hg
    have key : ∀ y : Fin 2 → K, (∃ s ∈ Ssub hK, ∃ C' : Matrix (Fin 2) (Fin 2) K,
        mat s = oddUni hK y C') → vecMulVec y (fun j => hK.bar (x j)) -
          vecMulVec x (fun j => hK.bar (y j)) = 0 := by
      rintro y ⟨s, hs, C', hsm⟩
      have hc := comm_Ssub hgm hsm
      have h1 : g * s * g⁻¹ * s⁻¹ = 1 := by rw [← h s hs]; group
      rw [h1, mat_one, ← oddUni_zero hK (r := 2)] at hc
      exact ((oddUni_inj hc).2).symm
    have e0 := key ![1, 0] (exists_mem_Ssub_coord _)
    have e1 := key ![0, 1] (exists_mem_Ssub_coord _)
    have hx : x = 0 := by
      funext i
      fin_cases i
      · have := congrFun (congrFun e1 1) 0
        simp [vecMulVec] at this
        simpa using this
      · have := congrFun (congrFun e0 0) 1
        simp [vecMulVec] at this
        simpa using this
    exact mem_Vsub_of_mat (by rw [hgm, hx])
  · intro hv s hs
    obtain ⟨-, x, C, hsm⟩ := hs
    obtain ⟨-, Y, hYm⟩ := hv
    apply mat_injective
    rw [mat_mul, mat_mul, hsm, hYm, oddUni_comm_zero]

end Center

end CFSG.RankThree.PartOne.U5K.Hyp
