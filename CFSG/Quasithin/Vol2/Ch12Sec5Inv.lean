module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.S125Inv

open Matrix Module

local instance fact_prime_two' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local notation "W5" => Fin 5 → ZMod 2
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)
local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def t1 : M5 := 1 + Matrix.single 0 4 1

@[expose] def t2 : M5 := 1 + Matrix.single 0 3 1 + Matrix.single 1 4 1

@[expose] def colMat (v : Fin 5 → W5) : M5 := Matrix.of fun i j => v j i

theorem colMat_col (v : Fin 5 → W5) : (colMat v).col = v := by
  funext j i
  rfl

theorem colMat_mulVec_single (v : Fin 5 → W5) (j : Fin 5) :
    colMat v *ᵥ Pi.single j 1 = v j := by
  rw [Matrix.mulVec_single_one, colMat_col]

theorem colMat_isUnit {v : Fin 5 → W5} (hv : LinearIndependent (ZMod 2) v) :
    IsUnit (colMat v) := by
  rw [← colMat_col v] at hv
  exact Matrix.linearIndependent_cols_iff_isUnit.1 hv

theorem t1_cols : ∀ j : Fin 5, t1 *ᵥ Pi.single j 1 =
    Pi.single j 1 + if j = 4 then Pi.single 0 1 else 0 := by
  decide

theorem t2_cols : ∀ j : Fin 5, t2 *ᵥ Pi.single j 1 =
    Pi.single j 1 + (if j = 3 then Pi.single 0 1 else 0) + if j = 4 then Pi.single 1 1 else 0 := by
  decide

theorem ext_cols {A B : M5} (h : ∀ j : Fin 5, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) :
    A = B := by
  ext i j
  have := congrFun (h j) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this

theorem colMat_t1 {N : M5} {v : Fin 5 → W5} (h0 : N *ᵥ v 0 = 0) (h1 : N *ᵥ v 1 = 0)
    (h2 : N *ᵥ v 2 = 0) (h3 : N *ᵥ v 3 = 0) (h4 : N *ᵥ v 4 = v 0) :
    (1 + N) * colMat v = colMat v * t1 := by
  refine ext_cols fun j => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, colMat_mulVec_single, t1_cols,
    Matrix.mulVec_add, colMat_mulVec_single, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  fin_cases j
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [h4, colMat_col]

theorem colMat_t2 {N : M5} {v : Fin 5 → W5} (h0 : N *ᵥ v 0 = 0) (h1 : N *ᵥ v 1 = 0)
    (h2 : N *ᵥ v 2 = 0) (h3 : N *ᵥ v 3 = v 0) (h4 : N *ᵥ v 4 = v 1) :
    (1 + N) * colMat v = colMat v * t2 := by
  refine ext_cols fun j => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, colMat_mulVec_single, t2_cols,
    Matrix.mulVec_add, Matrix.mulVec_add, colMat_mulVec_single, Matrix.add_mulVec,
    Matrix.one_mulVec, add_assoc]
  congr 1
  fin_cases j
  · simp [h0]
  · simp [h1]
  · simp [h2]
  · simp [h3, colMat_col]
  · simp [h4, colMat_col]

theorem zmod2_eq_one {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem exists_conj_of_colMat {g : SL5} {v : Fin 5 → W5} (hv : LinearIndependent (ZMod 2) v)
    {t : M5} (h : (g : M5) * colMat v = colMat v * t) :
    ∃ b : SL5, ((b * g * b⁻¹ : SL5) : M5) = t := by
  have hP := colMat_isUnit hv
  have hdet : (colMat v).det = 1 :=
    zmod2_eq_one ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero
  let P : SL5 := ⟨colMat v, hdet⟩
  have hPinv : ((P⁻¹ : SL5) : M5) * colMat v = 1 :=
    congrArg Subtype.val (inv_mul_cancel P)
  refine ⟨P⁻¹, ?_⟩
  rw [inv_inv]
  change ((P⁻¹ : SL5) : M5) * (g : M5) * colMat v = t
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]

theorem mem_span_singleton_zmod2 {u x : W5} (h : x ∈ Submodule.span (ZMod 2) {u}) :
    x = 0 ∨ x = u := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
  by_cases ha : a = 0
  · left
    rw [ha, zero_smul]
  · right
    rw [zmod2_eq_one ha, one_smul]

theorem linearIndependent_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) : LinearIndependent (ZMod 2) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases hs : s = 0
  · rw [hs, zero_smul, zero_add] at hst
    by_cases ht : t = 0
    · exact ⟨hs, ht⟩
    · rw [zmod2_eq_one ht, one_smul] at hst
      exact absurd hst hy
  · rw [zmod2_eq_one hs, one_smul] at hst
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact absurd hst hx
    · rw [zmod2_eq_one ht, one_smul] at hst
      exfalso
      apply hxy
      have h1 : x = -y := eq_neg_of_add_eq_zero_left hst
      have h2 : -y = y := by
        rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2),
          show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [h1, h2]

theorem exists_conj_t1 {g : SL5} {w₁ : W5}
    (hNN : ∀ x : W5, ((g : M5) - 1) *ᵥ (((g : M5) - 1) *ᵥ x) = 0)
    (hw₁ : ((g : M5) - 1) *ᵥ w₁ ≠ 0)
    (h1 : ∀ x : W5, ((g : M5) - 1) *ᵥ x = 0 ∨ ((g : M5) - 1) *ᵥ x = ((g : M5) - 1) *ᵥ w₁) :
    ∃ b : SL5, ((b * g * b⁻¹ : SL5) : M5) = t1 := by
  set N : M5 := (g : M5) - 1 with hN
  set u₁ := N *ᵥ w₁ with hu₁
  let f : W5 →ₗ[ZMod 2] W5 := Matrix.mulVecLin N
  have hf : ∀ x, f x = N *ᵥ x := fun _ => rfl
  set K := LinearMap.ker f with hK
  have hrange : LinearMap.range f = Submodule.span (ZMod 2) {u₁} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rcases h1 x with h | h
      · rw [hf, h]
        exact Submodule.zero_mem _
      · rw [hf, h]
        exact Submodule.mem_span_singleton_self _
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨w₁, rfl⟩
  have hK4 : finrank (ZMod 2) K = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, finrank_span_singleton hw₁, Module.finrank_fin_fun, ← hK] at h
    omega
  have hu₁K : u₁ ∈ K := hNN w₁
  let f₁ : Fin 1 → K := ![⟨u₁, hu₁K⟩]
  have hf₁ : LinearIndependent (ZMod 2) f₁ := by
    rw [linearIndependent_unique_iff]
    intro h
    apply hw₁
    have := congrArg Subtype.val h
    exact this
  obtain ⟨k₁, hk₁⟩ := exists_linearIndependent_snoc_of_lt_finrank hf₁ (by rw [hK4]; norm_num)
  obtain ⟨k₂, hk₂⟩ := exists_linearIndependent_snoc_of_lt_finrank hk₁ (by rw [hK4]; norm_num)
  obtain ⟨k₃, hk₃⟩ := exists_linearIndependent_snoc_of_lt_finrank hk₂ (by rw [hK4]; norm_num)
  set f₄ : Fin 4 → K := Fin.snoc (Fin.snoc (Fin.snoc f₁ k₁) k₂) k₃ with hf₄
  have hLI4 : LinearIndependent (ZMod 2) (K.subtype ∘ f₄) :=
    hk₃.map' K.subtype (Submodule.ker_subtype K)
  have hw₁K : w₁ ∉ Submodule.span (ZMod 2) (Set.range (K.subtype ∘ f₄)) := by
    intro h
    have hle : Submodule.span (ZMod 2) (Set.range (K.subtype ∘ f₄)) ≤ K := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (f₄ i).2
    exact hw₁ (hle h)
  let v : Fin 5 → W5 := Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₄) w₁
  have hv : LinearIndependent (ZMod 2) v := hLI4.finSnoc hw₁K
  have hv0 : v 0 = u₁ := rfl
  have hvK : ∀ i : Fin 4, N *ᵥ v (Fin.castSucc i) = 0 := fun i => by
    have : v (Fin.castSucc i) = ((f₄ i : K) : W5) := by
      change Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₄) w₁ (Fin.castSucc i) = _
      rw [Fin.snoc_castSucc]
      rfl
    rw [this]
    exact (f₄ i).2
  have hv4 : v 4 = w₁ := by
    change Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₄) w₁ (Fin.last 4) = w₁
    rw [Fin.snoc_last]
  have hcol : (1 + N) * colMat v = colMat v * t1 :=
    colMat_t1 (hvK 0) (hvK 1) (hvK 2) (hvK 3) (by rw [hv4, hv0])
  have hg : (g : M5) = 1 + N := by
    rw [hN]
    abel
  rw [← hg] at hcol
  exact exists_conj_of_colMat hv hcol

theorem exists_conj_t2 {g : SL5} {w₁ w₂ : W5}
    (hNN : ∀ x : W5, ((g : M5) - 1) *ᵥ (((g : M5) - 1) *ᵥ x) = 0)
    (hw₁ : ((g : M5) - 1) *ᵥ w₁ ≠ 0) (hw₂ : ((g : M5) - 1) *ᵥ w₂ ≠ 0)
    (hw₁₂ : ((g : M5) - 1) *ᵥ w₂ ≠ ((g : M5) - 1) *ᵥ w₁) :
    ∃ b : SL5, ((b * g * b⁻¹ : SL5) : M5) = t2 := by
  set N : M5 := (g : M5) - 1 with hN
  set u₁ := N *ᵥ w₁ with hu₁
  set u₂ := N *ᵥ w₂ with hu₂
  let f : W5 →ₗ[ZMod 2] W5 := Matrix.mulVecLin N
  have hf : ∀ x, f x = N *ᵥ x := fun _ => rfl
  set K := LinearMap.ker f with hK
  have hu₁K : u₁ ∈ K := hNN w₁
  have hu₂K : u₂ ∈ K := hNN w₂
  have hRK : LinearMap.range f ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hNN x
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun, ← hK] at hsum
  have hRle := Submodule.finrank_mono hRK
  have hR2 : 2 ≤ finrank (ZMod 2) (LinearMap.range f) := by
    have hli : LinearIndependent (ZMod 2) ![u₁, u₂] := linearIndependent_pair hw₁ hw₂ hw₁₂.symm
    have hli' : LinearIndependent (ZMod 2)
        (![⟨u₁, ⟨w₁, rfl⟩⟩, ⟨u₂, ⟨w₂, rfl⟩⟩] : Fin 2 → LinearMap.range f) := by
      apply LinearIndependent.of_comp (LinearMap.range f).subtype
      convert hli using 1
      funext i
      fin_cases i <;> rfl
    have := hli'.fintype_card_le_finrank
    simpa using this
  have hK3 : finrank (ZMod 2) K = 3 := by omega
  let f₂ : Fin 2 → K := ![⟨u₁, hu₁K⟩, ⟨u₂, hu₂K⟩]
  have hf₂ : LinearIndependent (ZMod 2) f₂ := by
    apply LinearIndependent.of_comp K.subtype
    have hli : LinearIndependent (ZMod 2) ![u₁, u₂] := linearIndependent_pair hw₁ hw₂ hw₁₂.symm
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  obtain ⟨k, hk⟩ := exists_linearIndependent_snoc_of_lt_finrank hf₂ (by rw [hK3]; norm_num)
  set f₃ : Fin 3 → K := Fin.snoc f₂ k with hf₃
  have hLI3 : LinearIndependent (ZMod 2) (K.subtype ∘ f₃) :=
    hk.map' K.subtype (Submodule.ker_subtype K)
  have hspanK : Submodule.span (ZMod 2) (Set.range (K.subtype ∘ f₃)) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f₃ i).2
  have hw₁K : w₁ ∉ Submodule.span (ZMod 2) (Set.range (K.subtype ∘ f₃)) :=
    fun h => hw₁ (hspanK h)
  let v₄ : Fin 4 → W5 := Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₃) w₁
  have hLI4 : LinearIndependent (ZMod 2) v₄ := hLI3.finSnoc hw₁K
  have hw₂K : w₂ ∉ Submodule.span (ZMod 2) (Set.range v₄) := by
    intro h
    have hle : Submodule.span (ZMod 2) (Set.range v₄) ≤
        (Submodule.span (ZMod 2) {u₁}).comap f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · have e : v₄ (Fin.last 3) = w₁ := by simp only [v₄, Fin.snoc_last]
        rw [e]
        exact Submodule.mem_span_singleton_self _
      · have e : v₄ (Fin.castSucc i) = ((f₃ i : K) : W5) := by simp [v₄]
        rw [e, show f ((f₃ i : K) : W5) = 0 from (f₃ i).2]
        exact Submodule.zero_mem _
    rcases mem_span_singleton_zmod2 (hle h) with h0 | h0
    · exact hw₂ h0
    · exact hw₁₂ h0
  let v : Fin 5 → W5 := Fin.snoc (α := fun _ => W5) v₄ w₂
  have hv : LinearIndependent (ZMod 2) v := hLI4.finSnoc hw₂K
  have hv0 : v 0 = u₁ := rfl
  have hv1 : v 1 = u₂ := rfl
  have hvK : ∀ i : Fin 3, N *ᵥ v (Fin.castSucc (Fin.castSucc i)) = 0 := fun i => by
    have : v (Fin.castSucc (Fin.castSucc i)) = ((f₃ i : K) : W5) := by
      change Fin.snoc (α := fun _ => W5) v₄ w₂ (Fin.castSucc (Fin.castSucc i)) = _
      rw [Fin.snoc_castSucc]
      change Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₃) w₁ (Fin.castSucc i) = _
      rw [Fin.snoc_castSucc]
      rfl
    rw [this]
    exact (f₃ i).2
  have hv3 : v 3 = w₁ := by
    change Fin.snoc (α := fun _ => W5) v₄ w₂ (Fin.castSucc (Fin.last 3)) = w₁
    rw [Fin.snoc_castSucc]
    change Fin.snoc (α := fun _ => W5) (K.subtype ∘ f₃) w₁ (Fin.last 3) = w₁
    rw [Fin.snoc_last]
  have hv4 : v 4 = w₂ := by
    change Fin.snoc (α := fun _ => W5) v₄ w₂ (Fin.last 4) = w₂
    rw [Fin.snoc_last]
  have hcol : (1 + N) * colMat v = colMat v * t2 :=
    colMat_t2 (hvK 0) (hvK 1) (hvK 2) (by rw [hv3, hv0]) (by rw [hv4, hv1])
  have hg : (g : M5) = 1 + N := by
    rw [hN]
    abel
  rw [← hg] at hcol
  exact exists_conj_of_colMat hv hcol

theorem invol_class (g : SL5) (hg : g * g = 1) (hg1 : g ≠ 1) :
    ∃ b : SL5, ((b * g * b⁻¹ : SL5) : M5) = t1 ∨ ((b * g * b⁻¹ : SL5) : M5) = t2 := by
  set N : M5 := (g : M5) - 1 with hN
  have hgg : (g : M5) * g = 1 := congrArg Subtype.val hg
  have hNN : N * N = 0 := by
    have e : N * N = (g : M5) * g - ((g : M5) + g) + 1 := by
      rw [hN, sub_mul, mul_sub, mul_sub, one_mul, mul_one, mul_one]
      abel
    rw [e, hgg]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply]
    generalize (g : M5) i j = c
    split_ifs <;> fin_cases c <;> decide
  have hNNv : ∀ x : W5, N *ᵥ (N *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  have hN0 : N ≠ 0 := by
    intro h
    apply hg1
    apply Subtype.ext
    change (g : M5) = 1
    rw [← sub_eq_zero]
    exact h
  obtain ⟨w₁, hw₁⟩ : ∃ w : W5, N *ᵥ w ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hN0
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    rwa [Matrix.mulVec_single_one] at this
  obtain ⟨b, hb⟩ : ∃ b : SL5, ((b * g * b⁻¹ : SL5) : M5) = t1 ∨
      ((b * g * b⁻¹ : SL5) : M5) = t2 := by
    by_cases h1 : ∀ x : W5, N *ᵥ x = 0 ∨ N *ᵥ x = N *ᵥ w₁
    · obtain ⟨b, hb⟩ := exists_conj_t1 hNNv hw₁ h1
      exact ⟨b, Or.inl hb⟩
    · simp only [not_forall, not_or] at h1
      obtain ⟨w₂, hw₂, hw₁₂⟩ := h1
      obtain ⟨b, hb⟩ := exists_conj_t2 hNNv hw₁ hw₂ hw₁₂
      exact ⟨b, Or.inr hb⟩
  exact ⟨b, hb⟩

end CFSG.Quasithin.H13.S125Inv
