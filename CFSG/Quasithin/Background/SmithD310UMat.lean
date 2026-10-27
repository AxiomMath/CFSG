module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

public section

namespace CFSG.Quasithin.SmithD310U

open Matrix Module

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_range_le_one_of_comp_self {y : V →ₗ[K] V} (hV : finrank K V ≤ 3)
    (hy : y ∘ₗ y = 0) : finrank K (LinearMap.range y) ≤ 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker y
  have h2 : LinearMap.range y ≤ LinearMap.ker y := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hy, LinearMap.zero_apply]
  have h3 := Submodule.finrank_mono h2
  omega

theorem comp_eq_zero_of_comp_self {x y : V →ₗ[K] V} (hV : finrank K V ≤ 3) (hx : x ∘ₗ x = 0)
    (hy : y ∘ₗ y = 0) (hxy : x ∘ₗ y = y ∘ₗ x) : x ∘ₗ y = 0 := by
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp (finrank_range_le_one_of_comp_self hV hy)
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, x (y v) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  obtain ⟨c₁, hc₁⟩ := hv₀ ⟨y v, LinearMap.mem_range_self y v⟩
  obtain ⟨c₂, hc₂⟩ := hv₀ ⟨y (x v), LinearMap.mem_range_self y (x v)⟩
  have e1 : y v = c₁ • (v₀ : V) := (congrArg Subtype.val hc₁).symm
  have e2 : x (y v) = c₂ • (v₀ : V) := by
    rw [show x (y v) = y (x v) from LinearMap.congr_fun hxy v]
    exact (congrArg Subtype.val hc₂).symm
  have hc1 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at e1
    exact hv (by rw [e1, map_zero])
  have e3 : x (y v) = (c₂ * c₁⁻¹) • y v := by
    rw [e2, e1, smul_smul, mul_assoc, inv_mul_cancel₀ hc1, mul_one]
  have e4 : (c₂ * c₁⁻¹) • x (y v) = 0 := by
    rw [← map_smul, ← e3, ← LinearMap.comp_apply x x, hx, LinearMap.zero_apply]
  rcases smul_eq_zero.mp e4 with h | h
  · have hc2 : c₂ = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd (inv_eq_zero.mp h) hc1
    exact hv (by rw [e2, hc2, zero_smul])
  · exact hv h

end General

section Mat

variable {K : Type*} [Field K]

theorem mul_eq_zero_of_mul_self {x y : Matrix (Fin 3) (Fin 3) K} (hx : x * x = 0)
    (hy : y * y = 0) (hxy : x * y = y * x) : x * y = 0 := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, map_zero]
  refine comp_eq_zero_of_comp_self (by simp) ?_ ?_ ?_
  · rw [← Matrix.toLin'_mul, hx, map_zero]
  · rw [← Matrix.toLin'_mul, hy, map_zero]
  · rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hxy]

theorem sub_one_mul_self (h2 : (2 : K) = 0) {g : Matrix (Fin 3) (Fin 3) K} (hg : g * g = 1) :
    (g - 1) * (g - 1) = 0 := by
  have e : (g - 1) * (g - 1) = g * g - 1 - (2 : K) • (g - 1) := by
    rw [two_smul]
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [e, hg, h2, zero_smul, sub_self, sub_zero]

@[expose] def fixVec (S : Set (Matrix (Fin 3) (Fin 3) K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ g ∈ S, g *ᵥ v = v}
  add_mem' {u v} hu hv g hg := by rw [mulVec_add, hu g hg, hv g hg]
  zero_mem' g _ := mulVec_zero g
  smul_mem' c v hv g hg := by rw [mulVec_smul, hv g hg]

theorem mem_fixVec {S : Set (Matrix (Fin 3) (Fin 3) K)} {v : Fin 3 → K} :
    v ∈ fixVec S ↔ ∀ g ∈ S, g *ᵥ v = v := Iff.rfl

@[expose] def fixVecT (S : Set (Matrix (Fin 3) (Fin 3) K)) : Submodule K (Fin 3 → K) :=
  fixVec (Matrix.transpose '' S)

theorem mem_fixVecT {S : Set (Matrix (Fin 3) (Fin 3) K)} {v : Fin 3 → K} :
    v ∈ fixVecT S ↔ ∀ g ∈ S, gᵀ *ᵥ v = v := by
  constructor
  · intro h g hg
    exact h _ ⟨g, hg, rfl⟩
  · rintro h _ ⟨g, hg, rfl⟩
    exact h g hg

@[expose] def commVec (S : Set (Matrix (Fin 3) (Fin 3) K)) : Submodule K (Fin 3 → K) :=
  ⨆ g ∈ S, LinearMap.range (Matrix.toLin' (g - 1))

variable {S : Set (Matrix (Fin 3) (Fin 3) K)}

theorem fixVec_le_ker {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) :
    fixVec S ≤ LinearMap.ker (Matrix.toLin' (g - 1)) := by
  intro v hv
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, one_mulVec, hv g hg, sub_self]

theorem range_le_commVec {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) :
    LinearMap.range (Matrix.toLin' (g - 1)) ≤ commVec S :=
  le_iSup₂ (f := fun g (_ : g ∈ S) => LinearMap.range (Matrix.toLin' (g - 1))) g hg

theorem commVec_le_fixVec (h2 : (2 : K) = 0) (hS2 : ∀ g ∈ S, g * g = 1)
    (hSc : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) : commVec S ≤ fixVec S := by
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨v, rfl⟩ h hh
  have hcomm : (h - 1) * (g - 1) = (g - 1) * (h - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul, hSc h hh g hg]
    abel
  have hx : (h - 1) * (g - 1) = 0 :=
    mul_eq_zero_of_mul_self (sub_one_mul_self h2 (hS2 h hh)) (sub_one_mul_self h2 (hS2 g hg)) hcomm
  have e : (h - 1) *ᵥ ((g - 1) *ᵥ v) = 0 := by rw [mulVec_mulVec, hx, zero_mulVec]
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at e
  rw [Matrix.toLin'_apply]
  exact e

@[expose] noncomputable def homOf {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) :
    ((Fin 3 → K) ⧸ fixVec S) →ₗ[K] commVec S :=
  (fixVec S).liftQ ((Matrix.toLin' (g - 1)).codRestrict (commVec S)
    fun v => range_le_commVec hg (LinearMap.mem_range_self _ v))
    (by rw [LinearMap.ker_codRestrict]; exact fixVec_le_ker hg)

theorem homOf_mk {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) (v : Fin 3 → K) :
    ((homOf hg (Submodule.Quotient.mk v) : commVec S) : Fin 3 → K) = (g - 1) *ᵥ v := by
  rw [homOf, Submodule.liftQ_apply, LinearMap.codRestrict_apply, Matrix.toLin'_apply]

theorem card_le_pow [Finite K] :
    Nat.card S ≤
      Nat.card K ^ (finrank K ((Fin 3 → K) ⧸ fixVec S) * finrank K (commVec S)) := by
  have : Finite (((Fin 3 → K) ⧸ fixVec S) →ₗ[K] commVec S) := Module.finite_of_finite K
  let f : S → (((Fin 3 → K) ⧸ fixVec S) →ₗ[K] commVec S) := fun g => homOf g.2
  have hf : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ hgh
    have e : Matrix.toLin' (g - 1) = Matrix.toLin' (h - 1) := by
      refine LinearMap.ext fun v => ?_
      have := congrArg (fun φ : ((Fin 3 → K) ⧸ fixVec S) →ₗ[K] commVec S =>
        ((φ (Submodule.Quotient.mk v) : commVec S) : Fin 3 → K)) hgh
      simp only [f, homOf_mk] at this
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      exact this
    have e' : g - 1 = h - 1 := Matrix.toLin'.injective e
    exact Subtype.ext (sub_left_injective e')
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Module.natCard_eq_pow_finrank (K := K)
    (V := ((Fin 3 → K) ⧸ fixVec S) →ₗ[K] commVec S), Module.finrank_linearMap] at h1

theorem fixVecT_eq_orthogonal :
    fixVecT S = (Matrix.toBilin' (1 : Matrix (Fin 3) (Fin 3) K)).orthogonal (commVec S) := by
  ext v
  rw [mem_fixVecT, LinearMap.BilinForm.mem_orthogonal_iff]
  have key : ∀ (g : Matrix (Fin 3) (Fin 3) K) (u : Fin 3 → K),
      (Matrix.toBilin' (1 : Matrix (Fin 3) (Fin 3) K)) ((g - 1) *ᵥ u) v =
        u ⬝ᵥ ((gᵀ *ᵥ v) - v) := by
    intro g u
    rw [Matrix.toBilin'_apply', one_mulVec, ← vecMul_transpose, ← dotProduct_mulVec,
      transpose_sub, transpose_one, sub_mulVec, one_mulVec]
  constructor
  · intro h n hn
    have hle : commVec S ≤ LinearMap.ker
        (LinearMap.flip (Matrix.toBilin' (1 : Matrix (Fin 3) (Fin 3) K)) v) := by
      refine iSup₂_le fun g hg => ?_
      rintro _ ⟨u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.flip_apply, Matrix.toLin'_apply, key, h g hg, sub_self,
        dotProduct_zero]
    have := hle hn
    rwa [LinearMap.mem_ker, LinearMap.flip_apply] at this
  · intro h g hg
    rw [← sub_eq_zero]
    funext i
    have := h ((g - 1) *ᵥ Pi.single i 1)
      (range_le_commVec hg ⟨Pi.single i 1, Matrix.toLin'_apply _ _⟩)
    rw [key, single_one_dotProduct] at this
    exact this

theorem finrank_fixVecT : finrank K (fixVecT S) = 3 - finrank K (commVec S) := by
  rw [fixVecT_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal, Module.finrank_fin_fun]
  rw [LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero, det_one]
  exact one_ne_zero

theorem fixVec_ne_top {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) (hg1 : g ≠ 1) :
    fixVec S ≠ ⊤ := by
  intro htop
  refine hg1 (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  have hv : v ∈ fixVec S := by rw [htop]; trivial
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  exact hv g hg

theorem commVec_ne_bot {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) (hg1 : g ≠ 1) :
    commVec S ≠ ⊥ := by
  intro hbot
  have hle := range_le_commVec hg
  rw [hbot, le_bot_iff, LinearMap.range_eq_bot] at hle
  refine hg1 (sub_eq_zero.mp (Matrix.toLin'.injective ?_))
  rw [hle, map_zero]

end Mat

section Count

variable {K : Type*} [Field K] [Finite K] {S : Set (Matrix (Fin 3) (Fin 3) K)}

omit [Finite K] in
private theorem dims (h2 : (2 : K) = 0) (hS2 : ∀ g ∈ S, g * g = 1)
    (hSc : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) :
    finrank K ((Fin 3 → K) ⧸ fixVec S) + finrank K (fixVec S) = 3 ∧
      finrank K (commVec S) ≤ finrank K (fixVec S) := by
  refine ⟨?_, Submodule.finrank_mono (commVec_le_fixVec h2 hS2 hSc)⟩
  rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fin_fun]

theorem card_le_sq (h2 : (2 : K) = 0) (hS2 : ∀ g ∈ S, g * g = 1)
    (hSc : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) : Nat.card S ≤ Nat.card K ^ 2 := by
  obtain ⟨hq, hd⟩ := dims h2 hS2 hSc
  have h1 := card_le_pow (S := S)
  set ν := finrank K ((Fin 3 → K) ⧸ fixVec S)
  set d := finrank K (commVec S)
  have hνd : ν * d ≤ 2 := by
    have : ν ≤ 3 := by omega
    have : d ≤ 3 := by omega
    interval_cases ν <;> interval_cases d <;> omega
  exact h1.trans (Nat.pow_le_pow_right Nat.card_pos hνd)

theorem card_fixVec_mul_le {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) (hg1 : g ≠ 1) :
    Nat.card (fixVec S) * Nat.card K ≤ Nat.card K ^ 3 := by
  have hlt := Submodule.finrank_lt (fixVec_ne_top hg hg1)
  rw [Module.finrank_fin_fun] at hlt
  rw [Module.natCard_eq_pow_finrank (K := K), ← pow_succ]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem card_fixVecT_mul_le {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S) (hg1 : g ≠ 1) :
    Nat.card (fixVecT S) * Nat.card K ≤ Nat.card K ^ 3 := by
  have hd := Submodule.one_le_finrank_iff.mpr (commVec_ne_bot hg hg1)
  rw [Module.natCard_eq_pow_finrank (K := K), ← pow_succ, finrank_fixVecT]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem card_mul_le (h2 : (2 : K) = 0) (hS2 : ∀ g ∈ S, g * g = 1)
    (hSc : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) {g : Matrix (Fin 3) (Fin 3) K} (hg : g ∈ S)
    (hg1 : g ≠ 1) :
    Nat.card K * Nat.card S * Nat.card (fixVec S) * Nat.card (fixVecT S) ≤ Nat.card K ^ 6 := by
  obtain ⟨hq, hd⟩ := dims h2 hS2 hSc
  have h1 := card_le_pow (S := S)
  have hν := Submodule.finrank_lt (fixVec_ne_top hg hg1)
  rw [Module.finrank_fin_fun] at hν
  have hd1 := Submodule.one_le_finrank_iff.mpr (commVec_ne_bot hg hg1)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := fixVec S),
    Module.natCard_eq_pow_finrank (K := K) (V := fixVecT S), finrank_fixVecT]
  set ν := finrank K ((Fin 3 → K) ⧸ fixVec S)
  set d := finrank K (commVec S)
  set c := finrank K (fixVec S)
  have hexp : 1 + ν * d + c + (3 - d) ≤ 6 := by
    have : ν ≤ 3 := by omega
    have : d ≤ 3 := by omega
    interval_cases ν <;> interval_cases d <;> omega
  calc Nat.card K * Nat.card S * Nat.card K ^ c * Nat.card K ^ (3 - d)
      ≤ Nat.card K * Nat.card K ^ (ν * d) * Nat.card K ^ c * Nat.card K ^ (3 - d) := by
        gcongr
    _ = Nat.card K ^ (1 + ν * d + c + (3 - d)) := by ring
    _ ≤ Nat.card K ^ 6 := Nat.pow_le_pow_right Nat.card_pos hexp

end Count

end CFSG.Quasithin.SmithD310U
