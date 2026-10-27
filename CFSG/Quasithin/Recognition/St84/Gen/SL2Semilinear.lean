module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.LocalAnalysis.WeakClosure81.SLTwoNormalizer

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups

theorem exists_eq_smul_of_commute_SL2 {F : Type*} [Field F]
    (E : (Fin 2 → F) →+ (Fin 2 → F))
    (hE : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      E ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A : Matrix (Fin 2) (Fin 2) F).mulVec (E v)) :
    ∃ z : F, ∀ v, E v = z • v :=
  CFSG.LocalAnalysis.WeakClosure81.exists_smul_eq_of_commute_specialLinearGroup E hE

private theorem exists_ringHom_smul_of_normalizes {F : Type*} [Field F]
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ A : SL(2, F), ∃ A' : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v)
    (hT' : ∀ A' : SL(2, F), ∃ A : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v) :
    ∃ φ : F →+* F, ∀ (z : F) (v : Fin 2 → F), T (z • v) = φ z • T v := by
  classical
  let α : SL(2, F) → SL(2, F) := fun A => Classical.choose (hT A)
  have hα : ∀ (A : SL(2, F)) (v : Fin 2 → F), T (A • v) = α A • T v :=
    fun A => Classical.choose_spec (hT A)
  have hα_surj : Function.Surjective α := by
    intro A
    obtain ⟨A₀, hA₀⟩ := hT' A
    refine ⟨A₀, ?_⟩
    apply Subtype.ext
    apply Matrix.ext_of_mulVec_single
    intro j
    obtain ⟨v, hv⟩ := T.surjective (Pi.single j (1 : F))
    change (α A₀) • (Pi.single j (1 : F) : Fin 2 → F) =
      A • (Pi.single j (1 : F) : Fin 2 → F)
    rw [← hv, ← hα A₀ v, hA₀ v]
  have hTz : ∀ z : F, ∃ τ : F, ∀ w : Fin 2 → F, T (z • T.symm w) = τ • w := by
    intro z
    let E : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun w => T (z • T.symm w)
        map_zero' := by simp
        map_add' := by
          intro x y
          simp only [map_add, smul_add] }
    have hcomm : ∀ (A : SL(2, F)) (w : Fin 2 → F), E (A • w) = A • E w := by
      intro A w
      obtain ⟨A₀, rfl⟩ := hα_surj A
      have key : T.symm ((α A₀) • w) = A₀ • T.symm w := by
        have h1 : T (A₀ • T.symm w) = (α A₀) • w := by
          rw [hα A₀ (T.symm w), T.apply_symm_apply]
        rw [← h1, T.symm_apply_apply]
      calc
        E ((α A₀) • w) = T (z • T.symm ((α A₀) • w)) := rfl
        _ = T (z • (A₀ • T.symm w)) := by rw [key]
        _ = T (A₀ • (z • T.symm w)) := by rw [← smul_comm A₀ z (T.symm w)]
        _ = (α A₀) • T (z • T.symm w) := hα A₀ (z • T.symm w)
        _ = (α A₀) • E w := rfl
    obtain ⟨τ, hτ⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.exists_smul_eq_of_commute_specialLinearGroup E hcomm
    exact ⟨τ, fun w => hτ w⟩
  let φ : F → F := fun z => Classical.choose (hTz z)
  have hφ : ∀ (z : F) (w : Fin 2 → F), T (z • T.symm w) = φ z • w :=
    fun z w => Classical.choose_spec (hTz z) w
  have hφ_unique : ∀ (z τ : F),
      (∀ w : Fin 2 → F, T (z • T.symm w) = τ • w) → φ z = τ := by
    intro z τ hτ
    have h1 : φ z • T (Pi.single 0 (1 : F) : Fin 2 → F) =
        τ • T (Pi.single 0 (1 : F) : Fin 2 → F) := by
      rw [← hφ z (T (Pi.single 0 (1 : F) : Fin 2 → F))]
      exact hτ (T (Pi.single 0 (1 : F) : Fin 2 → F))
    have h2 : (φ z - τ) • T (Pi.single 0 (1 : F) : Fin 2 → F) = 0 := by
      rw [sub_smul, h1, sub_self]
    have hne : T (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
      intro h
      have he : (Pi.single 0 (1 : F) : Fin 2 → F) = 0 := by
        apply T.injective
        rw [h, map_zero]
      have h0 := congrFun he 0
      simpa using h0
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have hφ_zero : φ 0 = 0 := by
    apply hφ_unique 0 0
    intro w
    simp
  have hφ_one : φ 1 = 1 := by
    apply hφ_unique 1 1
    intro w
    simp
  have hφ_add : ∀ a b : F, φ (a + b) = φ a + φ b := by
    intro a b
    apply hφ_unique (a + b) (φ a + φ b)
    intro w
    rw [add_smul, map_add, hφ a w, hφ b w, add_smul]
  have hφ_smul : ∀ (z : F) (v : Fin 2 → F), T (z • v) = φ z • T v := by
    intro z v
    have h := hφ z (T v)
    simpa using h
  have hφ_mul : ∀ a b : F, φ (a * b) = φ a * φ b := by
    intro a b
    apply hφ_unique (a * b) (φ a * φ b)
    intro w
    have h1 : T ((a * b) • T.symm w) = φ a • T (b • T.symm w) := by
      rw [mul_smul, hφ_smul]
    rw [h1, hφ b w, smul_smul]
  refine ⟨{ toFun := φ, map_one' := hφ_one, map_mul' := hφ_mul, map_zero' := hφ_zero,
            map_add' := hφ_add }, hφ_smul⟩

private theorem bijective_ringHom_smul_of_normalizes {F : Type*} [Field F]
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ A : SL(2, F), ∃ A' : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v)
    (hT' : ∀ A' : SL(2, F), ∃ A : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v)
    (φ : F →+* F) (hφ : ∀ (z : F) (v : Fin 2 → F), T (z • v) = φ z • T v) :
    Function.Bijective φ := by
  classical
  have hsymm_fwd : ∀ A : SL(2, F), ∃ A' : SL(2, F),
      ∀ v : Fin 2 → F, T.symm (A • v) = A' • T.symm v := by
    intro A
    obtain ⟨A₀, hA₀⟩ := hT' A
    refine ⟨A₀, fun v => ?_⟩
    have h1 : T (A₀ • T.symm v) = A • v := by
      rw [hA₀ (T.symm v), T.apply_symm_apply]
    rw [← h1, T.symm_apply_apply]
  have hsymm_bwd : ∀ A' : SL(2, F), ∃ A : SL(2, F),
      ∀ v : Fin 2 → F, T.symm (A • v) = A' • T.symm v := by
    intro A'
    obtain ⟨A, hA⟩ := hT A'
    refine ⟨A, fun v => ?_⟩
    have h1 : T (A' • T.symm v) = A • v := by
      rw [hA (T.symm v), T.apply_symm_apply]
    rw [← h1, T.symm_apply_apply]
  obtain ⟨ψ, hψ⟩ := exists_ringHom_smul_of_normalizes T.symm hsymm_fwd hsymm_bwd
  have he₀_ne : (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa using h0
  have hTe₀_ne : T (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h
    apply he₀_ne
    apply T.injective
    rw [h, map_zero]
  have hψφ : ∀ a : F, ψ (φ a) = a := by
    intro a
    have h2 : a • (Pi.single 0 (1 : F) : Fin 2 → F) =
        ψ (φ a) • (Pi.single 0 (1 : F) : Fin 2 → F) := by
      calc
        a • (Pi.single 0 (1 : F) : Fin 2 → F) =
            T.symm (T (a • (Pi.single 0 (1 : F) : Fin 2 → F))) :=
          (T.symm_apply_apply _).symm
        _ = T.symm (φ a • T (Pi.single 0 (1 : F) : Fin 2 → F)) := by rw [hφ a]
        _ = ψ (φ a) • T.symm (T (Pi.single 0 (1 : F) : Fin 2 → F)) :=
          hψ (φ a) (T (Pi.single 0 (1 : F) : Fin 2 → F))
        _ = ψ (φ a) • (Pi.single 0 (1 : F) : Fin 2 → F) := by rw [T.symm_apply_apply]
    have h3 : (a - ψ (φ a)) • (Pi.single 0 (1 : F) : Fin 2 → F) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h he₀_ne
  have hφψ : ∀ b : F, φ (ψ b) = b := by
    intro b
    have h1 : T.symm (b • T (Pi.single 0 (1 : F) : Fin 2 → F)) =
        ψ b • (Pi.single 0 (1 : F) : Fin 2 → F) := by
      have h := hψ b (T (Pi.single 0 (1 : F) : Fin 2 → F))
      simpa using h
    have h2 : T (ψ b • (Pi.single 0 (1 : F) : Fin 2 → F)) =
        b • T (Pi.single 0 (1 : F) : Fin 2 → F) := by
      rw [← h1, T.apply_symm_apply]
    have h3 : b • T (Pi.single 0 (1 : F) : Fin 2 → F) =
        φ (ψ b) • T (Pi.single 0 (1 : F) : Fin 2 → F) := by
      rw [← h2]
      exact hφ (ψ b) (Pi.single 0 (1 : F) : Fin 2 → F)
    have h4 : (b - φ (ψ b)) • T (Pi.single 0 (1 : F) : Fin 2 → F) = 0 := by
      rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hTe₀_ne
  constructor
  · intro a b hab
    have h := congrArg ψ hab
    rwa [hψφ a, hψφ b] at h
  · intro b
    exact ⟨ψ b, hφψ b⟩

theorem exists_ringEquiv_of_normalizes_SL2 {F : Type*} [Field F]
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ A' : Matrix.SpecialLinearGroup (Fin 2) F,
        ∀ v, T ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
          (A' : Matrix (Fin 2) (Fin 2) F).mulVec (T v))
    (hT' : ∀ A' : Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
        ∀ v, T ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
          (A' : Matrix (Fin 2) (Fin 2) F).mulVec (T v)) :
    ∃ φ : F ≃+* F, ∀ (z : F) (v : Fin 2 → F), T (z • v) = φ z • T v := by
  classical
  have hTs : ∀ A : SL(2, F), ∃ A' : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v := by
    intro A
    obtain ⟨A', hA'⟩ := hT A
    exact ⟨A', fun v => by
      simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using hA' v⟩
  have hTs' : ∀ A' : SL(2, F), ∃ A : SL(2, F), ∀ v : Fin 2 → F, T (A • v) = A' • T v := by
    intro A'
    obtain ⟨A, hA⟩ := hT' A'
    exact ⟨A, fun v => by
      simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] using hA v⟩
  obtain ⟨φ, hφ⟩ := exists_ringHom_smul_of_normalizes T hTs hTs'
  exact ⟨RingEquiv.ofBijective φ
    (bijective_ringHom_smul_of_normalizes T hTs hTs' φ hφ), hφ⟩

theorem exists_ringEquiv_of_map_mul {F : Type*} [Field F] (l a c : F →+ F)
    (hl : Function.Bijective l) (h : ∀ y t : F, l (y * t) = a y * c t) :
    ∃ σ : F ≃+* F, (∀ x, l x = l 1 * σ x) ∧ (∀ y, a y = a 1 * σ y) ∧
      (∀ t, c t = c 1 * σ t) := by
  have hl1 : l 1 ≠ 0 := by
    intro h0
    have h1 : (1 : F) = 0 := hl.1 (by rw [h0, map_zero])
    exact one_ne_zero h1
  have h11 : l 1 = a 1 * c 1 := by rw [← h 1 1, mul_one]
  have ha1 : a 1 ≠ 0 := by
    intro h0
    exact hl1 (by rw [h11, h0, zero_mul])
  have hc1 : c 1 ≠ 0 := by
    intro h0
    exact hl1 (by rw [h11, h0, mul_zero])
  have hxl : ∀ x : F, l x = a x * c 1 := fun x => by rw [← h x 1, mul_one]
  have hyl : ∀ y : F, l y = a 1 * c y := fun y => by rw [← h 1 y, one_mul]
  have hmul : ∀ x y : F, l (x * y) * l 1 = l x * l y := by
    intro x y
    rw [h x y, h11, hxl x, hyl y]
    ring
  let σ₀ : F →+* F :=
    { toFun := fun x => l x / l 1
      map_one' := div_self hl1
      map_mul' := by
        intro x y
        rw [div_mul_div_comm, ← hmul x y]
        rw [mul_div_mul_right (l (x * y)) (l 1) hl1]
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [map_add, add_div] }
  have hbij : Function.Bijective σ₀ := by
    constructor
    · intro x y hxy
      apply hl.1
      have h' : l x / l 1 = l y / l 1 := hxy
      exact (div_left_inj' hl1).mp h'
    · intro r
      obtain ⟨x, hx⟩ := hl.2 (r * l 1)
      refine ⟨x, ?_⟩
      show l x / l 1 = r
      rw [hx]
      exact mul_div_cancel_right₀ r hl1
  refine ⟨RingEquiv.ofBijective σ₀ hbij, ?_, ?_, ?_⟩
  · intro x
    show l x = l 1 * (l x / l 1)
    exact (mul_div_cancel₀ (l x) hl1).symm
  · intro y
    show a y = a 1 * (l y / l 1)
    have hay : l y = a y * c 1 := by rw [← h y 1, mul_one]
    rw [hay, h11, mul_div_mul_right (a y) (a 1) hc1, mul_div_cancel₀ (a y) ha1]
  · intro t
    show c t = c 1 * (l t / l 1)
    have htl : l t = a 1 * c t := by rw [← h 1 t, one_mul]
    rw [htl, h11, mul_comm (a 1) (c t), mul_comm (a 1) (c 1),
      mul_div_mul_right (c t) (c 1) ha1, mul_div_cancel₀ (c t) hc1]

end CFSG.Quasithin.F112R.St84
