module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

namespace CFSG.StandardType

open Module CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Entries

variable {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}

theorem int_neg_pair_of_mul_eq {a b k : ℤ} (hk : k = 2 ∨ k = 3) (ha : a < 0) (hb : b < 0)
    (h : a * b = k) : (a = -1 ∧ b = -k) ∨ (a = -k ∧ b = -1) := by
  have hk3 : k ≤ 3 := by omega
  have ha' : -3 ≤ a := by nlinarith
  have hb' : -3 ≤ b := by nlinarith
  rcases hk with rfl | rfl <;> interval_cases a <;> interval_cases b <;> simp_all

theorem GGIntCartan.entries (hC : GGIntCartan M C) {i j : Γ} (hij : i ≠ j) :
    (M i j = 2 ∧ C i j = 0 ∧ C j i = 0) ∨ (M i j = 3 ∧ C i j = -1 ∧ C j i = -1) ∨
      (M i j = 4 ∧ ((C i j = -1 ∧ C j i = -2) ∨ (C i j = -2 ∧ C j i = -1))) ∨
      (M i j = 6 ∧ ((C i j = -1 ∧ C j i = -3) ∨ (C i j = -3 ∧ C j i = -1))) := by
  rcases hC.2 i j hij with h | h | ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨hm, int_neg_pair_of_mul_eq (Or.inl rfl) h2 h3 h1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hm, int_neg_pair_of_mul_eq (Or.inr rfl) h2 h3 h1⟩))

theorem GGIntCartan.pair {C₁ C₂ : Matrix Γ Γ ℤ} (h₁ : GGIntCartan M C₁) (h₂ : GGIntCartan M C₂)
    {i j : Γ} (hij : i ≠ j) :
    ((C₁ i j = C₂ i j ∧ C₁ j i = C₂ j i) ∨ (C₁ i j = C₂ j i ∧ C₁ j i = C₂ i j)) ∧
      (M i j ≤ 3 → C₁ i j = C₂ i j ∧ C₁ i j = C₂ j i) := by
  have e₁ := h₁.entries hij
  have e₂ := h₂.entries hij
  omega

@[expose] def GGAtMostOneMultipleEdge (M : CoxeterMatrix Γ) : Prop :=
  ∀ i j k l, i ≠ j → k ≠ l → 4 ≤ M i j → 4 ≤ M k l → (k = i ∧ l = j) ∨ (k = j ∧ l = i)

theorem GGIntCartan.eq_or_eq_transpose {C₁ C₂ : Matrix Γ Γ ℤ} (h₁ : GGIntCartan M C₁)
    (h₂ : GGIntCartan M C₂) (hone : GGAtMostOneMultipleEdge M) : C₁ = C₂ ∨ C₁ = C₂.transpose := by
  by_cases hex : ∃ a b, a ≠ b ∧ 4 ≤ M a b ∧ C₁ a b ≠ C₂ a b
  · obtain ⟨a, b, hab, hM, hne⟩ := hex
    have hab' := ((h₁.pair h₂ hab).1).resolve_left fun h => hne h.1
    right
    ext i j
    rw [Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij
      rw [h₁.1, h₂.1]
    by_cases h3 : M i j ≤ 3
    · exact ((h₁.pair h₂ hij).2 h3).2
    rcases hone a b i j hab hij hM (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab'.1
    · exact hab'.2
  · push Not at hex
    left
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [h₁.1, h₂.1]
    by_cases h3 : M i j ≤ 3
    · exact ((h₁.pair h₂ hij).2 h3).1
    exact hex i j hij (by omega)

end Entries

section Reindex

variable {B B' : Type*} (e : B ≃ B') {M : CoxeterMatrix B} {C : Matrix B B ℤ}

theorem GGIntCartan.reindex (hC : GGIntCartan M C) :
    GGIntCartan (M.reindex e) (Matrix.reindex e e C) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [Matrix.reindex_apply, hC.1]
  · have := hC.2 (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
    simpa [Matrix.reindex_apply, CoxeterMatrix.reindex_apply] using this

theorem GGAtMostOneMultipleEdge.reindex (h : GGAtMostOneMultipleEdge M) :
    GGAtMostOneMultipleEdge (M.reindex e) := by
  intro i j k l hij hkl h1 h2
  simp only [CoxeterMatrix.reindex_apply] at h1 h2
  rcases h (e.symm i) (e.symm j) (e.symm k) (e.symm l) (e.symm.injective.ne hij)
      (e.symm.injective.ne hkl) h1 h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨e.symm.injective h3, e.symm.injective h4⟩
  · exact Or.inr ⟨e.symm.injective h3, e.symm.injective h4⟩

theorem isFiniteType_of_ggIntCartan_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    {C₀ : Matrix (Fin n) (Fin n) ℤ} (hC₀ : GGIntCartan M₀ C₀) (hFT₀ : TauCeti.IsFiniteType C₀)
    (hone : GGAtMostOneMultipleEdge M₀) {Γ : Type*} [Fintype Γ] (e : Fin n ≃ Γ)
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan (M₀.reindex e) C) : TauCeti.IsFiniteType C := by
  have hFT : TauCeti.IsFiniteType (Matrix.reindex e e C₀) := by
    rw [Matrix.reindex_apply]
    exact hFT₀.submatrix e.symm.injective
  rcases hC.eq_or_eq_transpose (hC₀.reindex e) (hone.reindex e) with rfl | rfl
  · exact hFT
  · exact hFT.transpose

end Reindex

section Standard

theorem ggIntCartan_A (n : ℕ) : GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n) := by
  refine ⟨fun i => by simp [CartanMatrix.A], fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem ggAtMostOneMultipleEdge_A (n : ℕ) : GGAtMostOneMultipleEdge (CoxeterMatrix.A n) := by
  intro i j k l _ _ h1 _
  exfalso
  simp only [CoxeterMatrix.A, Matrix.of_apply] at h1
  split_ifs at h1 <;> omega

theorem ggIntCartan_B (n : ℕ) : GGIntCartan (CoxeterMatrix.B n) (CartanMatrix.B n) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  simp only [CoxeterMatrix.B, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem ggAtMostOneMultipleEdge_B (n : ℕ) : GGAtMostOneMultipleEdge (CoxeterMatrix.B n) := by
  intro i j k l hij hkl h1 h2
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hkl' : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
  simp only [CoxeterMatrix.B, Matrix.of_apply, Fin.ext_iff] at h1 h2
  simp only [Fin.ext_iff]
  split_ifs at h1 h2 <;> omega

theorem cartanMatrix_D_pair (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    (CartanMatrix.D n i j = 0 ∧ CartanMatrix.D n j i = 0) ∨
      (CartanMatrix.D n i j = -1 ∧ CartanMatrix.D n j i = -1) := by
  rw [(CartanMatrix.D_isSymm n).apply i j]
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem ggIntCartan_D (n : ℕ) : GGIntCartan (ggCoxeterMatrixD n) (CartanMatrix.D n) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  rw [ggCoxeterMatrixD_apply]
  rcases cartanMatrix_D_pair n hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by simp [hij, h1], h1, h2⟩
  · exact Or.inr (Or.inl ⟨by simp [hij, h1], h1, h2⟩)

theorem ggAtMostOneMultipleEdge_D (n : ℕ) : GGAtMostOneMultipleEdge (ggCoxeterMatrixD n) := by
  intro i j k l _ _ h1 _
  exfalso
  rw [ggCoxeterMatrixD_apply] at h1
  split_ifs at h1 <;> omega

theorem ggIntCartan_E₆ : GGIntCartan CoxeterMatrix.E₆ (CartanMatrix.E 6) := by
  refine ⟨by decide, fun i => ?_⟩
  fin_cases i <;> decide

theorem ggIntCartan_E₇ : GGIntCartan CoxeterMatrix.E₇ (CartanMatrix.E 7) := by
  refine ⟨by decide, fun i => ?_⟩
  fin_cases i <;> decide

theorem ggIntCartan_E₈ : GGIntCartan CoxeterMatrix.E₈ (CartanMatrix.E 8) := by
  refine ⟨by decide, fun i => ?_⟩
  fin_cases i <;> decide

theorem ggIntCartan_F₄ : GGIntCartan CoxeterMatrix.F₄ CartanMatrix.F₄ := by
  refine ⟨by decide, fun i => ?_⟩
  fin_cases i <;> decide

theorem ggIntCartan_G₂ : GGIntCartan CoxeterMatrix.G₂ CartanMatrix.G₂ := by
  refine ⟨by decide, fun i => ?_⟩
  fin_cases i <;> decide

theorem ggAtMostOneMultipleEdge_of_le_three {B : Type*} {M : CoxeterMatrix B}
    (h : ∀ i j, M i j ≤ 3) : GGAtMostOneMultipleEdge M := by
  intro i j _ _ _ _ h1 _
  have := h i j
  omega

theorem ggAtMostOneMultipleEdge_of_pair {B : Type*} {M : CoxeterMatrix B} (a b : B)
    (h : ∀ i j, 4 ≤ M i j → (i = a ∧ j = b) ∨ (i = b ∧ j = a)) : GGAtMostOneMultipleEdge M := by
  intro i j k l _ _ h1 h2
  rcases h i j h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h k l h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp

theorem ggAtMostOneMultipleEdge_E₆ : GGAtMostOneMultipleEdge CoxeterMatrix.E₆ :=
  ggAtMostOneMultipleEdge_of_le_three fun i => by fin_cases i <;> decide

theorem ggAtMostOneMultipleEdge_E₇ : GGAtMostOneMultipleEdge CoxeterMatrix.E₇ :=
  ggAtMostOneMultipleEdge_of_le_three fun i => by fin_cases i <;> decide

theorem ggAtMostOneMultipleEdge_E₈ : GGAtMostOneMultipleEdge CoxeterMatrix.E₈ :=
  ggAtMostOneMultipleEdge_of_le_three fun i => by fin_cases i <;> decide

theorem ggAtMostOneMultipleEdge_F₄ : GGAtMostOneMultipleEdge CoxeterMatrix.F₄ :=
  ggAtMostOneMultipleEdge_of_pair 1 2 fun i => by fin_cases i <;> decide

theorem ggAtMostOneMultipleEdge_G₂ : GGAtMostOneMultipleEdge CoxeterMatrix.G₂ :=
  ggAtMostOneMultipleEdge_of_pair 0 1 fun i => by fin_cases i <;> decide

end Standard

@[expose] def GGIsWeylMatrixFixed {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (n : ℕ) (e : Fin n ≃ ι), 1 ≤ n ∧ (M = (CoxeterMatrix.A n).reindex e ∨
      (2 ≤ n ∧ M = (CoxeterMatrix.B n).reindex e) ∨
      (4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e))) ∨
    (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
    (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
    (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e) ∨
    (∃ e : Fin 4 ≃ ι, M = CoxeterMatrix.F₄.reindex e) ∨
    (∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e)

theorem GGIsWeylMatrix.fixed_or_D {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M) :
    GGIsWeylMatrixFixed M ∨
      ∃ (n : ℕ) (e : Fin n ≃ ι), 4 ≤ n ∧ M = (CoxeterMatrix.D n).reindex e := by
  rcases hM with ⟨n, e, hn, h | h | ⟨hn4, h⟩⟩ | h | h | h | h | h
  · exact Or.inl (Or.inl ⟨n, e, hn, Or.inl h⟩)
  · exact Or.inl (Or.inl ⟨n, e, hn, Or.inr (Or.inl h)⟩)
  · exact Or.inl (Or.inl ⟨n, e, hn, Or.inr (Or.inr ⟨hn4, h⟩)⟩)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem GGIsWeylMatrixFixed.finite {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrixFixed M) :
    Finite ι := by
  rcases hM with ⟨n, e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;>
    exact Finite.of_equiv _ e

theorem isFiniteType_of_ggIsWeylMatrixFixed {Γ : Type} [Fintype Γ] {M : CoxeterMatrix Γ}
    (hM : GGIsWeylMatrixFixed M) {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) :
    TauCeti.IsFiniteType C := by
  rcases hM with ⟨n, e, -, rfl | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩
  · exact isFiniteType_of_ggIntCartan_reindex (ggIntCartan_A n)
      (TauCeti.isFiniteType_cartanMatrix_A n) (ggAtMostOneMultipleEdge_A n) e hC
  · exact isFiniteType_of_ggIntCartan_reindex (ggIntCartan_B n)
      (TauCeti.isFiniteType_cartanMatrix_B n) (ggAtMostOneMultipleEdge_B n) e hC
  · exact isFiniteType_of_ggIntCartan_reindex (ggIntCartan_D n)
      (TauCeti.isFiniteType_cartanMatrix_D n) (ggAtMostOneMultipleEdge_D n) e hC
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
    rw [TauCeti.DynkinType.cartanMatrix_E6] at h
    exact isFiniteType_of_ggIntCartan_reindex ggIntCartan_E₆ h ggAtMostOneMultipleEdge_E₆ e hC
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rw [TauCeti.DynkinType.cartanMatrix_E7] at h
    exact isFiniteType_of_ggIntCartan_reindex ggIntCartan_E₇ h ggAtMostOneMultipleEdge_E₇ e hC
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
    rw [TauCeti.DynkinType.cartanMatrix_E8] at h
    exact isFiniteType_of_ggIntCartan_reindex ggIntCartan_E₈ h ggAtMostOneMultipleEdge_E₈ e hC
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
    rw [TauCeti.DynkinType.cartanMatrix_F4] at h
    exact isFiniteType_of_ggIntCartan_reindex ggIntCartan_F₄ h ggAtMostOneMultipleEdge_F₄ e hC
  · have h0 := TauCeti.DynkinType.isFiniteType_cartanMatrix_G2
    rw [TauCeti.DynkinType.cartanMatrix_G2] at h0
    have h1 : TauCeti.IsFiniteType (CartanMatrix.G₂.transpose : Matrix (Fin 2) (Fin 2) ℤ) := h0
    have h := h1.transpose
    rw [Matrix.transpose_transpose] at h
    exact isFiniteType_of_ggIntCartan_reindex ggIntCartan_G₂ h ggAtMostOneMultipleEdge_G₂ e hC

theorem ggCartanFaithfulInputFixed_holds :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) (M : CoxeterMatrix Γ) (C : Matrix Γ Γ ℤ),
      GGIsWeylMatrixFixed M → ∀ (hC : GGIntCartan M C) (V : Type) [AddCommGroup V]
        [Module (ZMod p) V] (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V)
        (hα : ∀ i, α i (h i) = 2) (hP : ∀ i j, α i (h j) = (C i j : ZMod p)),
        LinearIndependent (ZMod p) h →
        Function.Injective (M.toCoxeterSystem.lift
          ⟨fun i => reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩) := by
  intro p hp hp2 Γ M C hM hC V _ _ h α hα hP hind
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Γ := hM.finite
  have : Fintype Γ := Fintype.ofFinite Γ
  classical
  exact ggCartanFaithful_of_isFiniteType hα hP hp2 (isFiniteType_of_ggIsWeylMatrixFixed hM hC) hC
    hind

theorem ggCartanFaithful_of_ggIsWeylMatrix {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Γ : Type}
    {M : CoxeterMatrix Γ} (hM : GGIsWeylMatrix M)
    (hD : ¬ ∃ (n : ℕ) (e : Fin n ≃ Γ), 4 ≤ n ∧ M = (CoxeterMatrix.D n).reindex e)
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) (hind : LinearIndependent (ZMod p) h) :
    Function.Injective (M.toCoxeterSystem.lift
      ⟨fun i => reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩) :=
  ggCartanFaithfulInputFixed_holds p Fact.out hp2 Γ M C (hM.fixed_or_D.resolve_right hD) hC V h
    α hα hP hind

end CFSG.StandardType
