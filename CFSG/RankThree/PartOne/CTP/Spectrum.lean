module

public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open scoped MatrixGroups

section BlkGroup

variable (F : Type*) [Field F]

theorem sl_inv_mulVec (a : SL(3, F)) (v : Fin 3 → F) :
    (↑a⁻¹ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((a : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem sl_mulVec_inv (a : SL(3, F)) (v : Fin 3 → F) :
    (a : Matrix (Fin 3) (Fin 3) F) *ᵥ ((↑a⁻¹ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def blkGroup (W ℓ : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) where
  carrier := {g | (∀ v ∈ ℓ, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) ∧
    ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · simp [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hb1 v hv, ha1 v hv]
    · simp [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ha2, hb2]
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · have := ha1 v hv
      calc (↑a⁻¹ : Matrix (Fin 3) (Fin 3) F) *ᵥ v
          = (↑a⁻¹ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((a : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
            rw [this]
        _ = v := sl_inv_mulVec F a v
    · rw [← ha2 ((↑a⁻¹ : Matrix (Fin 3) (Fin 3) F) *ᵥ v), sl_mulVec_inv]

end BlkGroup

section Position

variable {F : Type*} [Field F]

private theorem finrank_span_pair {V : Type*} [AddCommGroup V] [Module F V] {x y : V}
    (h : LinearIndependent F ![x, y]) : Module.finrank F (Submodule.span F {x, y}) = 2 := by
  have := finrank_span_eq_card h
  rw [Matrix.range_cons_cons_empty] at this
  simpa using this

private theorem eq_span_pair {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Submodule F V) {x y : V} (hli : LinearIndependent F ![x, y]) (hx : x ∈ S) (hy : y ∈ S)
    (hS : Module.finrank F S = 2) : S = Submodule.span F {x, y} := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · exact Submodule.span_le.mpr (by
      rintro z (rfl | rfl)
      · exact hx
      · exact hy)
  · rw [finrank_span_pair hli, hS]

private theorem eq_span_singleton {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Submodule F V) {x : V} (hx0 : x ≠ 0) (hx : x ∈ S) (hS : Module.finrank F S = 1) :
    S = Submodule.span F {x} := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · exact Submodule.span_le.mpr (by simpa using hx)
  · rw [finrank_span_singleton hx0, hS]

private theorem finrank_line_of_isCompl {W ℓ : Submodule F (Fin 3 → F)} (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) : Module.finrank F ℓ = 1 := by
  have := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun, hW] at this
  omega

private theorem stable_split (W ℓ S : Submodule F (Fin 3 → F)) (hc : IsCompl W ℓ)
    (M : Matrix (Fin 3) (Fin 3) F) (a b : F) (hab : a ≠ b)
    (hW : ∀ w ∈ W, M.mulVec w = a • w) (hℓ : ∀ u ∈ ℓ, M.mulVec u = b • u)
    (hS : ∀ v ∈ S, M.mulVec v ∈ S) {v : Fin 3 → F} (hv : v ∈ S) :
    ∃ w ∈ W ⊓ S, ∃ u ∈ ℓ ⊓ S, v = w + u := by
  obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h1 : (a - b) • w ∈ S := by
    have := S.sub_mem (hS _ hv) (S.smul_mem b hv)
    have e : M.mulVec (w + u) - b • (w + u) = (a - b) • w := by
      rw [Matrix.mulVec_add, hW w hw, hℓ u hu, smul_add, sub_smul]
      abel
    rwa [e] at this
  have h2 : w ∈ S := by
    have := S.smul_mem (a - b)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hab', one_smul] at this
  exact ⟨w, ⟨hw, h2⟩, u, ⟨hu, by simpa using S.sub_mem hv h2⟩, rfl⟩

private theorem plane_le_of_line_eq {W₁ ℓ₁ W₂ ℓ₂ : Submodule F (Fin 3 → F)} (h₁ : IsCompl W₁ ℓ₁)
    (h₂ : IsCompl W₂ ℓ₂) (M₁ : Matrix (Fin 3) (Fin 3) F) (a₁ b₁ : F) (hab₁ : a₁ ≠ b₁)
    (hM₁W : ∀ w ∈ W₁, M₁.mulVec w = a₁ • w) (hM₁ℓ : ∀ u ∈ ℓ₁, M₁.mulVec u = b₁ • u)
    (hs₁W : ∀ v ∈ W₂, M₁.mulVec v ∈ W₂) (heq : ℓ₁ = ℓ₂) : W₂ ≤ W₁ := by
  intro v hv
  obtain ⟨w, ⟨hw, -⟩, u, ⟨hu, hu2⟩, rfl⟩ :=
    stable_split W₁ ℓ₁ W₂ h₁ M₁ a₁ b₁ hab₁ hM₁W hM₁ℓ hs₁W hv
  have : u = 0 := (Submodule.disjoint_def.mp h₂.disjoint) u hu2 (heq ▸ hu)
  rw [this, add_zero]
  exact hw

private theorem line_le_plane {W₁ ℓ₁ ℓ₂ : Submodule F (Fin 3 → F)} (h₁ : IsCompl W₁ ℓ₁)
    (hl₁ : Module.finrank F ℓ₁ = 1) (hl₂ : Module.finrank F ℓ₂ = 1) (hne : ℓ₁ ≠ ℓ₂)
    (M₁ : Matrix (Fin 3) (Fin 3) F) (a₁ b₁ : F) (hab₁ : a₁ ≠ b₁)
    (hM₁W : ∀ w ∈ W₁, M₁.mulVec w = a₁ • w) (hM₁ℓ : ∀ u ∈ ℓ₁, M₁.mulVec u = b₁ • u)
    (hs₁ℓ : ∀ v ∈ ℓ₂, M₁.mulVec v ∈ ℓ₂) : ℓ₂ ≤ W₁ := by
  have hdisj : ℓ₁ ⊓ ℓ₂ = ⊥ := by
    by_contra hbot
    apply hne
    have hle1 : ℓ₁ ⊓ ℓ₂ ≤ ℓ₁ := inf_le_left
    have hle2 : ℓ₁ ⊓ ℓ₂ ≤ ℓ₂ := inf_le_right
    have hpos : 0 < Module.finrank F (ℓ₁ ⊓ ℓ₂ : Submodule F (Fin 3 → F)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank F (ℓ₁ ⊓ ℓ₂ : Submodule F (Fin 3 → F))) with h | h
      · exact absurd (Submodule.finrank_eq_zero.mp h) hbot
      · exact h
    have a1 : Module.finrank F (ℓ₁ ⊓ ℓ₂ : Submodule F (Fin 3 → F)) ≤ 1 :=
      hl₁ ▸ Submodule.finrank_mono hle1
    have e1 : ℓ₁ ⊓ ℓ₂ = ℓ₁ := Submodule.eq_of_le_of_finrank_eq hle1 (by omega)
    have e2 : ℓ₁ ⊓ ℓ₂ = ℓ₂ := Submodule.eq_of_le_of_finrank_eq hle2 (by omega)
    rw [← e1, e2]
  intro v hv
  obtain ⟨w, ⟨hw, -⟩, u, ⟨hu, hu2⟩, rfl⟩ :=
    stable_split W₁ ℓ₁ ℓ₂ h₁ M₁ a₁ b₁ hab₁ hM₁W hM₁ℓ hs₁ℓ hv
  have : u = 0 := by
    have : u ∈ ℓ₁ ⊓ ℓ₂ := ⟨hu, hu2⟩
    rw [hdisj] at this
    exact this
  rw [this, add_zero]
  exact hw

private theorem exists_basis_aux {W₁ ℓ₁ W₂ ℓ₂ : Submodule F (Fin 3 → F)} (h₁ : IsCompl W₁ ℓ₁)
    (d₁ : Module.finrank F W₁ = 2) (h₂ : IsCompl W₂ ℓ₂) (d₂ : Module.finrank F W₂ = 2)
    (hl₁ : ℓ₁ ≤ W₂) (hl₂ : ℓ₂ ≤ W₁) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      W₁ = Submodule.span F {b 0, b 1} ∧ ℓ₁ = Submodule.span F {b 2} ∧
      W₂ = Submodule.span F {b 1, b 2} ∧ ℓ₂ = Submodule.span F {b 0} := by
  have e₁ : Module.finrank F ℓ₁ = 1 := finrank_line_of_isCompl h₁ d₁
  have e₂ : Module.finrank F ℓ₂ = 1 := finrank_line_of_isCompl h₂ d₂
  have hne1 : ℓ₁ ≠ ⊥ := fun h => by rw [h, finrank_bot] at e₁; omega
  have hne2 : ℓ₂ ≠ ⊥ := fun h => by rw [h, finrank_bot] at e₂; omega
  obtain ⟨u₃, hu₃, hu₃0⟩ := (Submodule.ne_bot_iff _).mp hne1
  obtain ⟨u₁, hu₁, hu₁0⟩ := (Submodule.ne_bot_iff _).mp hne2
  have hinf : W₁ ⊓ W₂ ≠ ⊥ := by
    intro hbot
    have h := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
    rw [hbot, finrank_bot, d₁, d₂] at h
    have := Submodule.finrank_le (W₁ ⊔ W₂)
    rw [Module.finrank_fin_fun] at this
    omega
  obtain ⟨u₂, ⟨hu₂1, hu₂2⟩, hu₂0⟩ := (Submodule.ne_bot_iff _).mp hinf
  have hli : LinearIndependent F ![u₁, u₂, u₃] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    have hg2 : g 2 = 0 := by
      have hmem : g 2 • u₃ ∈ W₁ := by
        have : g 2 • u₃ = -(g 0 • u₁ + g 1 • u₂) := by
          rw [eq_neg_iff_add_eq_zero, ← hg]; abel
        rw [this]
        exact W₁.neg_mem (W₁.add_mem (W₁.smul_mem _ (hl₂ hu₁)) (W₁.smul_mem _ hu₂1))
      have := (Submodule.disjoint_def.mp h₁.disjoint) _ hmem (ℓ₁.smul_mem _ hu₃)
      exact (smul_eq_zero.mp this).resolve_right hu₃0
    rw [hg2, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := by
      have hmem : g 0 • u₁ ∈ W₂ := by
        have : g 0 • u₁ = -(g 1 • u₂) := by
          rw [eq_neg_iff_add_eq_zero, hg]
        rw [this]
        exact W₂.neg_mem (W₂.smul_mem _ hu₂2)
      have := (Submodule.disjoint_def.mp h₂.disjoint) _ hmem (ℓ₂.smul_mem _ hu₁)
      exact (smul_eq_zero.mp this).resolve_right hu₁0
    rw [hg0, zero_smul, zero_add] at hg
    have hg1 : g 1 = 0 := (smul_eq_zero.mp hg).resolve_right hu₂0
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  let b : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = ![u₁, u₂, u₃] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb0 : b 0 = u₁ := by rw [hb]; rfl
  have hb1 : b 1 = u₂ := by rw [hb]; rfl
  have hb2 : b 2 = u₃ := by rw [hb]; rfl
  have hli01 : LinearIndependent F ![b 0, b 1] := by
    have := b.linearIndependent.comp (![0, 1] : Fin 2 → Fin 3) (by decide)
    convert this using 1
    ext i; fin_cases i <;> rfl
  have hli12 : LinearIndependent F ![b 1, b 2] := by
    have := b.linearIndependent.comp (![1, 2] : Fin 2 → Fin 3) (by decide)
    convert this using 1
    ext i; fin_cases i <;> rfl
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · exact eq_span_pair W₁ hli01 (hb0 ▸ hl₂ hu₁) (hb1 ▸ hu₂1) d₁
  · exact eq_span_singleton ℓ₁ (hb2 ▸ hu₃0) (hb2 ▸ hu₃) e₁
  · exact eq_span_pair W₂ hli12 (hb1 ▸ hu₂2) (hb2 ▸ hl₁ hu₃) d₂
  · exact eq_span_singleton ℓ₂ (hb0 ▸ hu₁0) (hb0 ▸ hu₁) e₂

end Position

section Eigenbasis

theorem exists_eigenbasis_of_pow_eq_one {F : Type*} [Field F] {m : ℕ} [NeZero m] {ζ : F}
    (hζ : IsPrimitiveRoot ζ m) (A : Matrix (Fin 3) (Fin 3) F) (hA : A ^ m = 1) :
    ∃ (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, A.mulVec (b i) = d i • b i := by
  obtain ⟨b, μ, hb⟩ := CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ
    (fun _ : Unit => Matrix.toLinAlgEquiv' A) (fun _ _ => Commute.refl _)
    (fun _ => by rw [← map_pow, hA, map_one])
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun F)), fun i =>
    μ () ((finCongr (Module.finrank_fin_fun F)).symm i), fun i => ?_⟩
  have := hb () ((finCongr (Module.finrank_fin_fun F)).symm i)
  simpa [Module.Basis.reindex_apply] using this

theorem exists_primitiveRoot_of_prime_dvd {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card F - 1) : ∃ ζ : F, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
  exact ⟨x, IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)⟩

private theorem eq_one_of_mul_self_eq_one {F : Type*} [Field F] [CharP F 2] {x : F}
    (h : x * x = 1) : x = 1 := by
  have h2 : (x + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
  rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]

theorem exists_coord_equiv {F : Type*} [Field F] (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    ∃ Φ : Matrix (Fin 3) (Fin 3) F ≃ₐ[F] Matrix (Fin 3) (Fin 3) F,
      (∀ B, (Φ B).det = B.det) ∧ (∀ B i j, Φ B i j = b.repr (B.mulVec (b j)) i) ∧
        (∀ B x, (Φ B).mulVec (b.repr x) = b.repr (B.mulVec x)) ∧
        ∀ (d : Fin 3 → F) (A : Matrix (Fin 3) (Fin 3) F), (∀ i, A.mulVec (b i) = d i • b i) →
          Φ A = diagonal d := by
  refine ⟨(Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) F ≃ₐ[F] _).trans
    (LinearMap.toMatrixAlgEquiv b), ?_, ?_, ?_, ?_⟩
  · intro B
    change ((LinearMap.toMatrix b b) (Matrix.toLin' B)).det = B.det
    rw [LinearMap.det_toMatrix, LinearMap.det_toLin']
  · intro B i j
    change (LinearMap.toMatrix b b) (Matrix.toLin' B) i j = _
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply]
  · intro B x
    change ((LinearMap.toMatrix b b) (Matrix.toLin' B)).mulVec _ = _
    rw [LinearMap.toMatrix_mulVec_repr, Matrix.toLin'_apply]
  · intro d A hb
    ext i j
    change (LinearMap.toMatrix b b) (Matrix.toLin' A) i j = _
    rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, hb j, map_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h, Ne.symm h]

theorem repr_mulVec_of_eigen {F : Type*} [Field F] (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (d : Fin 3 → F) (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i)
    (v : Fin 3 → F) (i : Fin 3) : b.repr (M.mulVec v) i = d i * b.repr v i := by
  obtain ⟨Φ, -, -, hΦvec, hΦdiag⟩ := exists_coord_equiv b
  have := congrFun (hΦvec M v) i
  rw [hΦdiag d M hb, Matrix.mulVec_diagonal] at this
  exact this.symm

theorem mulVec_eq_smul_iff {F : Type*} [Field F] (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (d : Fin 3 → F) (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i)
    (a : F) (v : Fin 3 → F) : M.mulVec v = a • v ↔ ∀ i, d i * b.repr v i = a * b.repr v i := by
  constructor
  · intro h i
    have := congrArg (fun x => b.repr x i) h
    simpa [repr_mulVec_of_eigen b d M hb] using this
  · intro h
    apply b.repr.injective
    ext i
    simpa [repr_mulVec_of_eigen b d M hb] using h i

private theorem exists_eq_of_eigenvector {F : Type*} [Field F]
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F) (A : Matrix (Fin 3) (Fin 3) F)
    (hb : ∀ i, A.mulVec (b i) = d i • b i) {x : Fin 3 → F} (hx0 : x ≠ 0) {l : F}
    (hx : A.mulVec x = l • x) : ∃ i, d i = l := by
  by_contra hcon
  push Not at hcon
  apply hx0
  apply b.repr.injective
  rw [map_zero]
  ext j
  have h2 := (mulVec_eq_smul_iff b d A hb l x).mp hx j
  have h3 : (d j - l) * (b.repr x) j = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) (hcon j)
  · simpa using h4

private theorem perm_fin3_cases (π : Equiv.Perm (Fin 3)) :
    (∃ c, π c = c) ∨ (π 0 = 1 ∧ π 1 = 2 ∧ π 2 = 0) ∨ (π 0 = 2 ∧ π 1 = 0 ∧ π 2 = 1) := by
  revert π
  decide

private theorem exists_eq_one_of_inverting {F : Type*} [Field F] [CharP F 2] (d : Fin 3 → F)
    (W : Matrix (Fin 3) (Fin 3) F) (hW : W.det ≠ 0)
    (h : ∀ i j, d i * W i j * d j = W i j) : ∃ c, d c = 1 := by
  obtain ⟨π, -, hπ⟩ : ∃ π ∈ Finset.univ, Equiv.Perm.sign π • ∏ i, W (π i) i ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rwa [← Matrix.det_apply])
  have hprod : ∏ i, W (π i) i ≠ 0 := fun h0 => hπ (by rw [h0, smul_zero])
  have hne : ∀ j, W (π j) j ≠ 0 := fun j => Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ _)
  have hd : ∀ j, d (π j) * d j = 1 := by
    intro j
    have h1 := h (π j) j
    have h2 : W (π j) j * (d (π j) * d j) = W (π j) j * 1 := by
      calc W (π j) j * (d (π j) * d j) = d (π j) * W (π j) j * d j := by ring
        _ = W (π j) j := h1
        _ = W (π j) j * 1 := (mul_one _).symm
    exact mul_left_cancel₀ (hne j) h2
  rcases perm_fin3_cases π with ⟨c, hc⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact ⟨c, eq_one_of_mul_self_eq_one (by simpa [hc] using hd c)⟩
  · have e0 := hd 0
    have e1 := hd 1
    have e2 := hd 2
    rw [h0] at e0
    rw [h1] at e1
    rw [h2] at e2
    have h02 : d 0 = d 2 := by
      have a1 : d 0 = (d 1)⁻¹ := eq_inv_of_mul_eq_one_right e0
      have a2 : d 2 = (d 1)⁻¹ := eq_inv_of_mul_eq_one_left e1
      rw [a1, a2]
    exact ⟨0, eq_one_of_mul_self_eq_one (by rwa [← h02] at e2)⟩
  · have e0 := hd 0
    have e1 := hd 1
    have e2 := hd 2
    rw [h0] at e0
    rw [h1] at e1
    rw [h2] at e2
    have h01 : d 0 = d 1 := by
      have a1 : d 0 = (d 2)⁻¹ := eq_inv_of_mul_eq_one_right e0
      have a2 : d 1 = (d 2)⁻¹ := eq_inv_of_mul_eq_one_left e2
      rw [a1, a2]
    exact ⟨0, eq_one_of_mul_self_eq_one (by rwa [← h01] at e1)⟩

private theorem spectrum_shape {F : Type*} [Field F] (d : Fin 3 → F) (c : Fin 3) (hc : d c = 1)
    (hprod : ∏ i, d i = 1) :
    ∃ (a : Fin 3) (μ : F), d a = μ ∧ ∀ i, d i = 1 ∨ d i = μ ∨ d i = μ⁻¹ := by
  rw [Fin.prod_univ_three] at hprod
  fin_cases c
  · have h12 : d 1 * d 2 = 1 := by
      simp only [Fin.zero_eta] at hc
      rwa [hc, one_mul] at hprod
    have h2 : d 2 = (d 1)⁻¹ := eq_inv_of_mul_eq_one_right h12
    refine ⟨1, d 1, rfl, fun i => ?_⟩
    fin_cases i
    · exact Or.inl hc
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h2)
  · have h02 : d 0 * d 2 = 1 := by
      simp only [Fin.mk_one] at hc
      rwa [hc, mul_one] at hprod
    have h2 : d 2 = (d 0)⁻¹ := eq_inv_of_mul_eq_one_right h02
    refine ⟨0, d 0, rfl, fun i => ?_⟩
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hc
    · exact Or.inr (Or.inr h2)
  · have h01 : d 0 * d 1 = 1 := by
      have : d 2 = 1 := hc
      rwa [this, mul_one] at hprod
    have h1 : d 1 = (d 0)⁻¹ := eq_inv_of_mul_eq_one_right h01
    refine ⟨0, d 0, rfl, fun i => ?_⟩
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h1)
    · exact Or.inl hc

private theorem galois_eigenvector {F : Type*} [Field F] (σ : F ≃+* F)
    (τ M : Matrix (Fin 3) (Fin 3) F) (hM : IsUnit M) (hfix : M * τ.map σ = τ * M) {v : Fin 3 → F}
    (hv0 : v ≠ 0) {μ : F} (hv : τ.mulVec v = μ • v) :
    ∃ x : Fin 3 → F, x ≠ 0 ∧ τ.mulVec x = σ μ • x := by
  have h1 : (τ.map σ).mulVec (σ ∘ v) = σ μ • (σ ∘ v) := by
    funext i
    have := RingHom.map_mulVec σ.toRingHom τ v i
    rw [hv] at this
    simpa using this.symm
  have hx : τ.mulVec (M.mulVec (σ ∘ v)) = σ μ • M.mulVec (σ ∘ v) := by
    rw [Matrix.mulVec_mulVec, ← hfix, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul]
  have hv'0 : (σ ∘ v) ≠ 0 := by
    intro h
    apply hv0
    funext i
    simpa using congrFun h i
  refine ⟨M.mulVec (σ ∘ v), ?_, hx⟩
  intro h
  exact hv'0 (Matrix.mulVec_injective_iff_isUnit.mpr hM (by simpa using h))

private theorem fixed_of_mem_spectrum {F : Type*} [Field F] [CharP F 2] (σ : F ≃+* F)
    (hσ : Odd (orderOf σ)) {μ : F} (hμ1 : μ ≠ 1) (hμ0 : μ ≠ 0)
    (h : σ μ = 1 ∨ σ μ = μ ∨ σ μ = μ⁻¹) : σ μ = μ := by
  rcases h with h | h | h
  · exact absurd (σ.injective (by rw [h, map_one])) hμ1
  · exact h
  · exfalso
    have hσσ : σ (σ μ) = μ := by rw [h, map_inv₀, h, inv_inv]
    have hiter : ∀ n : ℕ, (σ ^ (2 * n)) μ = μ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Nat.mul_succ, pow_add, RingAut.mul_apply, pow_two, RingAut.mul_apply, hσσ, ih]
    obtain ⟨k, hk⟩ := hσ
    have h2 : (σ ^ orderOf σ) μ = μ := by rw [pow_orderOf_eq_one]; rfl
    rw [hk, pow_succ', RingAut.mul_apply, hiter, h] at h2
    apply hμ1
    apply eq_one_of_mul_self_eq_one
    calc μ * μ = μ * μ⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel₀ hμ0

end Eigenbasis

theorem sigma_fixes_generator {F : Type} [Field F] [Finite F] [CharP F 2] (σ : F ≃+* F)
    (hσ : Odd (orderOf σ)) (τ w : SL(3, F)) (M : Matrix (Fin 3) (Fin 3) F) (hM : IsUnit M)
    (m : ℕ) (hm : 3 ≤ m) (hord : orderOf τ = m) (hprim : ∃ g : F, IsPrimitiveRoot g m)
    (hw : w * τ * w⁻¹ = τ⁻¹)
    (hfix : M * (τ : Matrix (Fin 3) (Fin 3) F).map σ = (τ : Matrix (Fin 3) (Fin 3) F) * M) :
    ∃ μ : F, IsPrimitiveRoot μ m ∧ σ μ = μ := by
  classical
  obtain ⟨ζ, hζ⟩ := hprim
  have hm0 : NeZero m := ⟨by omega⟩
  have hτpow : ∀ k : ℕ, (τ : Matrix (Fin 3) (Fin 3) F) ^ k = 1 ↔ m ∣ k := fun k => by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, ← Matrix.SpecialLinearGroup.coe_pow]
    constructor
    · intro h
      exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by simpa using congrFun (congrFun h i) j
    · intro h
      rw [h]; simp
  obtain ⟨b, d, hb⟩ := exists_eigenbasis_of_pow_eq_one hζ (τ : Matrix (Fin 3) (Fin 3) F)
    ((hτpow m).mpr dvd_rfl)
  obtain ⟨Φ, hΦdet, -, -, hΦdiag⟩ := exists_coord_equiv b
  have hΦτ := hΦdiag d _ hb
  have hτwτ : τ * w * τ = w := by
    calc τ * w * τ = τ * (w * τ * w⁻¹) * w := by group
      _ = w := by rw [hw]; group
  have hΦw : diagonal d * Φ (w : Matrix (Fin 3) (Fin 3) F) * diagonal d =
      Φ (w : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hΦτ, ← map_mul, ← map_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hτwτ]
  have hdetw : (Φ (w : Matrix (Fin 3) (Fin 3) F)).det ≠ 0 := by
    rw [hΦdet, Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
  have hent : ∀ i j, d i * Φ (w : Matrix (Fin 3) (Fin 3) F) i j * d j =
      Φ (w : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
    have := congrFun (congrFun hΦw i) j
    simpa [Matrix.mul_apply, Matrix.diagonal_apply] using this
  obtain ⟨c, hc⟩ := exists_eq_one_of_inverting d _ hdetw hent
  have hprod : ∏ i, d i = 1 := by
    rw [← Matrix.det_diagonal, ← hΦτ, hΦdet, Matrix.SpecialLinearGroup.det_coe]
  obtain ⟨a, μ, hμa, hshape⟩ := spectrum_shape d c hc hprod
  have hpowd : ∀ k : ℕ, (τ : Matrix (Fin 3) (Fin 3) F) ^ k = 1 ↔ μ ^ k = 1 := by
    intro k
    have h1 : (τ : Matrix (Fin 3) (Fin 3) F) ^ k = 1 ↔ d ^ k = 1 := by
      rw [← Φ.injective.eq_iff, map_pow, hΦτ, map_one, Matrix.diagonal_pow, ← Matrix.diagonal_one,
        Matrix.diagonal_injective.eq_iff]
      rfl
    rw [h1]
    constructor
    · intro h
      have := congrFun h a
      rw [Pi.pow_apply, hμa] at this
      exact this
    · intro h
      funext i
      rw [Pi.pow_apply]
      rcases hshape i with h' | h' | h'
      · rw [h', one_pow]; rfl
      · rw [h', h]; rfl
      · rw [h', inv_pow, h, inv_one]; rfl
  have hμ : IsPrimitiveRoot μ m :=
    ⟨(hpowd m).mp ((hτpow m).mpr dvd_rfl), fun l hl => (hτpow l).mp ((hpowd l).mpr hl)⟩
  have hμ1 : μ ≠ 1 := hμ.ne_one (by omega)
  have hμ0 : μ ≠ 0 := hμ.ne_zero (by omega)
  obtain ⟨x, hx0, hx⟩ := galois_eigenvector σ _ M hM hfix (b.ne_zero a) (by rw [hb a, hμa])
  obtain ⟨i, hi⟩ := exists_eq_of_eigenvector b d _ hb hx0 hx
  refine ⟨μ, hμ, fixed_of_mem_spectrum σ hσ hμ1 hμ0 ?_⟩
  have := hshape i
  rwa [hi] at this

section BlockHelpers

variable {F : Type*} [Field F]

theorem mem_span_pair_iff_repr (b : Module.Basis (Fin 3) F (Fin 3 → F)) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 0, b 1} ↔ b.repr v 2 = 0 := by
  constructor
  · intro hv
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
    simp [Module.Basis.repr_self]
  · intro h
    have := b.sum_repr v
    rw [Fin.sum_univ_three, h, zero_smul, add_zero] at this
    rw [← this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem mem_span_single_iff_repr (b : Module.Basis (Fin 3) F (Fin 3 → F)) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 2} ↔ b.repr v 0 = 0 ∧ b.repr v 1 = 0 := by
  constructor
  · intro hv
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    simp [Module.Basis.repr_self]
  · rintro ⟨h0, h1⟩
    have := b.sum_repr v
    rw [Fin.sum_univ_three, h0, h1, zero_smul, zero_smul, zero_add, zero_add] at this
    rw [← this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem mem_plane_iff_eigen (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1)
    (h02 : d 0 ≠ d 2) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 0, b 1} ↔ M.mulVec v = d 0 • v := by
  rw [mem_span_pair_iff_repr, mulVec_eq_smul_iff b d M hb]
  constructor
  · intro h i
    fin_cases i
    · rfl
    · simp [h01]
    · simp [h]
  · intro h
    have h3 : (d 2 - d 0) * b.repr v 2 = 0 := by linear_combination h 2
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm h02))

private theorem mem_line_iff_eigen (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1)
    (h02 : d 0 ≠ d 2) (v : Fin 3 → F) :
    v ∈ Submodule.span F {b 2} ↔ M.mulVec v = d 2 • v := by
  rw [mem_span_single_iff_repr, mulVec_eq_smul_iff b d M hb]
  constructor
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simp [h0]
    · simp [h1]
    · rfl
  · intro h
    have h0 : (d 0 - d 2) * b.repr v 0 = 0 := by linear_combination h 0
    have h1 : (d 0 - d 2) * b.repr v 1 = 0 := by
      have := h 1
      rw [← h01] at this
      linear_combination this
    exact ⟨(mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr h02),
      (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr h02)⟩

theorem isCompl_span_pair_single (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    IsCompl (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) := by
  have hc : IsCompl ({0, 1} : Set (Fin 3)) {2} := by
    have : ({0, 1} : Set (Fin 3)) = ({2} : Set (Fin 3))ᶜ := by
      ext x; fin_cases x <;> simp
    rw [this]
    exact isCompl_compl.symm
  have := b.linearIndependent.isCompl_span_image b.span_eq hc
  simpa [Set.image_pair, Set.image_singleton] using this

theorem finrank_span_pair_basis (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    Module.finrank F (Submodule.span F {b 0, b 1}) = 2 := by
  apply finrank_span_pair
  have := b.linearIndependent.comp (![0, 1] : Fin 2 → Fin 3) (by decide)
  convert this using 1
  ext i; fin_cases i <;> rfl

theorem perfect_fixes_line (H : Subgroup SL(3, F)) [Group.IsPerfect H] {v : Fin 3 → F}
    (hv : v ≠ 0)
    (hline : ∀ g ∈ H, ∃ c : F, (g : Matrix (Fin 3) (Fin 3) F).mulVec v = c • v) :
    ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
  choose! c hc using hline
  have hcmul : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g * c h := by
    intro g hg h hh
    have e : (c (g * h)) • v = (c g * c h) • v := by
      rw [← hc (g * h) (H.mul_mem hg hh), Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, hc h hh, Matrix.mulVec_smul, hc g hg, smul_smul, mul_comm]
    exact smul_left_injective F hv e
  have hc1 : c 1 = 1 := by
    have e : (c 1) • v = (1 : F) • v := by
      rw [← hc 1 H.one_mem, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, one_smul]
    exact smul_left_injective F hv e
  let χ : H →* F :=
    { toFun := fun g => c g.1
      map_one' := hc1
      map_mul' := fun g h => hcmul g.1 g.2 h.1 h.2 }
  have hsub : ∀ g : H, c g.1 = 1 := by
    intro g
    have hsub : Subsingleton χ.toHomUnits.range := by
      have : Group.IsPerfect χ.toHomUnits.range := Group.IsPerfect.range χ.toHomUnits
      infer_instance
    have h1 : (⟨χ.toHomUnits g, ⟨g, rfl⟩⟩ : χ.toHomUnits.range) = 1 := Subsingleton.elim _ _
    have h2 : χ.toHomUnits g = 1 := congrArg Subtype.val h1
    have h3 := congrArg Units.val h2
    simpa [χ] using h3
  intro g hg
  rw [hc g hg, hsub ⟨g, hg⟩, one_smul]

theorem le_blkGroup_of_comm (H : Subgroup SL(3, F)) [Group.IsPerfect H]
    (M : Matrix (Fin 3) (Fin 3) F) (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2)
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    H ≤ blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) := by
  have hWmem := mem_plane_iff_eigen b d M hb h01 h02
  have hℓmem := mem_line_iff_eigen b d M hb h01 h02
  have hcommv : ∀ g ∈ H, ∀ v, M.mulVec ((g : Matrix (Fin 3) (Fin 3) F).mulVec v) =
      (g : Matrix (Fin 3) (Fin 3) F).mulVec (M.mulVec v) := by
    intro g hg v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm g hg]
  have hmapsW : ∀ g ∈ H, ∀ v ∈ Submodule.span F {b 0, b 1},
      (g : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ Submodule.span F {b 0, b 1} := by
    intro g hg v hv
    rw [hWmem] at hv ⊢
    rw [hcommv g hg, hv, Matrix.mulVec_smul]
  have hmapsℓ : ∀ g ∈ H, ∀ v ∈ Submodule.span F {b 2},
      (g : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ Submodule.span F {b 2} := by
    intro g hg v hv
    rw [hℓmem] at hv ⊢
    rw [hcommv g hg, hv, Matrix.mulVec_smul]
  have hfix := perfect_fixes_line H (b.ne_zero 2) fun g hg =>
    Submodule.mem_span_singleton.mp (hmapsℓ g hg (b 2) (Submodule.subset_span rfl)) |>.imp
      fun c hc => hc.symm
  intro g hg
  refine ⟨fun v hv => ?_, fun v => ⟨fun hgv => ?_, hmapsW g hg v⟩⟩
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [Matrix.mulVec_smul, hfix g hg]
  · have := hmapsW g⁻¹ (H.inv_mem hg) _ hgv
    rwa [sl_inv_mulVec] at this

theorem card_blkGroup_le [Finite F] (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    Nat.card (blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2})) ≤
      Nat.card SL(2, F) := by
  obtain ⟨Φ, hΦdet, hΦ, -, -⟩ := exists_coord_equiv b
  have key : ∀ g : blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}),
      (∀ i, Φ (g : Matrix (Fin 3) (Fin 3) F) i 2 = if i = 2 then 1 else 0) ∧
      Φ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ Φ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    intro g
    obtain ⟨hg1, hg2⟩ := g.2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hΦ, hg1 (b 2) (Submodule.subset_span (Set.mem_singleton _)), Module.Basis.repr_self]
      by_cases h : i = 2
      · subst h; simp
      · simp [h]
    · rw [hΦ]
      exact (mem_span_pair_iff_repr b _).mp ((hg2 _).mpr (Submodule.subset_span (by simp)))
    · rw [hΦ]
      exact (mem_span_pair_iff_repr b _).mp ((hg2 _).mpr (Submodule.subset_span (by simp)))
  have hdet : ∀ g : blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}),
      (!![Φ (g : Matrix (Fin 3) (Fin 3) F) 0 0, Φ (g : Matrix (Fin 3) (Fin 3) F) 0 1;
        Φ (g : Matrix (Fin 3) (Fin 3) F) 1 0, Φ (g : Matrix (Fin 3) (Fin 3) F) 1 1] :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro g
    obtain ⟨h2, h20, h21⟩ := key g
    have h1 : (Φ (g : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
      rw [hΦdet]; exact Matrix.SpecialLinearGroup.det_coe (g : SL(3, F))
    have e02 : Φ (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by simpa using h2 0
    have e12 : Φ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by simpa using h2 1
    have e22 : Φ (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by simpa using h2 2
    rw [Matrix.det_fin_three, h20, h21, e02, e12, e22] at h1
    rw [Matrix.det_fin_two_of]
    linear_combination h1
  let ψ : blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) → SL(2, F) :=
    fun g => ⟨!![Φ (g : Matrix (Fin 3) (Fin 3) F) 0 0, Φ (g : Matrix (Fin 3) (Fin 3) F) 0 1;
        Φ (g : Matrix (Fin 3) (Fin 3) F) 1 0, Φ (g : Matrix (Fin 3) (Fin 3) F) 1 1], hdet g⟩
  have hinj : Function.Injective ψ := by
    intro g g' hgg
    have hm := congrArg (fun s : SL(2, F) => (s : Matrix (Fin 2) (Fin 2) F)) hgg
    have e00 := congrFun (congrFun hm 0) 0
    have e01 := congrFun (congrFun hm 0) 1
    have e10 := congrFun (congrFun hm 1) 0
    have e11 := congrFun (congrFun hm 1) 1
    simp only [ψ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
    obtain ⟨h2, h20, h21⟩ := key g
    obtain ⟨h2', h20', h21'⟩ := key g'
    have hΦeq : Φ (g : Matrix (Fin 3) (Fin 3) F) = Φ (g' : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact e00
      · exact e01
      · exact (h2 _).trans (h2' _).symm
      · exact e10
      · exact e11
      · exact (h2 _).trans (h2' _).symm
      · exact h20.trans h20'.symm
      · exact h21.trans h21'.symm
      · exact (h2 _).trans (h2' _).symm
    exact Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      have := congrFun (congrFun (Φ.injective hΦeq) i) j
      exact this)
  exact Nat.card_le_card_of_injective ψ hinj

private theorem eq_smul_basis_of_eigen_distinct (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (d : Fin 3 → F) (M : Matrix (Fin 3) (Fin 3) F) (hb : ∀ i, M.mulVec (b i) = d i • b i)
    (hd : Function.Injective d) (i : Fin 3) {v : Fin 3 → F} (hv : M.mulVec v = d i • v) :
    ∃ c : F, v = c • b i := by
  refine ⟨b.repr v i, ?_⟩
  apply b.repr.injective
  ext j
  have h := (mulVec_eq_smul_iff b d M hb (d i) v).mp hv j
  by_cases hji : j = i
  · subst hji; simp
  · have h0 : b.repr v j = 0 := by
      have h3 : (d j - d i) * b.repr v j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr fun h => hji (hd h))
    simp [h0, Module.Basis.repr_self, Ne.symm hji]

private theorem eq_bot_of_distinct (H : Subgroup SL(3, F)) [Group.IsPerfect H]
    (M : Matrix (Fin 3) (Fin 3) F) (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (hb : ∀ i, M.mulVec (b i) = d i • b i) (hd : Function.Injective d)
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hfix : ∀ i, ∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) F).mulVec (b i) = b i := fun i =>
    perfect_fixes_line H (b.ne_zero i) fun g hg => by
      have hm : M.mulVec ((g : Matrix (Fin 3) (Fin 3) F).mulVec (b i)) =
          d i • (g : Matrix (Fin 3) (Fin 3) F).mulVec (b i) := by
        rw [Matrix.mulVec_mulVec, ← hcomm g hg, ← Matrix.mulVec_mulVec, hb i,
          Matrix.mulVec_smul]
      exact eq_smul_basis_of_eigen_distinct b d M hb hd i hm
  rw [Subgroup.mem_bot]
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have : Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) F) = Matrix.mulVecLin 1 :=
      b.ext fun i => by simpa using hfix i g hg
    exact LinearMap.congr_fun this v
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    have := congrFun (congrFun h1 i) j
    exact this

private theorem exists_eq_blkGroup_aux [Finite F] (H : Subgroup SL(3, F)) [Group.IsPerfect H]
    (hcard : Nat.card H = Nat.card SL(2, F)) (M : Matrix (Fin 3) (Fin 3) F)
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F)
    (hb : ∀ i, M.mulVec (b i) = d i • b i) (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2)
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    ∃ (W ℓ : Submodule F (Fin 3 → F)) (a₀ c₀ : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
      a₀ ≠ c₀ ∧ (∀ w ∈ W, M.mulVec w = a₀ • w) ∧ (∀ u ∈ ℓ, M.mulVec u = c₀ • u) ∧
      H = blkGroup F W ℓ := by
  refine ⟨Submodule.span F {b 0, b 1}, Submodule.span F {b 2}, d 0, d 2,
    isCompl_span_pair_single b, finrank_span_pair_basis b, h02,
    fun w hw => (mem_plane_iff_eigen b d M hb h01 h02 w).mp hw,
    fun u hu => (mem_line_iff_eigen b d M hb h01 h02 u).mp hu, ?_⟩
  have hle := le_blkGroup_of_comm H M b d hb h01 h02 hcomm
  exact Subgroup.eq_of_le_of_card_ge hle (hcard ▸ card_blkGroup_le b)

end BlockHelpers

theorem exists_eq_blkGroup {F : Type} [Field F] [Finite F] (hq : 4 ≤ Nat.card F)
    (H : Subgroup SL(3, F)) [Group.IsPerfect H] (hcard : Nat.card H = Nat.card SL(2, F))
    (M : Matrix (Fin 3) (Fin 3) F)
    (hdiag : ∃ (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, M.mulVec (b i) = d i • b i)
    (hns : ¬ ∃ c : F, M = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hcomm : ∀ h ∈ H, (h : Matrix (Fin 3) (Fin 3) F) * M = M * (h : Matrix (Fin 3) (Fin 3) F)) :
    ∃ (W ℓ : Submodule F (Fin 3 → F)) (a b : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
      a ≠ b ∧ (∀ w ∈ W, M.mulVec w = a • w) ∧ (∀ u ∈ ℓ, M.mulVec u = b • u) ∧
      H = blkGroup F W ℓ := by
  obtain ⟨b, d, hb⟩ := hdiag
  have hnotconst : ¬ (d 0 = d 1 ∧ d 0 = d 2) := by
    rintro ⟨h1, h2⟩
    apply hns
    refine ⟨d 0, ?_⟩
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h : Matrix.mulVecLin M = Matrix.mulVecLin (d 0 • (1 : Matrix (Fin 3) (Fin 3) F)) :=
      b.ext fun i => by
        fin_cases i
        · simpa using hb 0
        · simpa [h1] using hb 1
        · simpa [h2] using hb 2
    exact LinearMap.congr_fun h v
  have transfer : ∀ e : Equiv.Perm (Fin 3), d (e 0) = d (e 1) → d (e 0) ≠ d (e 2) →
      ∃ (W ℓ : Submodule F (Fin 3 → F)) (a b : F), IsCompl W ℓ ∧ Module.finrank F W = 2 ∧
        a ≠ b ∧ (∀ w ∈ W, M.mulVec w = a • w) ∧ (∀ u ∈ ℓ, M.mulVec u = b • u) ∧
        H = blkGroup F W ℓ := fun e h01 h02 =>
    exists_eq_blkGroup_aux H hcard M (b.reindex e.symm) (d ∘ e)
      (fun i => by simpa using hb (e i)) h01 h02 hcomm
  by_cases h01 : d 0 = d 1
  · exact transfer 1 h01 fun h => hnotconst ⟨h01, h⟩
  by_cases h02 : d 0 = d 2
  · have e0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
    have e1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
    have e2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
    exact transfer (Equiv.swap 1 2) (by rw [e0, e1]; exact h02) (by rw [e0, e2]; exact h01)
  by_cases h12 : d 1 = d 2
  · have e0 : (finRotate 3) 0 = 1 := by decide
    have e1 : (finRotate 3) 1 = 2 := by decide
    have e2 : (finRotate 3) 2 = 0 := by decide
    exact transfer (finRotate 3) (by rw [e0, e1]; exact h12)
      (by rw [e0, e2]; exact fun h => h01 h.symm)
  exfalso
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
  have hbot := eq_bot_of_distinct H M b d hb hd hcomm
  have hcard1 : Nat.card H = 1 := by rw [hbot]; exact Subgroup.card_bot
  have hge : Nat.card F ≤ Nat.card SL(2, F) := by
    let ι : F → SL(2, F) := fun t => ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
    have hinj : Function.Injective ι := by
      intro s t hst
      have := congrFun (congrFun (congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F))
        hst) 0) 1
      simpa [ι] using this
    exact Nat.card_le_card_of_injective ι hinj
  omega

section Krylov

variable {F : Type*} [Field F]

private theorem aeval_quadratic (M : Matrix (Fin 3) (Fin 3) F) (a b c : F) :
    Polynomial.aeval M (Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C a : Polynomial F) =
      c • (M * M) + b • M + a • (1 : Matrix (Fin 3) (Fin 3) F) := by
  simp [Algebra.algebraMap_eq_smul_one, pow_two]

private theorem isUnit_aeval_of_irreducible {p : ℕ} {M : Matrix (Fin 3) (Fin 3) F} {c : F}
    (hirr : Irreducible (Polynomial.X ^ p - Polynomial.C c : Polynomial F))
    (hM : M ^ p = c • (1 : Matrix (Fin 3) (Fin 3) F))
    {g : Polynomial F} (hg : g ≠ 0) (hdeg : g.natDegree < p) : IsUnit (Polynomial.aeval M g) := by
  have hcop : IsCoprime (Polynomial.X ^ p - Polynomial.C c : Polynomial F) g := by
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd hg
    rw [Polynomial.natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨u, w, huw⟩ := hcop
  have h0 : Polynomial.aeval M (Polynomial.X ^ p - Polynomial.C c : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hM,
      Algebra.algebraMap_eq_smul_one, sub_self]
  have h1 := congrArg (Polynomial.aeval M) huw
  rw [map_add, map_mul, map_mul, h0, mul_zero, zero_add, map_one] at h1
  rw [isUnit_iff_exists]
  exact ⟨Polynomial.aeval M w, by rw [← map_mul, mul_comm, map_mul, h1], h1⟩

private theorem linearIndependent_krylov {p : ℕ} (hp3 : 3 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) F} {c : F}
    (hirr : Irreducible (Polynomial.X ^ p - Polynomial.C c : Polynomial F))
    (hM : M ^ p = c • (1 : Matrix (Fin 3) (Fin 3) F))
    {v : Fin 3 → F} (hv : v ≠ 0) :
    LinearIndependent F ![v, M.mulVec v, M.mulVec (M.mulVec v)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
  have hP : (Polynomial.C (g 2) * Polynomial.X ^ 2 + Polynomial.C (g 1) * Polynomial.X +
      Polynomial.C (g 0) : Polynomial F) = 0 := by
    by_contra hne
    have hdeg : (Polynomial.C (g 2) * Polynomial.X ^ 2 + Polynomial.C (g 1) * Polynomial.X +
        Polynomial.C (g 0) : Polynomial F).natDegree < p :=
      lt_of_le_of_lt Polynomial.natDegree_quadratic_le (by omega)
    have hu := isUnit_aeval_of_irreducible hirr hM hne hdeg
    rw [aeval_quadratic] at hu
    obtain ⟨u, hu'⟩ := hu
    have h1 : (g 2 • (M * M) + g 1 • M + g 0 • (1 : Matrix (Fin 3) (Fin 3) F)).mulVec v = 0 := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
      rw [← hg]; abel
    rw [← hu'] at h1
    apply hv
    have := congrArg (fun w => (↑u⁻¹ : Matrix (Fin 3) (Fin 3) F).mulVec w) h1
    simpa [Matrix.mulVec_mulVec] using this
  have h0 := congrArg (fun P => P.coeff 0) hP
  have h1 := congrArg (fun P => P.coeff 1) hP
  have h2 := congrArg (fun P => P.coeff 2) hP
  simp [Polynomial.coeff_X, Polynomial.coeff_C] at h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem exists_aeval_of_commute {M : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F}
    (hli : LinearIndependent F ![v, M.mulVec v, M.mulVec (M.mulVec v)])
    {A : Matrix (Fin 3) (Fin 3) F} (hA : A * M = M * A) :
    ∃ P : Polynomial F, A = Polynomial.aeval M P := by
  let B : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hB : ⇑B = ![v, M.mulVec v, M.mulVec (M.mulVec v)] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hrepr := B.sum_repr (A.mulVec v)
  simp only [Fin.sum_univ_three, hB] at hrepr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hrepr
  set c : Fin 3 → F := fun i => B.repr (A.mulVec v) i with hc
  refine ⟨Polynomial.C (c 2) * Polynomial.X ^ 2 + Polynomial.C (c 1) * Polynomial.X +
    Polynomial.C (c 0), ?_⟩
  rw [aeval_quadratic]
  set Q : Matrix (Fin 3) (Fin 3) F := c 2 • (M * M) + c 1 • M + c 0 • 1 with hQ
  have hQv : A.mulVec v = Q.mulVec v := by
    rw [hQ, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    rw [← hrepr]; abel
  have hQM : Q * M = M * Q := by
    have h1 : Commute (M * M) M := (Commute.refl M).mul_left (Commute.refl M)
    have h2 : Commute M M := Commute.refl M
    have h3 : Commute (1 : Matrix (Fin 3) (Fin 3) F) M := Commute.one_left M
    exact ((h1.smul_left (c 2)).add_left (h2.smul_left (c 1))).add_left (h3.smul_left (c 0))
  have step : ∀ w, A.mulVec w = Q.mulVec w → A.mulVec (M.mulVec w) = Q.mulVec (M.mulVec w) := by
    intro w hw
    rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_mulVec,
      ← hQM, ← Matrix.mulVec_mulVec]
  have hext : Matrix.mulVecLin A = Matrix.mulVecLin Q := by
    refine B.ext fun i => ?_
    rw [hB]
    fin_cases i
    · exact hQv
    · exact step _ hQv
    · exact step _ (step _ hQv)
  exact Matrix.ext_iff_mulVec.mpr fun w => LinearMap.congr_fun hext w

end Krylov

theorem eigenbasis_or_commutative {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card F - 1) (M : Matrix (Fin 3) (Fin 3) F) (c : F) (hc : c ≠ 0)
    (hM : M ^ p = c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    (∃ (b : Module.Basis (Fin 3) F (Fin 3 → F)) (d : Fin 3 → F),
      ∀ i, M.mulVec (b i) = d i • b i) ∨
    ∀ X Y : Matrix (Fin 3) (Fin 3) F, X * M = M * X → Y * M = M * Y → X * Y = Y * X := by
  by_cases hr : ∃ r : F, r ^ p = c
  · left
    obtain ⟨r, hr⟩ := hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hr
      exact hc hr.symm
    have hM' : (r⁻¹ • M) ^ p = 1 := by
      rw [smul_pow, hM, smul_smul, inv_pow, hr, inv_mul_cancel₀ hc, one_smul]
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_prime_dvd hp hpq
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨b, d, hb⟩ := exists_eigenbasis_of_pow_eq_one hζ (r⁻¹ • M) hM'
    refine ⟨b, fun i => r * d i, fun i => ?_⟩
    have h := hb i
    rw [Matrix.smul_mulVec] at h
    calc M.mulVec (b i) = r • (r⁻¹ • M.mulVec (b i)) := by
          rw [smul_smul, mul_inv_cancel₀ hr0, one_smul]
      _ = (r * d i) • b i := by rw [h, smul_smul]
  · right
    push Not at hr
    have hirr := X_pow_sub_C_irreducible_of_prime hp hr
    intro A B hA hB
    have hv : (Pi.single 0 1 : Fin 3 → F) ≠ 0 := by
      intro h
      simpa using congrFun h 0
    have hli := linearIndependent_krylov hp3 hirr hM hv
    obtain ⟨P, rfl⟩ := exists_aeval_of_commute hli hA
    obtain ⟨Q, rfl⟩ := exists_aeval_of_commute hli hB
    rw [← map_mul, ← map_mul, mul_comm]

theorem exists_basis_of_position {F : Type} [Field F]
    (W₁ ℓ₁ W₂ ℓ₂ : Submodule F (Fin 3 → F))
    (h₁ : IsCompl W₁ ℓ₁) (d₁ : Module.finrank F W₁ = 2)
    (h₂ : IsCompl W₂ ℓ₂) (d₂ : Module.finrank F W₂ = 2) (hne : ¬ (W₁ = W₂ ∧ ℓ₁ = ℓ₂))
    (M₁ M₂ : Matrix (Fin 3) (Fin 3) F) (a₁ b₁ a₂ b₂ : F) (hab₁ : a₁ ≠ b₁) (hab₂ : a₂ ≠ b₂)
    (hM₁W : ∀ w ∈ W₁, M₁.mulVec w = a₁ • w) (hM₁ℓ : ∀ u ∈ ℓ₁, M₁.mulVec u = b₁ • u)
    (hM₂W : ∀ w ∈ W₂, M₂.mulVec w = a₂ • w) (hM₂ℓ : ∀ u ∈ ℓ₂, M₂.mulVec u = b₂ • u)
    (hs₁W : ∀ v ∈ W₂, M₁.mulVec v ∈ W₂) (hs₁ℓ : ∀ v ∈ ℓ₂, M₁.mulVec v ∈ ℓ₂)
    (hs₂W : ∀ v ∈ W₁, M₂.mulVec v ∈ W₁) (hs₂ℓ : ∀ v ∈ ℓ₁, M₂.mulVec v ∈ ℓ₁) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      W₁ = Submodule.span F {b 0, b 1} ∧ ℓ₁ = Submodule.span F {b 2} ∧
      W₂ = Submodule.span F {b 1, b 2} ∧ ℓ₂ = Submodule.span F {b 0} := by
  have e₁ : Module.finrank F ℓ₁ = 1 := finrank_line_of_isCompl h₁ d₁
  have e₂ : Module.finrank F ℓ₂ = 1 := finrank_line_of_isCompl h₂ d₂
  have hlne : ℓ₁ ≠ ℓ₂ := by
    intro h
    have h1 : W₂ ≤ W₁ := plane_le_of_line_eq h₁ h₂ M₁ a₁ b₁ hab₁ hM₁W hM₁ℓ hs₁W h
    have h2 : W₁ ≤ W₂ := plane_le_of_line_eq h₂ h₁ M₂ a₂ b₂ hab₂ hM₂W hM₂ℓ hs₂W h.symm
    exact hne ⟨le_antisymm h2 h1, h⟩
  have hl₂ : ℓ₂ ≤ W₁ := line_le_plane h₁ e₁ e₂ hlne M₁ a₁ b₁ hab₁ hM₁W hM₁ℓ hs₁ℓ
  have hl₁ : ℓ₁ ≤ W₂ := line_le_plane h₂ e₂ e₁ hlne.symm M₂ a₂ b₂ hab₂ hM₂W hM₂ℓ hs₂ℓ
  exact exists_basis_aux h₁ d₁ h₂ d₂ hl₁ hl₂

end CFSG.RankThree.PartOne.CTP
