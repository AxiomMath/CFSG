module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot

public section

namespace CFSG.RankThree.PartOne.KFCL.Sp

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

@[expose] def Hp (n : ℕ) : Subgroup (Equiv.Perm (Fin n ⊕ Fin n)) where
  carrier := {τ | ∀ a, τ (par a) = par (τ a)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro σ τ hσ hτ a
    simp only [Equiv.Perm.mul_apply]
    rw [hτ a, hσ]
  inv_mem' := by
    intro τ hτ a
    apply τ.injective
    rw [hτ]
    simp

theorem mem_Hp {τ : Equiv.Perm (Fin n ⊕ Fin n)} : τ ∈ Hp n ↔ ∀ a, τ (par a) = par (τ a) := Iff.rfl

omit [Field K] in
theorem sgn_eq_one [Field K] [CharP K 2] (c : Fin n ⊕ Fin n) : sgn K c = 1 := by
  rcases c with i | i
  · simp
  · simp [CharTwo.neg_eq]

section Perm

variable [CharP K 2]

theorem permMat_symplectic {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) :
    (Matrix.permMatrixHom (R := K) τ)ᵀ * gram K n * Matrix.permMatrixHom (R := K) τ = gram K n := by
  have h1 : (Matrix.permMatrixHom (R := K) τ)ᵀ = τ.permMatrix K := by
    rw [Matrix.permMatrixHom_apply, Matrix.transpose_permMatrix, inv_inv]
  rw [h1, Matrix.permMatrixHom_apply]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp only [Matrix.submatrix_apply, Equiv.Perm.inv_def, Equiv.symm_symm, id,
    _root_.CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
  by_cases h : b = par a
  · subst h
    rw [ite_eq_left (by rw [hτ a]), ite_eq_left rfl, sgn_eq_one, sgn_eq_one]
  · rw [ite_eq_right h, ite_eq_right]
    intro h'
    apply h
    apply τ.injective
    rw [h', hτ a]

@[expose] noncomputable def permSp (τ : Equiv.Perm (Fin n ⊕ Fin n)) (hτ : τ ∈ Hp n) : StatedSp n K :=
  ofSymplecticMat (Matrix.permMatrixHom τ) (permMat_symplectic hτ)

theorem mat_permSp {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) :
    mat n K (permSp τ hτ) = Matrix.permMatrixHom (R := K) τ := rfl

theorem permSp_mul {σ τ : Equiv.Perm (Fin n ⊕ Fin n)} (hσ : σ ∈ Hp n) (hτ : τ ∈ Hp n) :
    permSp (K := K) (σ * τ) ((Hp n).mul_mem hσ hτ) = permSp σ hσ * permSp τ hτ := by
  apply mat_injective
  rw [map_mul, mat_permSp, mat_permSp, mat_permSp, map_mul]

theorem permSp_one : permSp (K := K) (1 : Equiv.Perm (Fin n ⊕ Fin n)) (Hp n).one_mem = (1 : StatedSp n K) := by
  apply mat_injective
  rw [mat_permSp, map_one, map_one]

@[expose] noncomputable def permSpHom (n : ℕ) (K : Type) [Field K] [CharP K 2] :
    ↥(Hp n) →* StatedSp n K where
  toFun τ := permSp τ.1 τ.2
  map_one' := permSp_one
  map_mul' σ τ := permSp_mul σ.2 τ.2

theorem permSp_inv {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) :
    (permSp (K := K) τ hτ)⁻¹ = permSp τ⁻¹ ((Hp n).inv_mem hτ) := by
  have h : permSp (K := K) τ hτ * permSp τ⁻¹ ((Hp n).inv_mem hτ) = 1 := by
    apply mat_injective
    rw [map_mul, mat_permSp, mat_permSp, ← map_mul, mul_inv_cancel, map_one, map_one]
  exact inv_eq_of_mul_eq_one_right h

omit [CharP K 2] in
theorem permMat_conj_apply' (σ : Equiv.Perm (Fin n ⊕ Fin n)) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (a b : Fin n ⊕ Fin n) :
    (Matrix.permMatrixHom (R := K) σ⁻¹ * M * Matrix.permMatrixHom (R := K) σ) a b = M (σ a) (σ b) := by
  simp only [Matrix.permMatrixHom_apply, inv_inv]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

@[expose] noncomputable def cj {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x : StatedSp n K) :
    StatedSp n K :=
  (permSp τ hτ)⁻¹ * x * permSp τ hτ

theorem mat_cj_apply {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x : StatedSp n K)
    (a b : Fin n ⊕ Fin n) : mat n K (cj hτ x) a b = mat n K x (τ a) (τ b) := by
  unfold cj
  rw [permSp_inv, map_mul, map_mul, mat_permSp, mat_permSp]
  exact permMat_conj_apply' τ _ a b

theorem cj_mul {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x y : StatedSp n K) :
    cj hτ (x * y) = cj hτ x * cj hτ y := by
  unfold cj
  group

theorem cj_inv {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x : StatedSp n K) :
    cj hτ x⁻¹ = (cj hτ x)⁻¹ := by
  unfold cj
  group

theorem cj_cj {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) (x : StatedSp n K) :
    cj ((Hp n).inv_mem hτ) (cj hτ x) = x := by
  apply mat_injective
  ext a b
  rw [mat_cj_apply, mat_cj_apply]
  simp

end Perm

section Torus

@[expose] def spTorus (p n : ℕ) (K : Type) [Field K] : Subgroup (StatedSp n K) where
  carrier := {g | ∃ x : Fin n → K, (∀ i, x i ^ p = 1) ∧
    mat n K g = Matrix.diagonal (Sum.elim x (fun i => (x i)⁻¹))}
  mul_mem' := by
    rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
    refine ⟨x * y, fun i => by simp [mul_pow, hx i, hy i], ?_⟩
    rw [map_mul, hax, hby, Matrix.diagonal_mul_diagonal]
    congr 1
    funext c
    rcases c with i | i <;> simp [mul_comm]
  one_mem' := ⟨fun _ => 1, fun _ => one_pow _, by
    rw [map_one]
    ext a b
    rcases a with i | i <;> rcases b with j | j <;> simp [Matrix.one_apply, Matrix.diagonal_apply]⟩
  inv_mem' := by
    rintro a ⟨x, hx, hax⟩
    refine ⟨fun i => (x i)⁻¹, fun i => by rw [inv_pow, hx i, inv_one], ?_⟩
    ext r t
    rw [mat_inv_apply, hax]
    by_cases hrt : r = t
    · subst hrt
      rcases r with i | i
      · simp [sgn]
      · simp [sgn]
    · have : par t ≠ par r := fun h => hrt (par_injective h).symm
      rw [Matrix.diagonal_apply_ne _ this, Matrix.diagonal_apply_ne _ hrt, mul_zero]

variable {p : ℕ}

theorem mem_spTorus_iff {g : StatedSp n K} :
    g ∈ spTorus p n K ↔ ∃ x : Fin n → K, (∀ i, x i ^ p = 1) ∧
      mat n K g = Matrix.diagonal (Sum.elim x (fun i => (x i)⁻¹)) := Iff.rfl

theorem spTorus_apply_ne {g : StatedSp n K} (hg : g ∈ spTorus p n K) {a b : Fin n ⊕ Fin n}
    (hab : a ≠ b) : mat n K g a b = 0 := by
  obtain ⟨x, -, hx⟩ := hg
  rw [hx, Matrix.diagonal_apply_ne _ hab]

theorem spTorus_pow {g : StatedSp n K} (hg : g ∈ spTorus p n K) (a : Fin n ⊕ Fin n) :
    (mat n K g a a) ^ p = 1 := by
  obtain ⟨x, hx, hxg⟩ := hg
  rw [hxg, Matrix.diagonal_apply_eq]
  rcases a with i | i
  · simpa using hx i
  · simp [inv_pow, hx i]

theorem spTorus_par {g : StatedSp n K} (hg : g ∈ spTorus p n K) (a : Fin n ⊕ Fin n) :
    mat n K g (par a) (par a) = (mat n K g a a)⁻¹ := by
  obtain ⟨x, hx, hxg⟩ := hg
  rw [hxg, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  rcases a with i | i <;> simp [par]

theorem spTorus_ne_zero {g : StatedSp n K} (hg : g ∈ spTorus p n K) (a : Fin n ⊕ Fin n) (hp : p ≠ 0) :
    mat n K g a a ≠ 0 := by
  intro h0
  have := spTorus_pow hg a
  rw [h0, zero_pow hp] at this
  exact zero_ne_one this

variable [CharP K 2]

theorem cj_mem_spTorus {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) {g : StatedSp n K}
    (hg : g ∈ spTorus p n K) : cj hτ g ∈ spTorus p n K := by
  refine ⟨fun i => mat n K g (τ (Sum.inl i)) (τ (Sum.inl i)), fun i => spTorus_pow hg _, ?_⟩
  ext a b
  rw [mat_cj_apply]
  by_cases hab : a = b
  · subst hab
    rcases a with i | i
    · simp [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_eq]
      have : τ (Sum.inr i) = par (τ (Sum.inl i)) := by rw [← hτ]; rfl
      rw [this, spTorus_par hg]
      simp
  · have : τ a ≠ τ b := fun h => hab (τ.injective h)
    rw [spTorus_apply_ne hg this, Matrix.diagonal_apply_ne _ hab]

theorem cj_mem_spTorus_iff {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) {g : StatedSp n K} :
    cj hτ g ∈ spTorus p n K ↔ g ∈ spTorus p n K :=
  ⟨fun h => cj_cj hτ g ▸ cj_mem_spTorus ((Hp n).inv_mem hτ) h, cj_mem_spTorus hτ⟩

@[expose] noncomputable def spWeyl (n : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup (StatedSp n K) :=
  (permSpHom n K).range

theorem spWeyl_le_normalizer : spWeyl n K ≤ Subgroup.normalizer (spTorus p n K : Set (StatedSp n K)) := by
  rintro _ ⟨⟨τ, hτ⟩, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : permSp (K := K) τ hτ * x * (permSp τ hτ)⁻¹ = cj ((Hp n).inv_mem hτ) x := by
    unfold cj
    rw [← permSp_inv hτ, inv_inv]
  show x ∈ spTorus p n K ↔ permSp τ hτ * x * (permSp τ hτ)⁻¹ ∈ spTorus p n K
  rw [h1, cj_mem_spTorus_iff]

theorem mem_spWeyl_iff {w : StatedSp n K} : w ∈ spWeyl n K ↔ ∃ (τ : Equiv.Perm (Fin n ⊕ Fin n)) (hτ : τ ∈ Hp n),
    permSp τ hτ = w := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, rfl⟩
    exact ⟨τ, hτ, rfl⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩

theorem mem_map_conj_permSp_iff {τ : Equiv.Perm (Fin n ⊕ Fin n)} (hτ : τ ∈ Hp n) {H : Subgroup (StatedSp n K)}
    {x : StatedSp n K} :
    x ∈ H.map (MulAut.conj (permSp τ hτ)).toMonoidHom ↔ cj hτ x ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

end Torus

end CFSG.RankThree.PartOne.KFCL.Sp
