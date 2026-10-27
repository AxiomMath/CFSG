module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H13.L827X.SL2Orb

section Basis

variable {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E]

@[expose] noncomputable def matHom {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) :
    (E ≃ₗ[F] E) →* Matrix ι ι F :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom

section MatHom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matHom_apply (b : Module.Basis ι F E) (g : E ≃ₗ[F] E) :
    matHom b g = LinearMap.toMatrix b b (g : E →ₗ[F] E) := rfl

theorem matHom_apply_entry (b : Module.Basis ι F E) (g : E ≃ₗ[F] E) (i j : ι) :
    matHom b g i j = b.repr (g (b j)) i := by
  rw [matHom_apply, LinearMap.toMatrix_apply]
  rfl

theorem matHom_injective (b : Module.Basis ι F E) : Function.Injective (matHom b) := by
  intro g h hgh
  rw [matHom_apply, matHom_apply] at hgh
  have h1 : (g : E →ₗ[F] E) = (h : E →ₗ[F] E) := (LinearMap.toMatrix b b).injective hgh
  exact LinearEquiv.ext fun x => congrArg (fun f : E →ₗ[F] E => f x) h1

theorem det_matHom (b : Module.Basis ι F E) (g : E ≃ₗ[F] E) :
    (matHom b g).det = ((LinearEquiv.det g : Fˣ) : F) := by
  rw [matHom_apply, LinearMap.det_toMatrix, LinearEquiv.coe_det]

theorem matHom_neg (b : Module.Basis ι F E) :
    matHom b (LinearEquiv.neg F) = -1 := by
  ext i j
  rw [matHom_apply_entry, Matrix.neg_apply, Matrix.one_apply]
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

end MatHom

theorem exists_basis_zero_eq (hE : Module.finrank F E = 2) {x : E} (hx : x ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = x := by
  have hne : Submodule.span F {x} ≠ ⊤ := by
    intro htop
    have h1 := finrank_span_singleton (K := F) hx
    rw [htop, finrank_top, hE] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨y, hy⟩ : ∃ y : E, y ∉ Submodule.span F {x} := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun y _ => hcon y)
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hy
      have h2 : t • y = -(s • x) := eq_neg_of_add_eq_zero_right hst
      have hy' : y = t⁻¹ • (-(s • x)) := by
        rw [← h2, inv_smul_smul₀ ht]
      rw [hy']
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
    subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx, rfl⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hE]), ?_⟩
  simp

theorem matHom_col_zero (b : Module.Basis (Fin 2) F E) (g : E ≃ₗ[F] E) (c : F)
    (hg : g (b 0) = c • b 0) : matHom b g 0 0 = c ∧ matHom b g 1 0 = 0 := by
  constructor
  · simp [matHom_apply_entry, hg, Module.Basis.repr_self]
  · simp [matHom_apply_entry, hg, Module.Basis.repr_self]

theorem det_eq_one_of_isPerfect (Λ : Subgroup (E ≃ₗ[F] E)) [Group.IsPerfect Λ] (g : Λ) :
    LinearEquiv.det (g : E ≃ₗ[F] E) = 1 := by
  let f : Λ →* Fˣ := (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).comp Λ.subtype
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  haveI : IsMulCommutative f.range := inferInstance
  have hmem : f g ∈ f.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
  have h1 : (⟨f g, hmem⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem fixing_comm_card_dvd {G : Type*} [Group G] [Finite G] (b : Module.Basis (Fin 2) F E)
    (φ : G →* (E ≃ₗ[F] E)) (hφ : Function.Injective φ)
    (hdet : ∀ g : G, LinearEquiv.det (φ g) = 1) (hfix : ∀ g : G, φ g (b 0) = b 0) :
    IsMulCommutative G ∧ Nat.card G ∣ Nat.card F := by
  classical
  have hnorm : ∀ g : G, matHom b (φ g) 0 0 = 1 ∧ matHom b (φ g) 1 1 = 1 ∧
      matHom b (φ g) 1 0 = 0 := by
    intro g
    obtain ⟨h00, h10⟩ := matHom_col_zero b (φ g) 1 (by simpa using hfix g)
    have hd := det_matHom b (φ g)
    rw [hdet g, Matrix.det_fin_two, h00, h10] at hd
    simp only [Units.val_one, mul_zero, sub_zero, one_mul] at hd
    exact ⟨h00, hd, h10⟩
  let ι : G →* Multiplicative F :=
    { toFun := fun g => Multiplicative.ofAdd (matHom b (φ g) 0 1)
      map_one' := by
        simp only [map_one, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]
        rfl
      map_mul' := by
        intro g h
        simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
        obtain ⟨g00, g11, -⟩ := hnorm g
        obtain ⟨h00, h11, -⟩ := hnorm h
        rw [g00, h11, ← ofAdd_add]
        congr 1
        ring }
  have hι : Function.Injective ι := by
    intro g h hgh
    have h1 : matHom b (φ g) 0 1 = matHom b (φ h) 0 1 := Multiplicative.ofAdd.injective hgh
    apply hφ
    apply matHom_injective b
    obtain ⟨g00, g11, g10⟩ := hnorm g
    obtain ⟨h00, h11, h10⟩ := hnorm h
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨⟨⟨fun a c => hι ?_⟩⟩, ?_⟩
  · simp only [map_mul]
    exact mul_comm _ _
  · have hcard : Nat.card G = Nat.card (ι.range) :=
      Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
    rw [hcard]
    exact Subgroup.card_subgroup_dvd_card ι.range

end Basis

end CFSG.Quasithin.H13.L827X.SL2Orb

end
