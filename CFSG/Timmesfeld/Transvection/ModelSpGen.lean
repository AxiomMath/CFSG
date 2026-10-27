module

public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.ClassicalGroups.Alternating.Generation

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating in
theorem closure_spTrans_eq_top (n : ℕ) (F : Type) [Field F] :
    Subgroup.closure {x : StatedSp n F | ∃ (v : Fin n ⊕ Fin n → F) (c : F),
      SpExtras.mat n F x = spTrans v c} = ⊤ := by
  set β : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) := Matrix.toBilin' (spGram n F) with hβdef
  have hβ : ∀ x y, β x y = spForm x y := fun x y => Matrix.toBilin'_apply' _ _ _
  have hβa : β.IsAlt := fun x => by rw [hβ]; exact spForm_self x
  have hβn : β.Nondegenerate := by
    rw [hβdef, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
    exact (isUnit_det_of_right_inverse (B := -spGram n F)
      (by rw [Matrix.mul_neg, spGram_mul_self, neg_neg])).ne_zero
  let ρ : StatedSp n F →* LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n ⊕ Fin n) F ≃* _).toMonoidHom.comp
      (StatedSp n F).subtype
  have hρ : ∀ (g : StatedSp n F) (x : Fin n ⊕ Fin n → F),
      ((ρ g : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
        (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) x = SpExtras.mat n F g *ᵥ x :=
    fun _ _ => rfl
  have hρinj : Function.Injective ρ := fun g h hgh =>
    Subtype.ext ((Matrix.GeneralLinearGroup.toLin : GL (Fin n ⊕ Fin n) F ≃* _).injective hgh)
  rw [eq_top_iff]
  intro g _
  have h1 : ρ g ∈ bilinIsometryGroup β := fun x y => by
    rw [hρ, hρ, hβ, hβ]
    calc spForm (SpExtras.mat n F g *ᵥ x) (SpExtras.mat n F g *ᵥ y)
        = x ⬝ᵥ ((SpExtras.mat n F g)ᵀ *ᵥ (spGram n F *ᵥ (SpExtras.mat n F g *ᵥ y))) := by
          rw [Matrix.dotProduct_mulVec x (SpExtras.mat n F g)ᵀ, Matrix.vecMul_transpose]
      _ = x ⬝ᵥ (((SpExtras.mat n F g)ᵀ * spGram n F * SpExtras.mat n F g) *ᵥ y) := by
          rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
      _ = spForm x y := by rw [mat_transpose_mul]
  rw [alternating_transvection_generation hβa hβn] at h1
  have h2 : ρ g ∈ (Subgroup.closure {x : StatedSp n F | ∃ (v : Fin n ⊕ Fin n → F) (c : F),
      SpExtras.mat n F x = spTrans v c}).map ρ := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨a, c, rfl⟩
    obtain ⟨x, hx⟩ := exists_mat_eq_spTrans a (-c)
    refine ⟨x, ⟨a, -c, hx⟩, Units.ext (LinearMap.ext fun y => ?_)⟩
    change ((ρ x : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) y = _
    rw [hρ, hx, spTrans_mulVec, symplecticTransvection_apply, hβ, spForm_comm y a, neg_mul_neg]
  obtain ⟨h, hh, hhg⟩ := h2
  rwa [← hρinj hhg]

theorem eq_top_of_forall_isTransGroup_le {n : ℕ} {F : Type} [Field F] {L : Subgroup (StatedSp n F)}
    (h : ∀ (v : Fin n ⊕ Fin n → F) (X : Subgroup (StatedSp n F)), IsTransGroup v X → X ≤ L) :
    L = ⊤ := by
  rw [eq_top_iff, ← closure_spTrans_eq_top n F, Subgroup.closure_le]
  rintro x ⟨v, c, hx⟩
  obtain ⟨X, hX⟩ := exists_isTransGroup v
  exact h v X hX ((hX.1 x).2 ⟨c, hx⟩)

theorem monoidHom_eq_of_forall_spTrans {n : ℕ} {F : Type} [Field F] {G : Type*} [Group G]
    {α β : StatedSp n F →* G}
    (h : ∀ (x : StatedSp n F) (v : Fin n ⊕ Fin n → F) (c : F),
      SpExtras.mat n F x = spTrans v c → α x = β x) : α = β :=
  MonoidHom.eq_of_eqOn_dense (closure_spTrans_eq_top n F) fun x ⟨v, c, hx⟩ => h x v c hx

end ModelRank

end CFSG.Timmesfeld.Transvection
