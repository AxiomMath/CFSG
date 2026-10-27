module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualInv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

namespace NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')
  (Q : QuadDatum K E)

theorem exists_eq_of_preserves_det (hn : 3 ≤ n)
    (hrange : ρ'.range = StatedSL n F) (hQρ : ∀ (g : Γ) (e : E), Q.Qf (ρ g e) = Q.Qf e)
    (hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1) (T : E ≃ₗ[K] E)
    (hTQ : ∀ e, Q.Qf (T e) = Q.Qf e) (hP : C.Preserves T)
    (hdet : ∀ A : Matrix (Fin n) (Fin n) F, (∀ x, (C.Ψ (T (C.inl x))).1 = A *ᵥ x) →
      A.det = 1) : ∃ g : Γ, ρ g = T := by
  have hTl : ∀ x, T (C.inl x) = C.inl (C.Ψ (T (C.inl x))).1 := fun x =>
    C.eq_inl_of_mem_W₁ (hP.1 x)
  let A₀ : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun x => (C.Ψ (T (C.inl x))).1
      map_add' := fun x x' => by simp [map_add]
      map_smul' := fun a x => by
        have h1 : C.inl (a • x) = (C.θ₁.symm a) • C.inl x := by
          rw [C.smul_inl, RingEquiv.apply_symm_apply]
        have h2 := C.smul (C.θ₁.symm a) (T (C.inl x))
        simp only [RingHom.id_apply]
        rw [h1, map_smul, h2, RingEquiv.apply_symm_apply] }
  have hA₀ : ∀ x, T (C.inl x) = C.inl (A₀ x) := hTl
  set Amat : Matrix (Fin n) (Fin n) F := LinearMap.toMatrix' A₀ with hAmat
  have hAmatv : ∀ x, Amat *ᵥ x = A₀ x := fun x => by
    rw [← Matrix.toLin'_apply, hAmat, Matrix.toLin'_toMatrix']
  have hdetA : Amat.det = 1 := hdet Amat fun x => (hAmatv x).symm
  let A : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Amat (by
    rw [hdetA]; exact one_ne_zero)
  obtain ⟨g, hg⟩ := exists_eq_of_mem_statedSL hrange (mem_statedSL_of_det (A := A) hdetA)
  let U : E →+ E :=
    (ρ g⁻¹).toAddEquiv.toAddMonoidHom.comp T.toAddEquiv.toAddMonoidHom
  have hUapp : ∀ e, U e = ρ g⁻¹ (T e) := fun e => rfl
  have hU : ∀ e, Q.Qf (U e) = Q.Qf e := fun e => by rw [hUapp, hQρ, hTQ]
  have hl : ∀ x, U (C.inl x) = C.inl x := by
    intro x
    rw [hUapp, hA₀, C.ρ_inl, map_inv, hg]
    congr 1
    show ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (A₀ x) = x
    rw [← hAmatv, Matrix.mulVec_mulVec]
    have : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Amat = 1 := Units.inv_mul A
    rw [this, Matrix.one_mulVec]
  have hr : ∀ y, U (C.inr y) ∈ C.W₂ := fun y => by
    rw [hUapp]
    exact C.ρ_mem_W₂ _ (hP.2 y)
  have hall := C.eq_self_of_isometry Q (by omega) hrange hQρ hK U hU hl hr
  refine ⟨g, LinearEquiv.ext fun e => ?_⟩
  have h := hall e
  rw [hUapp] at h
  calc ρ g e = ρ g (ρ g⁻¹ (T e)) := by rw [h]
    _ = T e := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl

end NatDualCoord

end CFSG.RankThree.GF2n.Stroth80
