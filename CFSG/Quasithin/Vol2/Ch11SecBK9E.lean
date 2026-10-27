module

public import CFSG.Quasithin.Vol2.Ch11SecBK7A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix QuadraticMap
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K]

abbrev spB (K : Type) [Field K] : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) :=
  Matrix.toBilin' (KGNat.spJ K)

theorem spB_eq_spForm (u v : Fin 2 ⊕ Fin 2 → K) :
    spB K u v = (CFSG.LieType.BorelTits.spForm 2 K).β u v := by
  rw [Matrix.toBilin'_apply']
  rfl

theorem exists_sp_of_isometry (g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K))
    (hg : ∀ u v, spB K (g u) (g v) = spB K u v) :
    ∃ γ : ↥(StatedSp 2 K), ∀ v, mat 2 K γ *ᵥ v = g v := by
  obtain ⟨γ, hγ⟩ := CFSG.LieType.BorelTits.exists_natRep_eq_of_isometry 2 K g fun u v => by
    rw [← spB_eq_spForm, ← spB_eq_spForm]
    exact hg u v
  refine ⟨γ, fun v => ?_⟩
  rw [mat_apply, ← CFSG.LieType.BorelTits.natRep_apply]
  exact hγ v

@[expose] noncomputable def linEquiv (γ : ↥(StatedSp 2 K)) :
    (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K) where
  toFun x := mat 2 K γ *ᵥ x
  invFun x := mat 2 K γ⁻¹ *ᵥ x
  map_add' := mulVec_add _
  map_smul' c x := mulVec_smul _ c x
  left_inv x := KGNat.mat_inv_mulVec γ x
  right_inv x := KGNat.mat_mulVec_inv γ x

theorem linEquiv_apply (γ : ↥(StatedSp 2 K)) (x : Fin 2 ⊕ Fin 2 → K) :
    linEquiv γ x = mat 2 K γ *ᵥ x := rfl

@[expose] def IsSpForm (Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)) : Prop :=
  ∀ x y, polar Q x y = spB K x y

@[expose] def stabQ (Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)) : Subgroup ↥(StatedSp 2 K) where
  carrier := {γ | ∀ x, Q (mat 2 K γ *ᵥ x) = Q x}
  one_mem' x := by rw [map_one, one_mulVec]
  mul_mem' {γ δ} hγ hδ x := by
    show Q (mat 2 K (γ * δ) *ᵥ x) = Q x
    rw [map_mul, ← mulVec_mulVec, hγ, hδ]
  inv_mem' {γ} hγ x := by
    show Q (mat 2 K γ⁻¹ *ᵥ x) = Q x
    rw [← hγ (mat 2 K γ⁻¹ *ᵥ x), KGNat.mat_mulVec_inv]

theorem mem_stabQ {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} {γ : ↥(StatedSp 2 K)} :
    γ ∈ stabQ Q ↔ ∀ x, Q (mat 2 K γ *ᵥ x) = Q x := Iff.rfl

theorem polar_map_of_iso {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (g : V →ₗ[K] V) (hg : ∀ x, Q (g x) = Q x) (x y : V) : polar Q (g x) (g y) = polar Q x y := by
  simp only [polar, ← map_add, hg]

theorem card_stabQ {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q) :
    Nat.card ↥(stabQ Q) = Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  let Φ : ↥(stabQ Q) → ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun γ =>
    ⟨linEquiv γ.1, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => γ.2 x⟩
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨fun γ δ h => ?_, fun g => ?_⟩)
  · have h1 := congrArg (fun g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
      (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K))) h
    exact Subtype.ext (K7.sp_ext fun x => LinearEquiv.congr_fun h1 x)
  · have hg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2
    obtain ⟨γ, hγ⟩ := exists_sp_of_isometry (g : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] _).toLinearMap
      fun u v => by
        rw [← hQ, ← hQ]
        exact polar_map_of_iso _ hg u v
    refine ⟨⟨γ, fun x => ?_⟩, Subtype.ext (LinearEquiv.ext fun x => hγ x)⟩
    rw [hγ]
    exact hg x

theorem polarBilin_nondegenerate {Q : QuadraticForm K (Fin 2 ⊕ Fin 2 → K)} (hQ : IsSpForm Q) :
    (polarBilin Q).Nondegenerate := by
  have h : polarBilin Q = spB K := LinearMap.ext₂ fun x y => hQ x y
  rw [h]
  exact KGNat.toBilin'_spJ_nondegenerate

theorem finrank_four : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 2 * 2 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
