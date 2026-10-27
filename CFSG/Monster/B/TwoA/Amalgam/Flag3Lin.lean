module

public import CFSG.Monster.B.TwoA.Base.ConjSub

public section

namespace CFSG.Monster.B.TwoA.Amalgam

open Module

theorem exists_linearEquiv_map_eq_map_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {S T S' T' : Submodule K V} (hST : S ≤ T) (hST' : S' ≤ T')
    (hS : finrank K S = finrank K S') (hT : finrank K T = finrank K T') :
    ∃ e : V ≃ₗ[K] V, S.map (e : V →ₗ[K] V) = S' ∧ T.map (e : V →ₗ[K] V) = T' := by
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_map_eq hS
  have hT₁ : S' ≤ T.map (e₁ : V →ₗ[K] V) := he₁ ▸ Submodule.map_mono hST
  obtain ⟨e₂, he₂S, he₂T⟩ :=
    exists_linearEquiv_fix_map_eq hT₁ hST' (by rw [LinearEquiv.finrank_map_eq, hT])
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · rw [LinearEquiv.coe_trans, Submodule.map_comp, he₁, he₂S]
  · rw [LinearEquiv.coe_trans, Submodule.map_comp, he₂T]

theorem eq_one_of_forall_map_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V ≃ₗ[ZMod 2] V)
    (h : ∀ S : Submodule (ZMod 2) V, finrank (ZMod 2) S = 1 → S.map (f : V →ₗ[ZMod 2] V) = S) :
    f = 1 := by
  refine LinearEquiv.ext fun v => ?_
  change f v = v
  by_cases hv : v = 0
  · rw [hv, map_zero]
  have hS := h _ (finrank_span_singleton hv)
  have hfv : f v ∈ (ZMod 2) ∙ v := by
    rw [← hS]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hfv
  have hc2 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hc2 c with rfl | rfl
  · rw [zero_smul] at hc
    exact absurd ((f.map_eq_zero_iff).1 hc.symm) hv
  · rw [one_smul] at hc
    exact hc.symm

section Coset

variable {G M X : Type*} [Group G] [Group M] [MulAction M X]

theorem mk_eq_mk_iff_of_hom (φ : G →* M) (x₀ : X) {H : Subgroup G}
    (hH : ∀ g : G, g ∈ H ↔ φ g • x₀ = x₀) (x g : G) :
    (x : G ⧸ H) = g ↔ φ x • x₀ = φ g • x₀ := by
  rw [QuotientGroup.eq, hH, map_mul, map_inv, mul_smul, inv_smul_eq_iff, eq_comm]

theorem exists_quotient_equiv_of_hom (φ : G →* M) (x₀ : X)
    (htr : ∀ x : X, ∃ g : G, φ g • x₀ = x) {H : Subgroup G}
    (hH : ∀ g : G, g ∈ H ↔ φ g • x₀ = x₀) :
    ∃ f : G ⧸ H ≃ X, (∀ g : G, f (g : G ⧸ H) = φ g • x₀) ∧
      ∀ (g : G) (a : G ⧸ H), f (g • a) = φ g • f a := by
  let _ := MulAction.compHom X φ
  have hst : H = MulAction.stabilizer G x₀ := by
    ext g
    rw [hH, MulAction.mem_stabilizer_iff]
    rfl
  have : MulAction.IsPretransitive G X := ⟨fun x y => by
    obtain ⟨g, rfl⟩ := htr x
    obtain ⟨h, rfl⟩ := htr y
    refine ⟨h * g⁻¹, ?_⟩
    change φ (h * g⁻¹) • φ g • x₀ = φ h • x₀
    rw [← mul_smul, ← map_mul, inv_mul_cancel_right]⟩
  subst hst
  let f : G ⧸ MulAction.stabilizer G x₀ ≃ X :=
    (MulAction.orbitEquivQuotientStabilizer G x₀).symm.trans
      ((Set.equivOfEq (MulAction.orbit_eq_univ G x₀)).trans (Equiv.Set.univ X))
  have hf : ∀ g : G, f (g : G ⧸ MulAction.stabilizer G x₀) = φ g • x₀ := fun g =>
    MulAction.orbitEquivQuotientStabilizer_symm_apply G x₀ g
  refine ⟨f, hf, fun g a => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H h =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, hf, hf, map_mul, mul_smul]

end Coset

end CFSG.Monster.B.TwoA.Amalgam
