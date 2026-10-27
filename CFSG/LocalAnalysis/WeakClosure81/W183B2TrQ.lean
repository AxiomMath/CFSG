module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct MonoidAlgebra

private lemma w183b2_one_tmul_ne_zero {F K W : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup W] [Module F W] {w : W} (hw : w ≠ 0) :
    (1 : K) ⊗ₜ[F] w ≠ 0 := by
  intro h
  let L : F →ₗ[F] K := Algebra.linearMap F K
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective F K)
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hL
  have h2 : (TensorProduct.lid F W) (g.rTensor W ((1 : K) ⊗ₜ[F] w)) = 0 := by
    rw [h]
    simp
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h2
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg (1 : F)
    simpa [L] using this
  rw [hg1, one_smul] at h2
  exact hw h2

private theorem w183b2_quotient_isIrreducible_of_isCoatom {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (W : Subrepresentation ρ)
    (hW : IsCoatom W) : W.quotient.IsIrreducible := by
  have hne : W.toSubmodule ≠ ⊤ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial (V ⧸ W.toSubmodule) := (Submodule.Quotient.nontrivial_iff).mpr hne
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top this
  · intro S
    let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.toSubmodule.mkQ, by
      intro g v hv
      exact S.apply_mem_toSubmodule g (show W.toSubmodule.mkQ v ∈ S.toSubmodule from hv)⟩
    have hWT : W ≤ T := by
      intro v hv
      show W.toSubmodule.mkQ v ∈ S.toSubmodule
      have h0 : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
      rw [h0]
      exact S.toSubmodule.zero_mem
    rcases eq_or_lt_of_le hWT with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule y
      have hvT : v ∈ T := show W.toSubmodule.mkQ v ∈ S.toSubmodule from hy
      rw [← h] at hvT
      show W.toSubmodule.mkQ v = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hvT
    · right
      have hT : T = ⊤ := hW.2 T h
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊤
      rw [eq_top_iff]
      intro y _
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule y
      have : v ∈ T := by rw [hT]; exact Submodule.mem_top
      exact this

theorem w183b2_exists_irr_quotient {G : Type} [Group G] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] [Nontrivial W] (ρ : Representation (ZMod 2) G W) :
    ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module (AlgebraicClosure (ZMod 2)) Q)
      (_ : FiniteDimensional (AlgebraicClosure (ZMod 2)) Q)
      (σ : Representation (AlgebraicClosure (ZMod 2)) G Q) (ψ : W →+ Q),
      σ.IsIrreducible ∧ (∀ (g : G) (w : W), ψ (ρ g w) = σ g (ψ w)) ∧
        Submodule.span (AlgebraicClosure (ZMod 2)) (Set.range ψ) = ⊤ := by
  classical
  let K := AlgebraicClosure (ZMod 2)
  let P := K ⊗[ZMod 2] W
  let σ₀ : Representation K G P :=
    { toFun := fun g => (ρ g).baseChange K
      map_one' := by
        rw [map_one]
        exact LinearMap.baseChange_id
      map_mul' := by
        intro g h
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]
        rfl }
  haveI : Module.Finite (ZMod 2) W := (Module.finite_iff_finite).mpr inferInstance
  haveI hPfin : Module.Finite K P := Module.Finite.base_change (ZMod 2) K W
  have hPnt : Nontrivial P := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact ⟨(1 : K) ⊗ₜ[ZMod 2] w, 0, w183b2_one_tmul_ne_zero hw⟩
  haveI : Nontrivial P := hPnt
  haveI : Module.Finite K[G] σ₀.asModule :=
    Module.Finite.of_restrictScalars_finite K K[G] _
  have hnt : Nontrivial σ₀.asModule :=
    (Equiv.nontrivial_congr σ₀.asModuleEquiv.toEquiv).mpr inferInstance
  haveI : Nontrivial σ₀.asModule := hnt
  have : Nontrivial (Submodule K[G] σ₀.asModule) :=
    (Submodule.nontrivial_iff K[G]).mpr inferInstance
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Submodule K[G] σ₀.asModule)
  let p : Subrepresentation σ₀ := Subrepresentation.subrepresentationSubmoduleOrderIso.symm N
  have hp : IsCoatom p := (OrderIso.isCoatom_iff _ _).mpr hN
  let Q := P ⧸ p.toSubmodule
  let σ : Representation K G Q := p.quotient
  have hσ : σ.IsIrreducible := w183b2_quotient_isIrreducible_of_isCoatom σ₀ p hp
  let ψ : W →+ Q :=
    { toFun := fun w => Submodule.Quotient.mk ((1 : K) ⊗ₜ[ZMod 2] w)
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [TensorProduct.tmul_add]
        exact map_add (Submodule.mkQ p.toSubmodule) _ _ }
  have hψ : ∀ (g : G) (w : W), ψ (ρ g w) = σ g (ψ w) := by
    intro g w
    have hbase : (ρ g).baseChange K ((1 : K) ⊗ₜ[ZMod 2] w) =
        (1 : K) ⊗ₜ[ZMod 2] ρ g w := by
      rw [LinearMap.baseChange_tmul]
    change Submodule.Quotient.mk ((1 : K) ⊗ₜ[ZMod 2] ρ g w) =
      p.quotient g (Submodule.Quotient.mk ((1 : K) ⊗ₜ[ZMod 2] w))
    rw [← hbase]
    exact (Subrepresentation.quotient_apply_mk p g ((1 : K) ⊗ₜ[ZMod 2] w)).symm
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    have hgen : ∀ x : P, x ∈ Submodule.span K (Set.range fun w : W => (1 : K) ⊗ₜ[ZMod 2] w) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | tmul c w =>
        rw [TensorProduct.tmul_eq_smul_one_tmul]
        exact Submodule.smul_mem _ c (Submodule.subset_span ⟨w, rfl⟩)
      | add x y hx hy => exact Submodule.add_mem _ hx hy
    have hP : Submodule.span K (Set.range fun w : W => (1 : K) ⊗ₜ[ZMod 2] w) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact hgen x
    have hrange : Set.range ψ =
        p.toSubmodule.mkQ '' Set.range fun w : W => (1 : K) ⊗ₜ[ZMod 2] w :=
      Set.range_comp' p.toSubmodule.mkQ (fun w : W => (1 : K) ⊗ₜ[ZMod 2] w)
    rw [hrange, ← Submodule.map_span, hP, Submodule.map_top, Submodule.range_mkQ]
  exact ⟨Q, inferInstance, inferInstance, inferInstance, σ, ψ, hσ, hψ, hspan⟩

end CFSG.LocalAnalysis.WeakClosure81

end
