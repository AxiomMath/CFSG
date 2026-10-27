module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped MonoidAlgebra
open scoped TensorProduct

private lemma endFieldRep_injective {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (hfaith : Function.Injective ρ) :
    Function.Injective (CFSG.endFieldRep ρ) := by
  intro g h hgh
  apply hfaith
  ext v
  have h1 : ρ.asModuleEquiv ((CFSG.endFieldRep ρ) g (ρ.asModuleEquiv.symm v)) = ρ g v := by
    rw [CFSG.endFieldRep_apply', LinearEquiv.apply_symm_apply]
  have h2 : ρ.asModuleEquiv ((CFSG.endFieldRep ρ) h (ρ.asModuleEquiv.symm v)) = ρ h v := by
    rw [CFSG.endFieldRep_apply', LinearEquiv.apply_symm_apply]
  rw [← h1, ← h2, hgh]

private lemma finrank_ker_endFieldRep_eq {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (hirr : ρ.IsIrreducible) (g : Γ) :
    Module.finrank (ZMod p)
        ((LinearMap.ker ((CFSG.endFieldRep ρ) g - 1)).restrictScalars (ZMod p)) =
      Module.finrank (ZMod p) (LinearMap.ker (ρ g - 1)) := by
  classical
  letI : Representation.IsIrreducible ρ := hirr
  let 𝔽 := Module.End (MonoidAlgebra (ZMod p) Γ) ρ.asModule
  letI : Field 𝔽 := CFSG.endField_field ρ
  letI : Module 𝔽 ρ.asModule := CFSG.endFieldModule ρ
  let T : ρ.asModule →ₗ[𝔽] ρ.asModule := (CFSG.endFieldRep ρ) g - 1
  let W : Submodule 𝔽 ρ.asModule := LinearMap.ker T
  let K : Submodule (ZMod p) F := LinearMap.ker (ρ g - 1)
  have hmemW : ∀ y : ρ.asModule, y ∈ W ↔ (CFSG.endFieldRep ρ) g y = y := by
    intro y
    simp only [W, T, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    exact sub_eq_zero
  have hmemK : ∀ x : F, x ∈ K ↔ ρ g x = x := by
    intro x
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    exact sub_eq_zero
  have hmap : (W.restrictScalars (ZMod p)).map ρ.asModuleEquiv.toLinearMap = K := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [hmemK]
      rw [show x = ρ.asModuleEquiv y from hyx.symm]
      have hy' : (CFSG.endFieldRep ρ) g y = y := (hmemW y).mp hy
      calc
        ρ g (ρ.asModuleEquiv y) = ρ.asModuleEquiv ((CFSG.endFieldRep ρ) g y) :=
          (CFSG.endFieldRep_apply' ρ g y).symm
        _ = ρ.asModuleEquiv y := by rw [hy']
    · intro hx
      refine ⟨ρ.asModuleEquiv.symm x, ?_, ?_⟩
      · change ρ.asModuleEquiv.symm x ∈ W
        rw [hmemW]
        apply ρ.asModuleEquiv.injective
        rw [CFSG.endFieldRep_apply', LinearEquiv.apply_symm_apply]
        exact (hmemK x).mp hx
      · exact ρ.asModuleEquiv.apply_symm_apply x
  change Module.finrank (ZMod p) (W.restrictScalars (ZMod p)) = Module.finrank (ZMod p) K
  have h1 : Module.finrank (ZMod p) (W.restrictScalars (ZMod p)) =
      Module.finrank (ZMod p)
        ((W.restrictScalars (ZMod p)).map ρ.asModuleEquiv.toLinearMap) :=
    (Submodule.equivMapOfInjective (p := W.restrictScalars (ZMod p))
      ρ.asModuleEquiv.toLinearMap ρ.asModuleEquiv.injective).finrank_eq
  rw [h1, hmap]

private lemma finrank_ker_le_restrictScalars {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (hirr : ρ.IsIrreducible) (g : Γ) :
    Module.finrank (Module.End (MonoidAlgebra (ZMod p) Γ) ρ.asModule)
        (LinearMap.ker ((CFSG.endFieldRep ρ) g - 1)) ≤
      Module.finrank (ZMod p)
        ((LinearMap.ker ((CFSG.endFieldRep ρ) g - 1)).restrictScalars (ZMod p)) := by
  classical
  letI : Representation.IsIrreducible ρ := hirr
  let 𝔽 := Module.End (MonoidAlgebra (ZMod p) Γ) ρ.asModule
  letI : Field 𝔽 := CFSG.endField_field ρ
  letI : Module 𝔽 ρ.asModule := CFSG.endFieldModule ρ
  letI : Algebra (ZMod p) 𝔽 :=
    Module.End.instAlgebra (ZMod p) (MonoidAlgebra (ZMod p) Γ) ρ.asModule
  letI : Module (ZMod p) 𝔽 := Algebra.toModule
  let W : Submodule 𝔽 ρ.asModule := LinearMap.ker ((CFSG.endFieldRep ρ) g - 1)
  letI : Module 𝔽 ↥W := Submodule.module W
  letI : Module (ZMod p) ↥W := Submodule.module (W.restrictScalars (ZMod p))
  letI : IsScalarTower (ZMod p) 𝔽 ↥W :=
    ⟨fun a b w => Subtype.ext (smul_assoc a b (w : ρ.asModule))⟩
  have hpos : 0 < Module.finrank (ZMod p) 𝔽 := Module.finrank_pos
  change Module.finrank 𝔽 W ≤ Module.finrank (ZMod p) W
  have hmul := @Module.finrank_mul_finrank (ZMod p) 𝔽 ↥W
    (inferInstance : Semiring (ZMod p)) (inferInstance : Semiring 𝔽)
    (inferInstance : AddCommMonoid ↥W)
    (inferInstance : Module (ZMod p) 𝔽) (inferInstance : Module 𝔽 ↥W)
    (inferInstance : Module (ZMod p) ↥W)
    (inferInstance : IsScalarTower (ZMod p) 𝔽 ↥W)
    (inferInstance : StrongRankCondition (ZMod p)) (inferInstance : StrongRankCondition 𝔽)
    (inferInstance : Module.Free (ZMod p) 𝔽) (inferInstance : Module.Free 𝔽 ↥W)
  rw [← hmul]
  exact Nat.le_mul_of_pos_left _ hpos

private lemma finrank_ker_endFieldRep_le {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (hirr : ρ.IsIrreducible) (g : Γ) :
    Module.finrank (Module.End (MonoidAlgebra (ZMod p) Γ) ρ.asModule)
        (LinearMap.ker ((CFSG.endFieldRep ρ) g - 1)) ≤
      Module.finrank (ZMod p) (LinearMap.ker (ρ g - 1)) :=
  (finrank_ker_le_restrictScalars ρ hirr g).trans_eq (finrank_ker_endFieldRep_eq ρ hirr g)

private lemma fixed_descent_of_conjugate {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (𝔽 : Type) [Field 𝔽] [Module 𝔽 ρ.asModule]
    (τ : Representation 𝔽 Γ ρ.asModule)
    (hτ : ∀ (g : Γ) (m : ρ.asModule), ρ.asModuleEquiv (τ g m) = ρ g (ρ.asModuleEquiv m))
    (𝕜 : Type) [Field 𝕜] [Algebra 𝔽 𝕜]
    (σ : Representation 𝕜 Γ (𝕜 ⊗[𝔽] ρ.asModule))
    (hσ : ∀ g : Γ, σ g = (τ g).baseChange 𝕜)
    (H : Subgroup Γ) (g : Γ)
    (hH : ∀ v : 𝕜 ⊗[𝔽] ρ.asModule, (∀ h ∈ H, σ h v = v) → σ g v = v) :
    ∀ f : F, (∀ h ∈ H, ρ h f = f) → ρ g f = f := by
  intro f hf
  let m : ρ.asModule := ρ.asModuleEquiv.symm f
  have hmf : ρ.asModuleEquiv m = f := ρ.asModuleEquiv.apply_symm_apply f
  have hm : ∀ h ∈ H, τ h m = m := by
    intro h hh
    apply ρ.asModuleEquiv.injective
    rw [hτ, hmf]
    exact hf h hh
  let v : 𝕜 ⊗[𝔽] ρ.asModule := (1 : 𝕜) ⊗ₜ[𝔽] m
  have hv : ∀ h ∈ H, σ h v = v := by
    intro h hh
    have h1 : σ h v = (1 : 𝕜) ⊗ₜ[𝔽] τ h m := by
      rw [hσ h, LinearMap.baseChange_tmul]
    rw [h1, hm h hh]
  have hgm : τ g m = m := by
    have hinj : Function.Injective (fun m : ρ.asModule => (1 : 𝕜) ⊗ₜ[𝔽] m) :=
      Module.FaithfullyFlat.tensorProduct_mk_injective (A := 𝔽) (B := 𝕜) (M := ρ.asModule)
    apply hinj
    have h1 : σ g v = (1 : 𝕜) ⊗ₜ[𝔽] τ g m := by
      rw [hσ g, LinearMap.baseChange_tmul]
    have h2 : σ g v = v := hH v hv
    rw [h1] at h2
    simpa [v, hτ g m] using h2
  rw [← hmf, ← hτ g m, hgm]

theorem exists_isAlgClosed_extension {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    {F : Type} [AddCommGroup F] [Module (ZMod p) F] [Module.Finite (ZMod p) F]
    (ρ : Representation (ZMod p) Γ F) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ) :
    ∃ (𝕜 : Type) (_ : Field 𝕜) (_ : IsAlgClosed 𝕜) (_ : CharP 𝕜 p)
      (V : Type) (_ : AddCommGroup V) (_ : Module 𝕜 V) (_ : FiniteDimensional 𝕜 V)
      (σ : Representation 𝕜 Γ V),
      σ.IsIrreducible ∧ Function.Injective σ ∧
      (∀ g : Γ, Module.finrank 𝕜 (LinearMap.ker (σ g - 1)) ≤
        Module.finrank (ZMod p) (LinearMap.ker (ρ g - 1))) ∧
      ∀ (H : Subgroup Γ) (g : Γ), (∀ v : V, (∀ h ∈ H, σ h v = v) → σ g v = v) →
        ∀ f : F, (∀ h ∈ H, ρ h f = f) → ρ g f = f := by
  classical
  letI : Representation.IsIrreducible ρ := hirr
  let 𝔽 := Module.End (MonoidAlgebra (ZMod p) Γ) ρ.asModule
  letI : Field 𝔽 := CFSG.endField_field ρ
  letI : Finite 𝔽 := CFSG.endField_finite ρ
  letI : Module 𝔽 ρ.asModule := CFSG.endFieldModule ρ
  letI : Algebra (ZMod p) 𝔽 :=
    Module.End.instAlgebra (ZMod p) (MonoidAlgebra (ZMod p) Γ) ρ.asModule
  letI : Module.Finite (ZMod p) ρ.asModule := Representation.instFiniteAsModule ρ
  letI : FiniteDimensional 𝔽 ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod p) 𝔽 ρ.asModule
  have hchar𝔽 : CharP 𝔽 p := by
    have hring : ringChar 𝔽 = ringChar (ZMod p) :=
      (@Algebra.ringChar_eq (ZMod p) 𝔽 inferInstance inferInstance inferInstance
        inferInstance).symm
    exact ringChar.of_eq (by simpa [ZMod.ringChar_zmod_n] using hring)
  let 𝕜 := AlgebraicClosure 𝔽
  letI : Field 𝕜 := inferInstance
  letI : IsAlgClosed 𝕜 := inferInstance
  letI : CharP 𝕜 p := AlgebraicClosure.instCharP 𝔽
  let V := 𝕜 ⊗[𝔽] ρ.asModule
  let σ : Representation 𝕜 Γ V := CFSG.Theory.Representation.extendScalars 𝕜 (CFSG.endFieldRep ρ)
  letI : FiniteDimensional 𝕜 V :=
    CFSG.Theory.Representation.extendScalars_finite_dimensional (F' := 𝕜) (ρ := CFSG.endFieldRep ρ)
  have hσirr : σ.IsIrreducible :=
    CFSG.Theory.Representation.IsAbsolutelyIrreducible.irreducible_of_closure
      (ρ := CFSG.endFieldRep ρ) (self := CFSG.endFieldRep_isAbsolutelyIrreducible ρ)
  have hσinj : Function.Injective σ :=
    (CFSG.Theory.Representation.extendScalars_faithful_iff 𝕜 (CFSG.endFieldRep ρ)).mp
      (endFieldRep_injective ρ hfaith)
  have hfix : ∀ g : Γ, Module.finrank 𝕜 (LinearMap.ker (σ g - 1)) ≤
      Module.finrank (ZMod p) (LinearMap.ker (ρ g - 1)) := by
    intro g
    let T : ρ.asModule →ₗ[𝔽] ρ.asModule := (CFSG.endFieldRep ρ) g - 1
    have hσ : σ g - 1 = T.baseChange 𝕜 := by
      rw [show σ g = ((CFSG.endFieldRep ρ) g).baseChange 𝕜 from
        CFSG.Theory.Representation.extendScalars_apply 𝕜 (CFSG.endFieldRep ρ) g,
        ← LinearMap.baseChange_one, ← LinearMap.baseChange_sub]
    have hA : Module.finrank 𝕜 (LinearMap.ker (σ g - 1)) =
        Module.finrank 𝔽 (LinearMap.ker T) := by
      rw [hσ, ← (LinearMap.kerBaseChangeEquiv T).finrank_eq, Module.finrank_baseChange]
    rw [hA]
    exact finrank_ker_endFieldRep_le ρ hirr g
  have hdesc : ∀ (H : Subgroup Γ) (g : Γ),
      (∀ v : V, (∀ h ∈ H, σ h v = v) → σ g v = v) →
      ∀ f : F, (∀ h ∈ H, ρ h f = f) → ρ g f = f := by
    intro H g hH f hf
    exact fixed_descent_of_conjugate ρ 𝔽 (CFSG.endFieldRep ρ)
      (fun g m => CFSG.endFieldRep_apply' ρ g m) 𝕜 σ
      (fun g => CFSG.Theory.Representation.extendScalars_apply 𝕜 (CFSG.endFieldRep ρ) g)
      H g hH f hf
  exact ⟨𝕜, inferInstance, inferInstance, inferInstance, V, inferInstance, inferInstance,
    inferInstance, σ, hσirr, hσinj, hfix, hdesc⟩

end CFSG.RankThree.PartTwo.Sec16.Kcd166
