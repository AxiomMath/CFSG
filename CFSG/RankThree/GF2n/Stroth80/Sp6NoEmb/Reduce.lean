module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bRepInd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open Representation
open CFSG.QuasithinUnique.Setup.X7b (exists_isCoatom_subrep quotient_isIrreducible_of_isCoatom)

variable {K : Type} [Field K] {G : Type} [Group G]

theorem exists_irreducible_target {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [Nontrivial N]
    {ρN : Representation (ZMod 2) G N} (hNirr : ρN.IsIrreducible)
    {V : Type} [AddCommGroup V] [Module K V] (ρV : Representation K G V)
    {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X] (ρX : Representation K G X)
    (f : N →+ (V →ₗ[K] X)) (hf : ∀ g a, f (ρN g a) = linHom ρV ρX g (f a))
    (hinj : Function.Injective f) :
    ∃ (Z : Type) (_ : AddCommGroup Z) (_ : Module K Z) (_ : FiniteDimensional K Z)
      (ρZ : Representation K G Z), ρZ.IsIrreducible ∧ finrank K Z ≤ finrank K X ∧
      ∃ f' : N →+ (V →ₗ[K] Z), (∀ g a, f' (ρN g a) = linHom ρV ρZ g (f' a)) ∧
        Function.Injective f' := by
  classical
  set S : Set X := {x | ∃ a v, f a v = x} with hSdef
  have hfv : ∀ g a v, ρX g (f a v) = f (ρN g a) (ρV g v) := by
    intro g a v
    rw [hf, linHom_apply, LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  let W₀ : Subrepresentation ρX :=
    ⟨Submodule.span K S, fun g x hx => by
      have hle : Submodule.span K S ≤ (Submodule.span K S).comap (ρX g) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, v, rfl⟩
        exact Submodule.subset_span ⟨ρN g a, ρV g v, (hfv g a v).symm⟩
      exact hle hx⟩
  have hmem : ∀ a v, f a v ∈ W₀.toSubmodule := fun a v => Submodule.subset_span ⟨a, v, rfl⟩
  haveI : Nontrivial W₀.toSubmodule := by
    obtain ⟨a, ha⟩ := exists_ne (0 : N)
    have hfa : f a ≠ 0 := fun h => ha (hinj (h.trans (map_zero f).symm))
    obtain ⟨v, hv⟩ : ∃ v, f a v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hfa (LinearMap.ext hcon)
    exact ⟨⟨⟨f a v, hmem a v⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨W₁, hW₁⟩ := exists_isCoatom_subrep W₀.toRepresentation
  have hZirr := quotient_isIrreducible_of_isCoatom _ W₁ hW₁
  let φ : N → V →ₗ[K] (W₀.toSubmodule ⧸ W₁.toSubmodule) := fun a =>
    W₁.toSubmodule.mkQ ∘ₗ (f a).codRestrict W₀.toSubmodule (hmem a)
  let f' : N →+ (V →ₗ[K] (W₀.toSubmodule ⧸ W₁.toSubmodule)) :=
    { toFun := φ
      map_zero' := by
        refine LinearMap.ext fun v => ?_
        change Submodule.Quotient.mk (p := W₁.toSubmodule) ⟨f 0 v, hmem _ _⟩ = 0
        rw [Submodule.Quotient.mk_eq_zero]
        have : (⟨f 0 v, hmem 0 v⟩ : W₀.toSubmodule) = 0 := Subtype.ext (by simp)
        rw [this]
        exact W₁.toSubmodule.zero_mem
      map_add' := fun a b => by
        refine LinearMap.ext fun v => ?_
        change Submodule.Quotient.mk (p := W₁.toSubmodule) ⟨f (a + b) v, hmem _ _⟩ =
          Submodule.Quotient.mk (p := W₁.toSubmodule) ⟨f a v, hmem _ _⟩ +
            Submodule.Quotient.mk (p := W₁.toSubmodule) ⟨f b v, hmem _ _⟩
        rw [← Submodule.Quotient.mk_add]
        congr 1
        exact Subtype.ext (by simp) }
  have hf'eq : ∀ g a, f' (ρN g a) = linHom ρV W₁.quotient g (f' a) := by
    intro g a
    refine LinearMap.ext fun v => ?_
    change Submodule.Quotient.mk (p := W₁.toSubmodule) ⟨f (ρN g a) v, hmem _ _⟩ =
      Submodule.Quotient.mk (p := W₁.toSubmodule) (W₀.toRepresentation g ⟨f a (ρV g⁻¹ v), hmem _ _⟩)
    congr 1
    apply Subtype.ext
    change f (ρN g a) v = ρX g (f a (ρV g⁻¹ v))
    rw [hfv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨_, _, _, inferInstance, W₁.quotient, hZirr, ?_, f', hf'eq, ?_⟩
  · calc finrank K (W₀.toSubmodule ⧸ W₁.toSubmodule) ≤ finrank K W₀.toSubmodule :=
          Submodule.finrank_quotient_le _
      _ ≤ finrank K X := Submodule.finrank_le _
  ·
    rw [← AddMonoidHom.ker_eq_bot_iff f']
    let T : Submodule (ZMod 2) N := AddSubgroup.toZModSubmodule 2 f'.ker
    have hT : ∀ g, ∀ a ∈ T, ρN g a ∈ T := by
      intro g a ha
      change f' (ρN g a) = 0
      change f' a = 0 at ha
      rw [hf'eq, ha, map_zero]
    rcases ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρN).mp hNirr).2 T hT with h | h
    · exact (AddSubgroup.toZModSubmodule 2).injective (h.trans (map_bot _).symm)
    · exfalso
      apply hW₁.1
      apply Subrepresentation.toSubmodule_injective
      change W₁.toSubmodule = ⊤
      have hall : ∀ a v, (⟨f a v, hmem a v⟩ : W₀.toSubmodule) ∈ W₁.toSubmodule := by
        intro a v
        have ha : f' a = 0 := by
          have : a ∈ T := h ▸ Submodule.mem_top
          exact this
        have := LinearMap.congr_fun ha v
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      have hspan : Submodule.span K S ≤ W₁.toSubmodule.map W₀.toSubmodule.subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨a, v, rfl⟩
        exact ⟨⟨f a v, hmem a v⟩, hall a v, rfl⟩
      rw [eq_top_iff]
      intro w _
      obtain ⟨w', hw', hww'⟩ := hspan w.2
      have : w' = w := Subtype.ext hww'
      rw [← this]
      exact hw'

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
