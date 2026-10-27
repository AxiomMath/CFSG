module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearEndField
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.SL4ModEmbed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod

theorem equiv_act_wordProd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2))
    (M : ℕ → Matrix (Fin d) (Fin d) (ZMod 2))
    (hM : ∀ s < 6, ∀ v, e (ρ (genN s) v) = M s *ᵥ e v) :
    ∀ w : List ℕ, (∀ s ∈ w, s < 6) → ∀ v, e (ρ (wordProd w) v) = (w.map M).prod *ᵥ e v := by
  intro w
  induction w with
  | nil =>
    intro _ v
    simp [wordProd]
  | cons s w ih =>
    intro hw v
    have hs : s < 6 := hw s (List.mem_cons_self ..)
    rw [wordProd_cons, act_mul, hM s hs, ih (fun t ht => hw t (List.mem_cons_of_mem _ ht)),
      Matrix.mulVec_mulVec, List.map_cons, List.prod_cons]

theorem finrank_range_sub_one_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (f : V ≃ₗ[ZMod 2] V)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (h : ∀ v, e (f v) = A *ᵥ e v) :
    finrank (ZMod 2) (LinearMap.range ((f : V →ₗ[ZMod 2] V) - 1)) =
      finrank (ZMod 2) (LinearMap.range (A - 1).mulVecLin) := by
  have hcomp : (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) ∘ₗ ((f : V →ₗ[ZMod 2] V) - 1) =
      (A - 1).mulVecLin ∘ₗ (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) := by
    apply LinearMap.ext
    intro v
    simp [h, Matrix.sub_mulVec]
  calc finrank (ZMod 2) (LinearMap.range ((f : V →ₗ[ZMod 2] V) - 1))
      = finrank (ZMod 2) (Submodule.map (e : V →ₗ[ZMod 2] (Fin d → ZMod 2))
          (LinearMap.range ((f : V →ₗ[ZMod 2] V) - 1))) :=
        (LinearEquiv.finrank_map_eq e _).symm
    _ = finrank (ZMod 2) (LinearMap.range ((e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) ∘ₗ
          ((f : V →ₗ[ZMod 2] V) - 1))) := by rw [LinearMap.range_comp]
    _ = finrank (ZMod 2) (LinearMap.range ((A - 1).mulVecLin ∘ₗ
          (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)))) := by rw [hcomp]
    _ = finrank (ZMod 2) (LinearMap.range (A - 1).mulVecLin) := by
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e)]

theorem finrank_range_eq_of_intertwine {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2)) (f : V →ₗ[ZMod 2] V)
    (A : Matrix (Fin d) (Fin d) (ZMod 2)) (h : ∀ v, e (f v) = A *ᵥ e v) :
    finrank (ZMod 2) (LinearMap.range f) = finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
  have hcomp : (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) ∘ₗ f =
      A.mulVecLin ∘ₗ (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) := by
    apply LinearMap.ext
    intro v
    simp [h]
  calc finrank (ZMod 2) (LinearMap.range f)
      = finrank (ZMod 2) (Submodule.map (e : V →ₗ[ZMod 2] (Fin d → ZMod 2))
          (LinearMap.range f)) := (LinearEquiv.finrank_map_eq e _).symm
    _ = finrank (ZMod 2) (LinearMap.range ((e : V →ₗ[ZMod 2] (Fin d → ZMod 2)) ∘ₗ f)) := by
        rw [LinearMap.range_comp]
    _ = finrank (ZMod 2) (LinearMap.range (A.mulVecLin ∘ₗ
          (e : V →ₗ[ZMod 2] (Fin d → ZMod 2)))) := by rw [hcomp]
    _ = finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
        rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e)]

theorem intertwine_of_gen {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) (γ : MulAut SL4) (S : V ≃ₗ[ZMod 2] V)
    (h : ∀ s < 6, ∀ v, S (ρ (genN s) v) = ρ (γ (genN s)) (S v)) :
    ∀ (y : SL4) (v : V), S (ρ y v) = ρ (γ y) (S v) := by
  intro y
  have hy : y ∈ genClosure := closure_gen ▸ Subgroup.mem_top y
  induction hy using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact h s s.isLt
  | inv_mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [genN_inv]
    exact h s s.isLt
  | one =>
    intro v
    simp
  | mul x y _ _ hx hy =>
    intro v
    rw [act_mul, hx, hy, map_mul, act_mul]


theorem commutant_eq_zero_or_one {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Nontrivial V] {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) (Φ : V →ₗ[ZMod 2] V)
    (hΦ : ∀ s : Fin 6, ∀ v, Φ (ρ (genN s.val) v) = ρ (genN s.val) (Φ v)) : Φ = 0 ∨ Φ = 1 := by
  classical
  have hall : ∀ (g : SL4) (v : V), Φ (ρ g v) = ρ g (Φ v) := by
    intro g
    have hg : g ∈ genClosure := closure_gen ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact hΦ s
    | inv_mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      rw [genN_inv]
      exact hΦ s
    | one =>
      intro v
      simp
    | mul x y _ _ hx hy =>
      intro v
      rw [act_mul, hx, hy, act_mul]
  let ρ' : Representation (ZMod 2) SL4 V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp ρ
  have hρ' : ∀ g v, ρ' g v = ρ g v := fun g v => rfl
  have hirr' : ρ'.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
    exact ⟨inferInstance, fun U hU => hirr U fun s _ w hw => hU _ w hw⟩
  have hcard := card_endField_eq_two_of_card_eq_two (K := ZMod 2) (ZMod.card 2) (n := 4)
    (by norm_num) ρ' hirr'
  have hcomm : ∀ (r : MonoidAlgebra (ZMod 2) SL4) (y : V),
      Φ (ρ'.asAlgebraHom r y) = ρ'.asAlgebraHom r (Φ y) := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      intro y
      rw [Representation.asAlgebraHom_of]
      exact hall g y
    | add r₁ r₂ h₁ h₂ =>
      intro y
      rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, h₁, h₂]
    | smul c r h =>
      intro y
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]
  let c : Module.End (MonoidAlgebra (ZMod 2) SL4) ρ'.asModule :=
    { toFun := fun x => ρ'.asModuleEquiv.symm (Φ (ρ'.asModuleEquiv x))
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        apply ρ'.asModuleEquiv.injective
        simp only [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
          RingHom.id_apply]
        exact hcomm r _ }
  have htwo : ∀ c : Module.End (MonoidAlgebra (ZMod 2) SL4) ρ'.asModule, c = 0 ∨ c = 1 := by
    obtain ⟨y₀, hy₀, hyuniq⟩ := (Nat.card_eq_two_iff' (0 : Module.End (MonoidAlgebra (ZMod 2) SL4)
      ρ'.asModule)).1 hcard
    haveI : Nontrivial (Module.End (MonoidAlgebra (ZMod 2) SL4) ρ'.asModule) :=
      ⟨⟨y₀, 0, hy₀⟩⟩
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1y : (1 : Module.End (MonoidAlgebra (ZMod 2) SL4) ρ'.asModule) = y₀ :=
        hyuniq 1 one_ne_zero
      exact (hyuniq c hc).trans h1y.symm
  rcases htwo c with h0 | h1
  · left
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h0 (ρ'.asModuleEquiv.symm v)
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      LinearMap.zero_apply] at this
    have h2 := congrArg ρ'.asModuleEquiv this
    simpa using h2
  · right
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h1 (ρ'.asModuleEquiv.symm v)
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      Module.End.one_apply] at this
    have h2 := congrArg ρ'.asModuleEquiv this
    simpa using h2

end CFSG.LocalAnalysis.WeakClosure81
