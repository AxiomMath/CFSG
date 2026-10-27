module

public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResXDatumSurj {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
    GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      ∃ f : M.Group →* ↥(ggAutomizer X Bs), Function.Surjective f ∧
        ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i

theorem ggAutomizer_eq_closure_of_surj {G : Type} [Group G] {Bs X : Subgroup G} {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {φ : Λ → MulAut ↥Bs}
    (f : M.Group →* ↥(ggAutomizer X Bs)) (hs : Function.Surjective f)
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) :
    ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  have hF : ((ggAutomizer X Bs).subtype.comp f).range = ggAutomizer X Bs := by
    ext g
    constructor
    · rintro ⟨w, rfl⟩
      exact (f w).2
    · intro hg
      obtain ⟨w, hw⟩ := hs ⟨g, hg⟩
      exact ⟨w, by simpa using congrArg Subtype.val hw⟩
  have hcomp : ⇑((ggAutomizer X Bs).subtype.comp f) ∘ M.toCoxeterSystem.simple = φ :=
    funext fun i => by
      rw [Function.comp_apply, CoxeterMatrix.toCoxeterSystem_simple]
      exact hf i
  rw [← hF, MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp, hcomp]

theorem GGResXDatum.toSurj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (h : GGResXDatum p Bs X) : GGResXDatumSurj p Bs X := by
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, hh, α, hM, hC, hlin, hrefl, hpair, ⟨f, hf⟩, -⟩ := h
  exact ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, hh, α, hM, hC, hlin, hrefl, hpair, f.toMonoidHom,
    f.surjective, hf⟩

end CFSG.StandardType

end
