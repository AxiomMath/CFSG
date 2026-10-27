module

public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartOne

theorem exists_invariant_compl_of_not_dvd {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (Γ : Subgroup (V ≃ₗ[ZMod p] V))
    (hΓ : ¬ p ∣ Nat.card Γ) (B : Submodule (ZMod p) V) (hB : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) :
    ∃ C : Submodule (ZMod p) V, IsCompl B C ∧ ∀ g ∈ Γ, ∀ x ∈ C, g x ∈ C := by
  have hV : Finite V := Module.finite_of_finite (ZMod p)
  have hfin : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod p] V => (g : V → V)) DFunLike.coe_injective
  have hΓfin : Finite Γ := inferInstance
  let ρ : Representation (ZMod p) Γ V :=
    { toFun := fun g => ((g : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hne : NeZero (Nat.card Γ : ZMod p) := ⟨by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hΓ⟩
  let B' : Subrepresentation ρ := ⟨B, fun g v hv => hB g g.2 v hv⟩
  obtain ⟨C', hC'⟩ := ComplementedLattice.exists_isCompl B'
  refine ⟨C'.toSubmodule, ?_, fun g hg x hx => C'.apply_mem_toSubmodule ⟨g, hg⟩ hx⟩
  have h1 : B' ⊓ C' = ⊥ := disjoint_iff.mp hC'.1
  have h2 : B' ⊔ C' = ⊤ := codisjoint_iff.mp hC'.2
  have h1' := congrArg Subrepresentation.toSubmodule h1
  have h2' := congrArg Subrepresentation.toSubmodule h2
  exact ⟨disjoint_iff.mpr h1', codisjoint_iff.mpr h2'⟩

end CFSG.RankThree.PartOne
