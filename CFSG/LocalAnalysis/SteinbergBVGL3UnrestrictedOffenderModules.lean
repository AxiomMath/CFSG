module

public import CFSG.LocalAnalysis.SteinbergBVGL3SmallOffenderModules

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

universe u

theorem GL3_offender_unrestricted_explicit_module_production {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : finrank (ZMod 2) V = 3) {E : Type u} [AddCommGroup E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] [Nontrivial E]
    (ρ : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) E)
    (hE : Submodule.span (ZMod 2) {w | ∃ (s : V ≃ₗ[ZMod 2] V) (v : E), w = ρ s v - v} = ⊤)
    (B : Subgroup (V ≃ₗ[ZMod 2] V)) (hBe : CFSG.Open.IsElemAbelian 2 B) (hB : B ≠ ⊥) (r : ℕ)
    (hr : Nat.card B = 2 ^ r)
    (hoff : finrank (ZMod 2) E -
      finrank (ZMod 2) (Representation.invariants (ρ.comp B.subtype)) ≤ r) :
    finrank (ZMod 2) E ≤ 6 ∧
    ((∃ φ : E →ₗ[ZMod 2] V, (∀ g e, φ (ρ g e) = natRep V g (φ e)) ∧ Function.Surjective φ ∧
        LinearMap.ker φ = Representation.invariants ρ) ∨
      (Nonempty (ρ.Equiv ((natRep V).prod (natRep V))) ∧ finrank (ZMod 2) E = 6) ∨
      (∃ φ : E →ₗ[ZMod 2] Module.Dual (ZMod 2) V, (∀ g e, φ (ρ g e) = dualRep V g (φ e)) ∧
        Function.Surjective φ ∧ LinearMap.ker φ = Representation.invariants ρ) ∨
      (Nonempty (ρ.Equiv ((dualRep V).prod (dualRep V))) ∧ finrank (ZMod 2) E = 6)) ∧
    (∃ e : (V ≃ₗ[ZMod 2] V) ≃* (V ≃ₗ[ZMod 2] V), ∀ g v, e g v = natRep V g v) ∧
    ∃ e : (V ≃ₗ[ZMod 2] V) ≃* (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V),
      ∀ g f, e g f = dualRep V g f := by
  have hr2 : r ≤ 2 := by
    rcases (GL3_elementary_abelian_fixed_codimensions hV B hBe hB r hr).1 with h | h <;> omega
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
  have ha2 : (a : V ≃ₗ[ZMod 2] V) * a = 1 := by
    rw [← pow_two]
    exact hBe.2 a a.2
  have hle : Representation.invariants (ρ.comp B.subtype) ≤
      LinearMap.ker (ρ a - LinearMap.id) := by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact hv a
  have hrank : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (ρ (a : V ≃ₗ[ZMod 2] V) - LinearMap.id)
    have h2 := Submodule.finrank_mono hle
    omega
  have hdim : finrank (ZMod 2) E ≤ 6 := by
    have := GL3_three_involution_commutator_dimension_bound hV ρ hE a ha2
      fun h => ha1 (Subtype.ext h)
    omega
  exact ⟨hdim, small_GL3_offender_explicit_module_production hV ρ hdim hE B hBe hB r hr hoff⟩

end CFSG.LocalAnalysis.SteinbergBV
