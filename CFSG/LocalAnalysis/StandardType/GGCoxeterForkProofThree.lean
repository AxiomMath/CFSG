module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem zmod_three_cases' : ∀ z : ZMod 3, z = 0 ∨ z = 1 ∨ z = 2 := by
  decide

private theorem zmod_three_two_ne_zero' : (2 : ZMod 3) ≠ 0 := by decide

private theorem zmod_three_two_ne_one' : (2 : ZMod 3) ≠ 1 := by decide

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {V : Type*}
  [AddCommGroup V] [Module (ZMod p) V]
variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V}
  {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}

theorem ggFork_not_two_two (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) (ι : Additive ↥Bs ≃+ V)
    (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs}
    (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤)
    (hu : αa (h b) = 2) (hv : α b ha = 2) : False := by
  have hab : ha ≠ h b := fun e => by
    have := hind.injective (a₁ := none) (a₂ := some b) (by simpa using e)
    cases this
  have heq : αa = α b := by
    refine LinearMap.ext_on_range hspan fun o => ?_
    cases o with
    | none => simp [hF.aa, hv]
    | some i =>
      by_cases hi : i = b
      · subst hi
        simp [hu, hF.self]
      · simpa [sub_eq_zero] using hF.aL_sub_bL hi
  refine hNT (φa * φ b) (mul_mem_ggInduced hφa (hφ b)) ?_
  refine ggIsTransvection_of_apply ι (w := ha - h b) (f := α b) (sub_ne_zero.mpr hab)
    (ne_zero_of_apply_eq_two hp2 (hF.self b)).2 ?_ ?_
  · rw [map_sub, hv, hF.self b, sub_self]
  · intro v
    rw [map_mul, LinearEquiv.mul_apply, hlina, hlin b, heq, map_sub, map_smul, hF.self b,
      smul_eq_mul]
    module

theorem ggFork_cross_mem_of_p_three (hp3 : p = 3) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤) :
    αa (h b) = 0 ∨ αa (h b) = 1 := by
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  obtain ⟨h0, h1⟩ := ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina
  rcases zmod_three_cases' (αa (h b)) with hu | hu | hu
  · exact Or.inl hu
  · exact Or.inr hu
  · exfalso
    have hv : α b ha = 2 := by
      rcases zmod_three_cases' (α b ha) with hv | hv | hv
      · exact absurd (h0.mpr hv) (hu ▸ zmod_three_two_ne_zero')
      · exact absurd (h1.mpr hv) (hu ▸ zmod_three_two_ne_one')
      · exact hv
    exact ggFork_not_two_two hp2 hNT ι hF hφ hφa hlin hlina hind hspan hu hv

end CFSG.StandardType
