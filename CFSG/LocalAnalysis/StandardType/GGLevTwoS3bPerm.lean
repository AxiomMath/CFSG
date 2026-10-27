module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bBridge

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3b_reflectStep {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    (hR : TauCeti.IsFiniteType R) (roots : List (ι → ℤ)) (g : ι → ℤ) (p : List ℕ) : Prop :=
  ∀ i, i < roots.length → roots.getD (p.getD i 0) 0 = weylAction hR (rRefl hR g) (roots.getD i 0)

@[expose] def levTwoS3b_negStep {ι : Type} (roots : List (ι → ℤ)) (p : List ℕ) : Prop :=
  ∀ i, i < roots.length → roots.getD (p.getD i 0) 0 = -(roots.getD i 0)

theorem levTwoS3b_Cl_zero_elim {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {S : Set (ι → ℤ)} (hS : ∀ β ∈ S, IsRt hR β)
    (hi : Cl hR S (0 : ι → ℤ)) : False :=
  levTwoS3b_isRt_ne_zero (Cl_isRt hR hS hi) rfl

theorem levTwoS3b_permValid_of_reflect {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Matrix ι ι ℤ} {hR : TauCeti.IsFiniteType R} {roots : List (ι → ℤ)}
    {S : Set (ι → ℤ)} {g : ι → ℤ} {p : List ℕ} (hS : ∀ β ∈ S, IsRt hR β) (hg : Cl hR S g)
    (hp : levTwoS3b_reflectStep hR roots g p) :
    ∀ i, Cl hR S (roots.getD i 0) → Cl hR S (roots.getD (p.getD i 0) 0) := by
  intro i hi
  by_cases h : i < roots.length
  · rw [hp i h]
    exact Cl.refl hg hi
  · have h0 : roots.getD i 0 = (0 : ι → ℤ) := List.getD_eq_default _ _ (by omega)
    exact absurd (h0 ▸ hi) (levTwoS3b_Cl_zero_elim hS)

theorem levTwoS3b_permValid_of_neg {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (ι → ℤ)} {S : Set (ι → ℤ)} {p : List ℕ}
    (hS : ∀ β ∈ S, IsRt hR β) (hp : levTwoS3b_negStep roots p) :
    ∀ i, Cl hR S (roots.getD i 0) → Cl hR S (roots.getD (p.getD i 0) 0) := by
  intro i hi
  by_cases h : i < roots.length
  · rw [hp i h]
    have hg : IsRt hR (roots.getD i 0) := Cl_isRt hR hS hi
    rw [← levTwoS3b_weylAction_rRefl_self hg]
    exact Cl.refl hi hi
  · have h0 : roots.getD i 0 = (0 : ι → ℤ) := List.getD_eq_default _ _ (by omega)
    exact absurd (h0 ▸ hi) (levTwoS3b_Cl_zero_elim hS)

theorem levTwoS3b_hperm_of_valid {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (ι → ℤ)} {S : Set (ι → ℤ)} {perms : List (List ℕ)}
    (hS : ∀ β ∈ S, IsRt hR β)
    (hvalid : ∀ p ∈ perms,
      (∃ g, Cl hR S g ∧ levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p) :
    ∀ p ∈ perms, ∀ i, Cl hR S (roots.getD i 0) → Cl hR S (roots.getD (p.getD i 0) 0) := by
  intro p hp i hi
  rcases hvalid p hp with ⟨g, hg, hstep⟩ | hneg
  · exact levTwoS3b_permValid_of_reflect hS hg hstep i hi
  · exact levTwoS3b_permValid_of_neg hS hneg i hi

end CFSG.StandardType.LevTwo
