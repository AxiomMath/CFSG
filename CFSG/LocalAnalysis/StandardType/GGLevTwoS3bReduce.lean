module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

section Generic

theorem levTwoS3b_Cl_mono {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {S T : Set (ι → ℤ)} (h : S ⊆ T) {β : ι → ℤ}
    (hβ : Cl hR S β) : Cl hR T β := by
  induction hβ with
  | base hb => exact Cl.base (h hb)
  | refl _ _ iha ihb => exact Cl.refl iha ihb

theorem levTwoS3b_Cl_least {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {S C : Set (ι → ℤ)} (hS : S ⊆ C)
    (hC : ∀ α, C α → ∀ β, C β → C (weylAction hR (rRefl hR α) β)) {β : ι → ℤ}
    (hβ : Cl hR S β) : C β := by
  induction hβ with
  | base hb => exact hS hb
  | refl _ _ iha ihb => exact hC _ iha _ ihb

theorem levTwoS3b_Cl_insert_subset {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {Φ C : Set (ι → ℤ)} {r : ι → ℤ} (hΦC : Φ ⊆ C) (hrC : C r)
    (hC : ∀ α, C α → ∀ β, C β → C (weylAction hR (rRefl hR α) β)) {β : ι → ℤ}
    (hβ : Cl hR (Φ ∪ {r}) β) : C β :=
  levTwoS3b_Cl_least (fun x hx => by
    rcases hx with hx | hx
    · exact hΦC hx
    · rw [Set.mem_singleton_iff] at hx
      rw [← hx] at hrC
      exact hrC) hC hβ

theorem levTwoS3b_Cl_union_subset {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {Φ X C : Set (ι → ℤ)} (hΦC : Φ ⊆ C) (hXC : X ⊆ C)
    (hC : ∀ α, C α → ∀ β, C β → C (weylAction hR (rRefl hR α) β)) {β : ι → ℤ}
    (hβ : Cl hR (Φ ∪ X) β) : C β :=
  levTwoS3b_Cl_least (fun x hx => by
    rcases hx with hx | hx
    · exact hΦC hx
    · exact hXC hx) hC hβ

end Generic

end CFSG.StandardType.LevTwo
