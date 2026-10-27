module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Master2Aux
public import CFSG.LocalAnalysis.WeakClosure81.W183K3OneSided
public import CFSG.LocalAnalysis.WeakClosure81.W183K3TwoSided

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

theorem w183k3m2_false_of_rank_three (rows : Br3Rows)
    (hc : Br2Common Y Γ VA T 𝒢 Zs m i₀ δ) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨ IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2)
    (hZ : Nat.card ↥(Subgroup.center ↥L₁) = 3)
    (hall : ∀ D ∈ Γ, 2 ≤ mRank D) (hne : Γ.Nonempty) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D)
    {ED : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} (hED : Br2ED Γ VA m δ ED) : False := by
  by_cases hone : ∀ D ∈ Γ, D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
      D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))
  · exact br3_false_of_one_sided rows hc htwo
      (fun D hD => (w183k3m2_mem_normalizer hc htwo hall hD).1)
      hone hrk hne hshape.symm
  · obtain ⟨D, hDnot⟩ := not_forall.1 hone
    have hD : D ∈ Γ := by
      by_contra h
      exact hDnot (fun hmem => absurd hmem h)
    have hDnot' : ¬ (D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∨
        D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := fun hp => hDnot (fun _ => hp)
    have hDnot₁ : ¬ D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) :=
      fun h => hDnot' (Or.inl h)
    have hDnot₂ : ¬ D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
      fun h => hDnot' (Or.inr h)
    have hD2 : IsPGroup 2 D := (hc.h131.isElemAb D hD).isPGroup
    obtain ⟨y, hyY, hyDT⟩ := w183k3m2_exists_conj_le_T hc.sylow (hc.h131.le_G D hD) hD2
    have hD'mem : cj y D ∈ Γ := hc.h131.invariant D hD y hyY
    have hD'3 := w183k3m2_three_le_mOf_or hc htwo hD'mem hall (hrk (cj y D) hD'mem)
    have hD'₁ : ¬ cj y D ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
      rcases htwo.perm y hyY with ⟨hyL₁, hyL₂⟩ | ⟨hyL₁, hyL₂⟩
      · have := w183k3m2_not_centralizes_cj (g := y) (D := D) (S := L₂) hDnot₂
        rwa [hyL₂] at this
      · have := w183k3m2_not_centralizes_cj (g := y) (D := D) (S := L₁) hDnot₁
        rwa [hyL₁] at this
    have hD'₂ : ¬ cj y D ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)) := by
      rcases htwo.perm y hyY with ⟨hyL₁, hyL₂⟩ | ⟨hyL₁, hyL₂⟩
      · have := w183k3m2_not_centralizes_cj (g := y) (D := D) (S := L₁) hDnot₁
        rwa [hyL₁] at this
      · have := w183k3m2_not_centralizes_cj (g := y) (D := D) (S := L₂) hDnot₂
        rwa [hyL₂] at this
    exact br3_false_of_two_sided rows hc htwo
      (fun D hD => (w183k3m2_mem_normalizer hc htwo hall hD).1)
      hED hD'mem hyDT hD'₁ hD'₂ hD'3 hshape.symm hZ

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
