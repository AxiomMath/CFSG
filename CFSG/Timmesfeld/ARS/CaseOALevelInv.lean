module

public import CFSG.Timmesfeld.ARS.CaseEDist
public import CFSG.Timmesfeld.ARS.CaseEWeight

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem CFSG.LieType.Universal

variable {I : Type} [Fintype I] [DecidableEq I]

@[expose] def StarOneAt (A : Matrix I I ℤ) (hA : TauCeti.IsFiniteType A) (j : I) : Prop :=
  ∀ γ ∈ roots hA ∅, γ j = 1 → ∃ β ∈ roots hA ∅, β j = 1 ∧ coroot A j β = 0 ∧
    cartanPair A β γ = 0

section Level

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

include hA in
theorem levelInv_nonempty (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {j : I}
    (hstar : StarOneAt A hA j) {u v y : (coxeterMatrix hA).Group}
    (hu : u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (hv : v ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j})
    (hy : y = 1 ∨ y = (coxeterMatrix hA).toCoxeterSystem.simple j ∨
      ∃ z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k ≠ j},
        y = (coxeterMatrix hA).toCoxeterSystem.simple j * z *
        (coxeterMatrix hA).toCoxeterSystem.simple j) :
    (levelInv hA j (u * y * v)).Nonempty := by
  have hsymm := cartan_symm_of_posDef hpd
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hαj : (Pi.single j 1 : I → ℤ) ∈ roots hA ∅ := Or.inl ⟨1, j, by simp⟩
  have hsj : ∀ β : I → ℤ, coroot A j β = 0 → weylAction hA (cs.simple j) β = β := fun β h => by
    rw [weylAction_simple, reflection_apply_coroot, h, zero_smul, sub_zero]
  have hy1 : (levelInv hA j y).Nonempty := by
    rcases hy with rfl | rfl | ⟨z, hz, rfl⟩
    · exact ⟨Pi.single j 1, hαj, by simp, by simp⟩
    · obtain ⟨β, hβ, h2, h3, -⟩ := hstar _ hαj (by simp)
      exact ⟨β, hβ, h2, by rw [CoxeterSystem.inv_simple, hsj _ h3, h2]⟩
    · set γ := weylAction hA z (Pi.single j 1) with hγ
      have hγr : γ ∈ roots hA ∅ := weylAction_mem_roots hA _ hαj
      have hγj : γ j = 1 := by
        rw [hγ, weylAction_apply_self_of_mem_parabolic hA hz]
        simp
      obtain ⟨β, hβ, h2, h3, h4⟩ := hstar γ hγr hγj
      refine ⟨β, hβ, h2, ?_⟩
      have hz1 : weylAction hA z⁻¹ β j = 1 := by
        rw [weylAction_apply_self_of_mem_parabolic hA (inv_mem hz), h2]
      have hz2 : coroot A j (weylAction hA z⁻¹ β) = 0 := by
        rw [← cartanPair_single, ← cartanPair_weylAction hA hsymm z,
          weylAction_apply_inv_apply, h4]
      rw [mul_inv_rev, mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply,
        weylAction_mul_apply, hsj _ h3, hsj _ hz2, hz1]
  obtain ⟨β, hβ⟩ := hy1
  exact ⟨weylAction hA u β, levelInv_mul_right hA hv _ (levelInv_mul_left hA hu _ hβ)⟩

include hA in
theorem levelInv_eq_empty {w₀ : (coxeterMatrix hA).Group} {σ : I → I}
    (hσ : ∀ k, weylAction hA w₀ (Pi.single k 1) = -Pi.single (σ k) 1) (hσinj : Function.Injective σ)
    {j : I} (hσj : σ j = j) : levelInv hA j w₀ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun β hβ => ?_
  obtain ⟨-, h2, h3⟩ := hβ
  rw [weylAction_inv_apply_self_of_neg hA hσ hσinj hσj, h2] at h3
  omega

end Level

section TwoStep

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem not_twoStep_of_starOneAt (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {j : Fin D.rank}
    (hstar : StarOneAt D.cartan D.isFiniteType j) {w₀ : (coxeterMatrix D.isFiniteType).Group}
    {σ : Fin D.rank → Fin D.rank}
    (hσ : ∀ k, weylAction D.isFiniteType w₀ (Pi.single k 1) = -Pi.single (σ k) 1)
    (hσinj : Function.Injective σ) (hσj : σ j = j) : ¬ twoStep j w₀ := by
  rintro ⟨u, hu, v, hv, y, hy, rfl⟩
  obtain ⟨β, hβ⟩ := levelInv_nonempty D.isFiniteType hpd hstar hu hv hy
  rw [levelInv_eq_empty D.isFiniteType hσ hσinj hσj] at hβ
  exact hβ

end TwoStep

end CFSG.Timmesfeld.ARS
