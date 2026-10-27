module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[instance_reducible] private noncomputable def r920imf_conjAction (A U W : Subgroup G) {u : G}
    (hAW : A ≤ normalizer (W : Set G)) (hUW : U ≤ normalizer (W : Set G)) (hu : u ∈ U)
    (hfix : ∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) : MulAction ↥A W where
  smul a w :=
    ⟨u⁻¹ * (a : G) * (u * (w : G)) * (a : G)⁻¹, by
      have haW : (a : G) * (w : G) * (a : G)⁻¹ ∈ W :=
        (Subgroup.le_normalizer_iff.mp hAW) (a : G) a.2 (w : G) w.2
      have hconj : u⁻¹ * ((a : G) * u * (a : G)⁻¹ * u⁻¹) * (u⁻¹)⁻¹ ∈ W :=
        (Subgroup.le_normalizer_iff.mp hUW) u⁻¹ (inv_mem hu) _ (hfix (a : G) a.2)
      have heq : u⁻¹ * (a : G) * (u * (w : G)) * (a : G)⁻¹ =
          (u⁻¹ * ((a : G) * u * (a : G)⁻¹ * u⁻¹) * (u⁻¹)⁻¹) *
            ((a : G) * (w : G) * (a : G)⁻¹) := by group
      rw [heq]
      exact mul_mem hconj haW⟩
  one_smul w := by
    apply Subtype.ext
    simp [HSMul.hSMul]
  mul_smul a b w := by
    apply Subtype.ext
    simp only [HSMul.hSMul, Subgroup.coe_mul]
    group

theorem mem_of_fixed_coset_of_coprime {p : ℕ} (hp : p.Prime) {M U W A : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hAp : Nat.card A = p) (hAu : A ∈ uniqueSet M)
    (hAU : A ≤ normalizer (U : Set G)) (hAW : A ≤ normalizer (W : Set G)) (hWU : W ≤ U)
    (hUW : U ≤ normalizer (W : Set G)) (hUp : ¬ p ∣ Nat.card U) (hUM : U ⊓ M ≤ W) {u : G}
    (hu : u ∈ U) (hfix : ∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ W) : u ∈ W := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI := r920imf_conjAction A U W hAW hUW hu hfix
  have hApg : IsPGroup p ↥A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hAp)
  have hcop : ¬ p ∣ Nat.card W := fun h => hUp (h.trans (Subgroup.card_dvd_of_le hWU))
  obtain ⟨w, hwfix⟩ := hApg.nonempty_fixed_point_of_prime_not_dvd_card W hcop
  have hcent : u * (w : G) ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfixu : u⁻¹ * (a : G) * (u * (w : G)) * (a : G)⁻¹ = (w : G) := by
      have h := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hwfix ⟨a, ha⟩)
      change u⁻¹ * (a : G) * (u * (w : G)) * (a : G)⁻¹ = (w : G) at h
      exact h
    have hfixa : (a : G) * (u * (w : G)) * (a : G)⁻¹ = u * (w : G) := by
      calc (a : G) * (u * (w : G)) * (a : G)⁻¹
          = u * (u⁻¹ * (a : G) * (u * (w : G)) * (a : G)⁻¹) := by group
        _ = u * (w : G) := by rw [hfixu]
    calc (a : G) * (u * (w : G)) = (a : G) * (u * (w : G)) * (a : G)⁻¹ * (a : G) := by
          group
      _ = (u * (w : G)) * (a : G) := by rw [hfixa]
  have hxM : u * (w : G) ∈ M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hAu
      (Subgroup.centralizer_le_normalizer (A : Set G) hcent)
  have hxU : u * (w : G) ∈ U := mul_mem hu (hWU w.2)
  have hxW : u * (w : G) ∈ W := hUM ⟨hxU, hxM⟩
  have hu_eq : u = (u * (w : G)) * (w : G)⁻¹ := by group
  rw [hu_eq]
  exact mul_mem hxW (inv_mem w.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
