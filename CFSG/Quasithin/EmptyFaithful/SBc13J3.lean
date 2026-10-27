module

public import CFSG.Quasithin.EmptyFaithful.SBc13Pair
public import CFSG.Quasithin.EmptyFaithful.S146P12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem not_commutator_kz_le_pCore (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hp5 : p = 5) (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s) {J : Subgroup G} (hJG₂ : J ≤ g2_14615 K₂)
    (hJle : ¬ J ≤ g12_14615 T K₂) (hWG : pCoreOf 2 J ≤ mcOf T) :
    ¬ ⁅J, K₁ ⊔ K₂⁆ ≤ pCoreOf 2 J := by
  intro hcomm
  have hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ K₂ := hset.kz
  have hNle : Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ≤ mcOf T := by
    rw [← hKz]
    exact normalizer_kz_le_mcOf_14615 S h5 hred hdec hset
  have hGN : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← hKz]
    exact le_normalizer_conjClosure _ _
  have h5gen : K₁ ⊔ K₂ ≤ Subgroup.closure {x | x ∈ K₁ ⊔ K₂ ∧ orderOf x = 5} := by
    have := kz_le_closure_five_14615 S hdec hp5 hset
    rwa [hKz] at this
  set W := pCoreOf 2 J with hW
  have hWN : W ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hWG.trans hGN
  have hO : oTwoUpper (W ⊔ (K₁ ⊔ K₂)) = K₁ ⊔ K₂ := by
    apply le_antisymm
    · exact Der6A.oTwoUpper_le_of_normal_sup le_sup_right
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
          (sup_le hWN Subgroup.le_normalizer))
        (pCoreOf_isPGroup 2 J) le_sup_left (by rw [sup_comm])
    · refine h5gen.trans ((Subgroup.closure_le _).mpr fun x hx => ?_)
      obtain ⟨hxK, hx5⟩ := hx
      exact Subgroup.subset_closure ⟨Subgroup.mem_sup_right hxK, by rw [hx5]; decide⟩
  apply hJle
  intro x hxJ
  refine ⟨?_, hJG₂ hxJ⟩
  have hxW : conjSub x W = W :=
    conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 J hxJ)
  have hxKz : conjSub x (K₁ ⊔ K₂) ≤ W ⊔ (K₁ ⊔ K₂) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ : ∃ k ∈ K₁ ⊔ K₂, y = x * k * x⁻¹ :=
      ⟨x⁻¹ * y * x, mem_conjSub.mp hy, by group⟩
    have hc : x * k * x⁻¹ * k⁻¹ ∈ W := hcomm (by
      have := Subgroup.commutator_mem_commutator hxJ hk
      simpa [commutatorElement_def] using this)
    have e : x * k * x⁻¹ = (x * k * x⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact (W ⊔ (K₁ ⊔ K₂)).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hk)
  have hxY : conjSub x (W ⊔ (K₁ ⊔ K₂)) = W ⊔ (K₁ ⊔ K₂) := by
    have hle : conjSub x (W ⊔ (K₁ ⊔ K₂)) ≤ W ⊔ (K₁ ⊔ K₂) := by
      rw [show conjSub x (W ⊔ (K₁ ⊔ K₂)) = conjSub x W ⊔ conjSub x (K₁ ⊔ K₂) from
        Subgroup.map_sup _ _ _, hxW]
      exact sup_le le_sup_left hxKz
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub'])
  have hxK : conjSub x (K₁ ⊔ K₂) = K₁ ⊔ K₂ := by
    rw [← hO, ← oTwoUpper_conjSub_P, hxY]
  exact hNle (CosetGeom.mem_normalizer_of_conjSub_eq hxK)

end SBc13

end CFSG.Quasithin
