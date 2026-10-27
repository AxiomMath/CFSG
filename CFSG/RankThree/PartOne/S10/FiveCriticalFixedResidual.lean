module

public import CFSG.RankThree.PartOne.S10.FiveCriticalOddCore
import CFSG.RankThree.PartOne.S10.FiveCriticalResidual
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartOne.FiveCritical

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem five_fixed_residual_fields {G : Type} [Group G] [Finite G] {A L : Subgroup G} {x : G}
    (hAL : A ≤ normalizer (L : Set G)) (hAe : IsElementaryAbelian 5 A)
    (hLperf : Group.IsPerfect L)
    (hLq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 5 L))
    (hLO : haveI := oddThetaCore_subgroupOf_normal 5 L;
      CFSG.IsQuasisimple (L ⧸ (oddThetaCore 5 L).subgroupOf L))
    (hcomm : ⁅inSubgroup (aschbacherSolvableCore 5) L, L⁆ ≤ oddThetaCore 5 L)
    (hxE : x ∈ thetaQuotientCentralizer 5 A L) (hx1 : x ≠ 1) :
    (fiveResidual L x).subgroupOf (L ⊓ centralizer ({x} : Set G)) ∈
        thetaComponents 5 ↥(L ⊓ centralizer ({x} : Set G)) ∧
    L = oddThetaCore 5 L ⊔ fiveResidual L x ∧
    L ⊓ centralizer ({x} : Set G) =
      (oddThetaCore 5 L ⊓ centralizer ({x} : Set G)) ⊔ fiveResidual L x ∧
    (∀ R : Subgroup G, R ≤ L → IsPGroup 2 R → R ≤ centralizer ({x} : Set G) →
      R ≤ fiveResidual L x) ∧
    (CFSG.IsQuasisimple ↥(fiveResidual L x) → ∀ {q : ℕ}, q.Prime → ∀ D : Subgroup G, D ≤ L →
      (D.subgroupOf L).Normal → IsPGroup q D → ⁅L, D⁆ ≠ ⊥ → ∀ z ∈ fiveResidual L x,
      (∃ k : ℕ, ∀ d ∈ D, (z * d * z⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D) →
      z ∈ centralizer (fiveResidual L x : Set G)) := by
  have hp5 : Nat.Prime 5 := by norm_num
  have hxA : x ∈ A := (mem_thetaQuotientCentralizer_iff.mp hxE).1
  have hx5 : orderOf x = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp5 hxA hx1
  have hzE : zpowers x ≤ thetaQuotientCentralizer 5 A L := Subgroup.zpowers_le.mpr hxE
  have hzA : zpowers x ≤ A := hzE.trans inf_le_left
  have hUN : zpowers x ≤ normalizer (L : Set G) := hzA.trans hAL
  have hUp : IsPGroup 5 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx5]
    simp)
  have hUO : zpowers x ≤ normalizer (oddThetaCore 5 L : Set G) :=
    hzA.trans (le_normalizer_oddThetaCore hp5 hAL)
  have hUtriv : ∀ u ∈ zpowers x, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ oddThetaCore 5 L :=
    fun u hu l hl => five_E_trivial_mod_O hp5 hAL hLperf hcomm (hzE hu) l hl
  have hUtrivθ : ∀ u ∈ zpowers x, ∀ l ∈ L,
      u * l * u⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 5) L :=
    fun u hu l hl => (((sectionTen_quotient_action_kernel 5 hAL).2 u).mp (hzE hu)).2 l hl
  obtain ⟨h1, h2, h3, h4⟩ := odd_core_fixed_residual_ambient hp5 hUN hLperf hLO hUp hUO hUtriv
  have h5 := theta_component_fixed_residual_ambient hp5 hUN hLq hUp hUtrivθ
  have hC : centralizer ({x} : Set G) = centralizer (zpowers x : Set G) :=
    SteinbergBY.centralizer_singleton_eq_centralizer_zpowers x
  unfold fiveResidual
  rw [hC]
  exact ⟨h5, h1, h2, fun R hRL hR2 hRC => h3 R (le_inf hRL hRC) hR2, h4⟩

end CFSG.RankThree.PartOne.FiveCritical
