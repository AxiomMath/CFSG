module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofChoice
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

namespace Item21Late2Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_centralizer_subgroupOf {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A) {X : Subgroup G}
    (hAX : A ≤ X) {x : X}
    (hx : x ∈ Subgroup.centralizer ((A.subgroupOf X : Subgroup X) : Set X)) (hx3 : x ^ 3 = 1) :
    x ∈ A.subgroupOf X := by
  have hx3' : (x : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  have hcomm : ∀ a ∈ A, ∀ z ∈ Subgroup.zpowers (x : G), a * z = z * a := by
    intro a ha z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have h1 : (⟨a, hAX ha⟩ : X) * x = x * ⟨a, hAX ha⟩ :=
      Subgroup.mem_centralizer_iff.mp hx ⟨a, hAX ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    have h2 : a * (x : G) = (x : G) * a := congrArg Subtype.val h1
    exact (Commute.zpow_right h2 k).eq
  have hE := Sec13.isElemAbelian_sup hAe (Sec13.isElemAbelian_zpowers hx3') hcomm
  have heq := hmax _ hE le_sup_left
  have hmem : (x : G) ∈ A := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact Subgroup.mem_subgroupOf.mpr hmem

end Item21Late2Proof

open Item21Late2Proof

theorem item2130ChoiceY_of (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) : Item2130ChoiceY := by
  intro G _ _ A E U c L U₀ b hcfg h9 hU₀ hU₀L hbB hb1 hU₀b
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfg.pair
  have hG := hpair.standing
  have hA := hpair.mem_S
  have hAe : IsElemAbelian 3 A := hA.1.1
  have hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hA.1.2.1
  have hEA : E ≤ A := hpair.mem_E.2
  have hEmem : E ∈ partTwoE G := hpair.mem_E.1
  have hA27 : Nat.card A = 27 := by rw [hcfg.card_eq, h9]
  have hEeq : E = A :=
    Subgroup.eq_of_le_of_card_ge hEA (by rw [hA27, hEmem.2.1])
  have hbA : b ∈ A := hbB.1
  have hbE : b ∈ E := hEeq ▸ hbA
  obtain ⟨hU₀E, hU₀ab, hU₀4⟩ := mem_fourGroups_iff.mp hU₀.1
  have hU₀2 : IsPGroup 2 U₀ := IsPGroup.of_card (n := 2) (by rw [hU₀4]; norm_num)
  set X := Subgroup.centralizer ({b} : Set G) with hX
  have hAX : A ≤ X := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
  have hO3 := Sec6.map_le_centralizer_pCore_of_omega (X := X) (E := A.subgroupOf X)
    (S := U₀.subgroupOf X) (Sec6.isElemAbelian_subgroupOf hAe)
    (hU₀2.comap_of_injective X.subtype X.subtype_injective)
    (Sec6.subgroupOf_le_normalizer_subgroupOf (hEeq ▸ hU₀E))
    (fun x hx hx3 => mem_of_mem_centralizer_subgroupOf hAe hmax hAX hx hx3)
  have hU₀θ : ¬ U₀ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
    intro hle
    have hbot := Sec6.commutator_eq_bot_of_mem_partTwoS hA hbA hb1 hEA hle hU₀2 hU₀E
    have hU₀bot : U₀ = ⊥ := hU₀.2.trans hbot
    have h1 : Nat.card U₀ = 1 := by rw [hU₀bot, Subgroup.card_bot]
    rw [hU₀4] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨Y, hYb, hYU⟩ := Sec6.exists_mem_thetaComponentsAt_not_le hU₀2 hU₀b hU₀θ hO3
  have hAN := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hAe hbA hb1
  have hU₀Y : U₀ ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hU₀.2]
    exact Sec6.commutator_le_normalizer_of_mem_thetaComponentsAt hU₀b
      (fun L' hL' => hEA.trans (hAN L' hL')) hYb
  have hYθ : ¬ ⁅Y, U₀⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro hle
    apply hYU
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hYb] at hle
    exact hle.trans inf_le_right
  obtain ⟨hYU₀, -, -, hY0, -⟩ := Sec6.props_of_moved hG h45 h49 hA hpair.mem_E hbE hb1 hYb
    hU₀2 hU₀b hU₀E hU₀.2.le hU₀Y hYθ
  exact ⟨Y, hYb, lZero_subset_lZeroUnion hEmem hEA hY0, hU₀Y, hYU₀⟩

end CFSG.RankThree.PartTwo.Sec21
