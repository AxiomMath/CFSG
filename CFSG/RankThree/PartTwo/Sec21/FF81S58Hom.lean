module

import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem card_le_card_cen_mul_card_center {G : Type} [Group G] [Finite G] {T : Subgroup G} {l : G}
    (h : ∀ u ∈ T, l * u * l⁻¹ * u⁻¹ ∈ T ⊓ CenS T) :
    Nat.card T ≤ Nat.card ↥(T ⊓ Cen l) * Nat.card ↥(T ⊓ CenS T) := by
  let φ : T →* G :=
    { toFun := fun u => l * (u : G) * l⁻¹ * (u : G)⁻¹
      map_one' := by simp
      map_mul' := fun u v => by
        have hw : l * (v : G) * l⁻¹ * (v : G)⁻¹ ∈ CenS T :=
          (Subgroup.mem_inf.mp (h (v : G) v.2)).2
        have hc : (u : G)⁻¹ * (l * (v : G) * l⁻¹ * (v : G)⁻¹) =
            (l * (v : G) * l⁻¹ * (v : G)⁻¹) * (u : G)⁻¹ :=
          Subgroup.mem_centralizer_iff.mp hw ((u : G)⁻¹) (T.inv_mem u.2)
        show l * ((u : G) * (v : G)) * l⁻¹ * ((u : G) * (v : G))⁻¹ =
          (l * (u : G) * l⁻¹ * (u : G)⁻¹) * (l * (v : G) * l⁻¹ * (v : G)⁻¹)
        calc l * ((u : G) * (v : G)) * l⁻¹ * ((u : G) * (v : G))⁻¹
            = l * (u : G) * l⁻¹ * ((l * (v : G) * l⁻¹ * (v : G)⁻¹) * (u : G)⁻¹) := by group
          _ = l * (u : G) * l⁻¹ * ((u : G)⁻¹ * (l * (v : G) * l⁻¹ * (v : G)⁻¹)) := by
            rw [hc]
          _ = (l * (u : G) * l⁻¹ * (u : G)⁻¹) * (l * (v : G) * l⁻¹ * (v : G)⁻¹) := by group }
  have hφ : ∀ u : T, φ u = l * (u : G) * l⁻¹ * (u : G)⁻¹ := fun _ => rfl
  have hcen : ∀ x : T, (x : G) ∈ Cen l ↔ l * (x : G) * l⁻¹ * (x : G)⁻¹ = 1 := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hker : φ.ker = (T ⊓ Cen l).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, hφ, Subgroup.mem_subgroupOf, Subgroup.mem_inf, ← hcen x]
    exact ⟨fun h' => ⟨x.2, h'⟩, fun h' => h'.2⟩
  have hkerCard : Nat.card φ.ker = Nat.card ↥(T ⊓ Cen l) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ Cen l ≤ T)).toEquiv
  have hquot : Nat.card (↥T ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hrange : φ.range ≤ T ⊓ CenS T := by
    intro y hy
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [hφ]
    exact h (u : G) u.2
  calc Nat.card T = Nat.card (↥T ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    _ = Nat.card φ.range * Nat.card ↥(T ⊓ Cen l) := by rw [hquot, hkerCard]
    _ ≤ Nat.card ↥(T ⊓ CenS T) * Nat.card ↥(T ⊓ Cen l) :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hrange) (le_refl _)
    _ = Nat.card ↥(T ⊓ Cen l) * Nat.card ↥(T ⊓ CenS T) := Nat.mul_comm _ _

theorem card_of_model {H : Type} [Group H] (hH : StatedClassicalModel H .PSp 3 2 1) :
    Nat.card H = 1451520 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hH).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem inf_cenS_self_of_model {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : StatedClassicalModel K .PSp 3 2 1) : K ⊓ CenS K = ⊥ := by
  have hsimple : IsSimpleGroup K :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp K 3 2 1 hK
  have hcard : Nat.card K = 1451520 := card_of_model hK
  have hZ : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h0
    · exact h0
    · exfalso
      haveI : IsMulCommutative ↥K := Subgroup.center_eq_top_iff.mp h0
      have hprime : (Nat.card K).Prime := Group.is_simple_iff_prime_card.mp hsimple
      rw [hcard] at hprime
      norm_num at hprime
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxZ : (⟨x, hx.1⟩ : K) ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
