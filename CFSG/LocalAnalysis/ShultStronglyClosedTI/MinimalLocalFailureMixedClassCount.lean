module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassBasic

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_card_centralizer_eq_of_single_class {u z w : G}
    (hu : orderOf u = 2) (hz : orderOf z = 2) (huz : ¬ IsConj u z)
    (hsupp : ∀ a : G, orderOf a = 2 → ¬ IsConj w a →
      InvolutionCounting.thompsonPairCount u z a = 0)
    (hone : InvolutionCounting.thompsonPairCount u z w = 1) (hw : orderOf w = 2) :
    Nat.card G * Nat.card (Subgroup.centralizer ({w} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) *
        Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  classical
  have := Fintype.ofFinite G
  have hcount := InvolutionCounting.card_conjugatesOf_mul_eq_sum
    (InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hu)
    (InvolutionCounting.mul_self_eq_one_of_orderOf_eq_two hz) huz
  have hterm : ∀ a ∈ Finset.univ.filter (fun a : G => orderOf a = 2),
      InvolutionCounting.thompsonPairCount u z a = if IsConj w a then 1 else 0 := by
    intro a ha
    split_ifs with hwa
    · rw [← InvolutionCounting.thompsonPairCount_eq_of_isConj u z hwa, hone]
    · exact hsupp a (Finset.mem_filter.mp ha).2 hwa
  rw [Finset.sum_congr rfl hterm, Finset.sum_boole, Nat.cast_id, Finset.filter_filter] at hcount
  have hV : ((Finset.univ.filter fun a : G => orderOf a = 2 ∧ IsConj w a)).card =
      Nat.card (conjugatesOf w) := by
    rw [Nat.card_eq_card_toFinset]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    refine ⟨fun ha => ha.2, fun ha => ⟨?_, ha⟩⟩
    exact (InvolutionCounting.orderOf_eq_of_isConj ha).symm.trans hw
  rw [hV] at hcount
  have hu' := InvolutionCounting.card_centralizer_mul_card_conjugatesOf u
  have hz' := InvolutionCounting.card_centralizer_mul_card_conjugatesOf z
  have hw' := InvolutionCounting.card_centralizer_mul_card_conjugatesOf w
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G)) ?_
  calc Nat.card G * (Nat.card G * Nat.card (Subgroup.centralizer ({w} : Set G))) =
        Nat.card (Subgroup.centralizer ({w} : Set G)) *
          ((Nat.card (Subgroup.centralizer ({u} : Set G)) * Nat.card (conjugatesOf u)) *
            (Nat.card (Subgroup.centralizer ({z} : Set G)) * Nat.card (conjugatesOf z))) := by
        rw [hu', hz']
        ring
    _ = Nat.card (Subgroup.centralizer ({u} : Set G)) *
          Nat.card (Subgroup.centralizer ({z} : Set G)) *
          (Nat.card (Subgroup.centralizer ({w} : Set G)) * Nat.card (conjugatesOf w)) := by
        rw [← hcount]
        ring
    _ = Nat.card G * (Nat.card (Subgroup.centralizer ({u} : Set G)) *
          Nat.card (Subgroup.centralizer ({z} : Set G))) := by
        rw [hw']
        ring

theorem fixes_all_of_counts {H : Subgroup G} {u z w : G} {q : ℕ} (hq : 1 < q)
    (hthompson : Nat.card G * Nat.card (Subgroup.centralizer ({w} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) *
        Nat.card (Subgroup.centralizer ({z} : Set G)))
    (hzH : Nat.card (Subgroup.centralizer ({z} : Set G)) * (q - 1) = Nat.card H)
    (huH : Nat.card (H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      (q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G)))
    (hfix : Nat.card {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} *
        Nat.card (H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (Subgroup.centralizer ({u} : Set G))) :
    ∀ omega : rightCosetSpace H, rightCosetTranslate H omega u = omega := by
  set F := {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}
  have hindex : Nat.card H * Nat.card (rightCosetSpace H) = Nat.card G := by
    rw [card_rightCosetSpace]
    exact Subgroup.card_mul_index H
  have hH0 : 0 < Nat.card H := Nat.card_pos
  have hw0 : 0 < Nat.card (Subgroup.centralizer ({w} : Set G)) := Nat.card_pos
  have hq0 : 0 < q - 1 := by omega
  have hkey : Nat.card (rightCosetSpace H) = Nat.card F := by
    have hpos : 0 < Nat.card H * (q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G)) :=
      Nat.mul_pos (Nat.mul_pos hH0 hq0) hw0
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card H * (q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G)) *
          Nat.card (rightCosetSpace H) =
          (Nat.card H * Nat.card (rightCosetSpace H)) *
            Nat.card (Subgroup.centralizer ({w} : Set G)) * (q - 1) := by ring
      _ = Nat.card (Subgroup.centralizer ({u} : Set G)) *
            (Nat.card (Subgroup.centralizer ({z} : Set G)) * (q - 1)) := by
          rw [hindex, hthompson]
          ring
      _ = Nat.card F * ((q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G))) *
            Nat.card H := by
          rw [hzH, ← hfix, huH]
      _ = Nat.card H * (q - 1) * Nat.card (Subgroup.centralizer ({w} : Set G)) *
            Nat.card F := by ring
  have huniv : F = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ F) ?_
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hkey]
  intro omega
  have homega : omega ∈ F := huniv ▸ Set.mem_univ omega
  exact homega

end CFSG.ShultStronglyClosedTI.MixedClass
