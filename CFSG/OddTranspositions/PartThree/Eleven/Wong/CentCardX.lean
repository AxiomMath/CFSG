module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentIndexTwo
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentAlt5

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem second_centralizer_card_and_diagonal_normal :
    Nat.card D.X = 480 ∧ D.X ≤ normalizer (D.A : Set G) ∧
    D.A ⊓ centralizer {D.v} = D.J ∧ centralizer {D.t} ⊓ D.X = closure {D.t, D.u} ⊔ D.A := by
  obtain ⟨K0, hK0, hidx, hK0T⟩ := D.index_two_centralizer_kernel
  obtain ⟨L0, hL0, hL0idx, hL0T, hAL⟩ := D.index_four_characteristic_kernel hK0 hidx hK0T
  have hLA : L0.map (D.X.subtype.comp K0.subtype) = D.A :=
    D.characteristic_kernel_eq_diagonal hK0 hidx hK0T hL0 hL0idx hL0T hAL
  have hA60 : Nat.card D.A = 60 := by
    obtain ⟨eA⟩ := D.toSwapData.nonempty_A_mulEquiv_alt5
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hinj : Function.Injective (D.X.subtype.comp K0.subtype) := fun a b h =>
    K0.subtype_injective (D.X.subtype_injective h)
  have hL0card : Nat.card L0 = 60 := by
    rw [← Subgroup.card_map_of_injective (K := L0) hinj, hLA]
    exact hA60
  have hK0card : Nat.card K0 = 240 := by
    have h := Subgroup.card_mul_index L0
    rw [hL0card, hL0idx] at h
    omega
  have hXcard : Nat.card D.X = 480 := by
    have h := Subgroup.card_mul_index K0
    rw [hK0card, hidx] at h
    omega
  have hXnorm : D.X ≤ normalizer (D.A : Set G) := by
    rw [← hLA]
    exact D.map_characteristic_le_normalizer_X hK0 hL0
  have hAX : D.A ≤ D.X := by
    rintro _ ⟨x, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (D.d_commute_u x).eq
  have hAv : D.A ⊓ centralizer {D.v} = D.J := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxv⟩ := mem_inf.mp hx
      rw [← hL0T]
      exact mem_inf.mpr ⟨hAL hxA, mem_inf.mpr ⟨hAX hxA, hxv⟩⟩
    · refine le_inf D.J_le_A ?_
      refine (closure_le _).mpr ?_
      rintro g (rfl | rfl)
      · exact mem_centralizer_singleton_iff.mpr (Commute.refl D.v).eq
      · exact mem_centralizer_singleton_iff.mpr D.commute_v_w.eq.symm
  exact ⟨hXcard, hXnorm, hAv, D.toSwapData.centralizer_t_inf_centralizer_u⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
