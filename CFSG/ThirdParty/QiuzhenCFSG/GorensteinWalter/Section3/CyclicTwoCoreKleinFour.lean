module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreSetup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.FinalTheorem
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

set_option maxHeartbeats 800000 in
public theorem firstCase_U_eq_FU_sup_B
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    (hcomm : ⁅(bg.S : Subgroup G), bg.U⁆ ≤ fittingSubgroupOf bg.U) :
    bg.U = fittingSubgroupOf bg.U ⊔ bg.B := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hSnormU : (bg.S : Subgroup G) ≤ Subgroup.normalizer (bg.U : Set G) :=
    BenderGlauberman.S4_S_le_normalizer_U bg
  let : Subgroup.Normalizes (bg.S : Subgroup G) bg.U := ⟨hSnormU⟩
  have hUodd : Nat.Coprime 2 (Nat.card bg.U) :=
    BenderGlauberman.U_coprime_two bg
  have hcop : Nat.Coprime (Nat.card (bg.S : Subgroup G)) (Nat.card bg.U) := by
    obtain ⟨n, hn⟩ := bg.S.isPGroup'.exists_card_eq
    rw [hn]
    exact hUodd.pow_left n
  have hsolv : IsSolvable bg.U :=
    odd_order_theorem bg.U (Nat.coprime_two_left.mp hUodd)
  have hdecomp :
      fixedPointSubgroup (bg.S : Subgroup G) bg.U ⊔
          commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
      hsolv hcop
  have hfixMap_le :
      (fixedPointSubgroup (bg.S : Subgroup G) bg.U).map bg.U.subtype ≤ bg.B := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact BenderGlauberman.mem_B_of_fixed_s4 bg hy
  have hcommMap :
      (commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U)).map bg.U.subtype =
        ⁅bg.U, (bg.S : Subgroup G)⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator
      bg.U (bg.S : Subgroup G) hSnormU
  have htopMap : (⊤ : Subgroup bg.U).map bg.U.subtype = bg.U := by
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := bg.U))
  apply le_antisymm
  · have hsourceEq :
        bg.U =
          (fixedPointSubgroup (bg.S : Subgroup G) bg.U).map bg.U.subtype ⊔
            (commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U)).map
              bg.U.subtype := by
      calc
        bg.U = (⊤ : Subgroup bg.U).map bg.U.subtype := htopMap.symm
        _ = (fixedPointSubgroup (bg.S : Subgroup G) bg.U ⊔
              commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U)).map
              bg.U.subtype := by rw [hdecomp]
        _ = (fixedPointSubgroup (bg.S : Subgroup G) bg.U).map bg.U.subtype ⊔
              (commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U)).map
                bg.U.subtype := Subgroup.map_sup _ _ _
    have hcomm' : ⁅bg.U, (bg.S : Subgroup G)⁆ ≤ fittingSubgroupOf bg.U := by
      simpa [Subgroup.commutator_comm] using hcomm
    have hfixLe :
        (fixedPointSubgroup (bg.S : Subgroup G) bg.U).map bg.U.subtype ≤
          fittingSubgroupOf bg.U ⊔ bg.B :=
      hfixMap_le.trans le_sup_right
    have hcommLe :
        (commutatorAction (A := (bg.S : Subgroup G)) (G := bg.U)).map bg.U.subtype ≤
          fittingSubgroupOf bg.U ⊔ bg.B :=
      (le_of_eq hcommMap).trans (hcomm'.trans le_sup_left)
    exact (le_of_eq hsourceEq).trans (sup_le hfixLe hcommLe)
  · apply sup_le
    · exact fittingSubgroupOf_le bg.U
    · intro x hx
      exact BenderGlauberman.mem_U_of_mem_B_s4 bg hx

@[expose]
public def firstCaseKleinFourOfCommutingInvolutions
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Subgroup G where
  carrier := {a * b, a, b, 1}
  one_mem' := by simp
  mul_mem' := by
    have hba : b * a = a * b := hab.eq.symm
    have ha_ab : a * (a * b) = b := by
      rw [← mul_assoc, ha, one_mul]
    have hb_ab : b * (a * b) = a := by
      rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    have hab_a : (a * b) * a = b := by
      rw [mul_assoc, hba, ha_ab]
    have hab_b : (a * b) * b = a := by
      rw [mul_assoc, hb, mul_one]
    have hab_sq : (a * b) * (a * b) = 1 := by
      rw [← mul_assoc, hab_a, hb]
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      rcases hy with (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
  inv_mem' := by
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hab_sq : (a * b) * (a * b) = 1 := by
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab.eq.symm]
        _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
    have hab_inv : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right hab_sq
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      simp [ha_inv, hb_inv, hab_inv]

public theorem firstCaseKleinFourOfCommutingInvolutions_isKleinFour
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (habne : a ≠ b) (hab : Commute a b) :
    IsKleinFour (firstCaseKleinFourOfCommutingInvolutions a b ha hb hab) := by
  classical
  let V := firstCaseKleinFourOfCommutingInvolutions a b ha hb hab
  have hoa : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha) ha1
  have hob : orderOf b = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hb) hb1
  have habnot : a * b ∉ ({a, b, 1} : Set G) :=
    mul_notMem_of_orderOf_eq_two hoa hob habne
  constructor
  · change Nat.card V = 4
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({a * b, a, b, 1} : Set G).ncard = 4
    simp [habnot, ha1, hb1, habne]
  · apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      rcases x with ⟨x, hx⟩
      apply Subtype.ext
      change x ^ 2 = 1
      change x ∈ ({a * b, a, b, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · calc
          (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
          _ = a * (a * b) * b := by rw [hab.eq.symm]
          _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · simp
    · have haV : a ∈ V := by
        change a ∈ ({a * b, a, b, 1} : Set G)
        simp
      have hordV : orderOf (⟨a, haV⟩ : V) = 2 := by
        simpa [Subgroup.orderOf_mk] using hoa
      simpa [hordV] using
        (Monoid.order_dvd_exponent (⟨a, haV⟩ : V))

public structure FirstCaseFourData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) where
  V1 : Subgroup G
  V2 : Subgroup G
  V1_klein : IsKleinFour V1
  V2_klein : IsKleinFour V2
  t_mem_V1 : c.t ∈ V1
  t_mem_V2 : c.t ∈ V2
  t1_mem_V1 : d.bg.t1 ∈ V1
  t2_mem_V2 : d.bg.t2 ∈ V2
  V1_le_S : V1 ≤ (c.S : Subgroup G)
  V2_le_S : V2 ≤ (c.S : Subgroup G)

public theorem exists_firstCaseFourData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseBGData c) :
    Nonempty (FirstCaseFourData c d) := by
  classical
  have htS : c.t ∈ (c.S : Subgroup G) := c.S0_le_S c.t_mem_S0
  have ht1S : d.bg.t1 ∈ (c.S : Subgroup G) := by
    simpa [d.S_eq] using d.bg.t1_mem_S
  have ht2S : d.bg.t2 ∈ (c.S : Subgroup G) := by
    simpa [d.S_eq] using d.bg.t2_mem_S
  have htt : c.t * c.t = 1 := by
    simpa [pow_two] using c.t_involution.2
  have ht1t1 : d.bg.t1 * d.bg.t1 = 1 := by
    simpa [pow_two] using d.bg.t1_involution.2
  have ht2t2 : d.bg.t2 * d.bg.t2 = 1 := by
    simpa [pow_two] using d.bg.t2_involution.2
  have hcomm1 : Commute c.t d.bg.t1 := by
    have ht1H : d.bg.t1 ∈ c.H := centralizerSetup_S_le_H c ht1S
    rw [c.H_eq_centralizer,
      Subgroup.mem_centralizer_singleton_iff] at ht1H
    exact ht1H.symm
  have hcomm2 : Commute c.t d.bg.t2 := by
    have ht2H : d.bg.t2 ∈ c.H := centralizerSetup_S_le_H c ht2S
    rw [c.H_eq_centralizer,
      Subgroup.mem_centralizer_singleton_iff] at ht2H
    exact ht2H.symm
  have htS0bg : c.t ∈ d.bg.S0 := by
    simpa [d.S0_eq] using c.t_mem_S0
  have hne1 : c.t ≠ d.bg.t1 := by
    intro h
    apply d.bg.t1_not_mem_S0
    rw [← h]
    exact htS0bg
  have hne2 : c.t ≠ d.bg.t2 := by
    intro h
    apply d.bg.t2_not_mem_S0
    rw [← h]
    exact htS0bg
  let V1 := firstCaseKleinFourOfCommutingInvolutions
    c.t d.bg.t1 htt ht1t1 hcomm1
  let V2 := firstCaseKleinFourOfCommutingInvolutions
    c.t d.bg.t2 htt ht2t2 hcomm2
  refine ⟨{
    V1 := V1
    V2 := V2
    V1_klein := firstCaseKleinFourOfCommutingInvolutions_isKleinFour
      c.t d.bg.t1 htt ht1t1 c.t_involution.1 d.bg.t1_involution.1 hne1 hcomm1
    V2_klein := firstCaseKleinFourOfCommutingInvolutions_isKleinFour
      c.t d.bg.t2 htt ht2t2 c.t_involution.1 d.bg.t2_involution.1 hne2 hcomm2
    t_mem_V1 := by simp [V1, firstCaseKleinFourOfCommutingInvolutions]
    t_mem_V2 := by simp [V2, firstCaseKleinFourOfCommutingInvolutions]
    t1_mem_V1 := by simp [V1, firstCaseKleinFourOfCommutingInvolutions]
    t2_mem_V2 := by simp [V2, firstCaseKleinFourOfCommutingInvolutions]
    V1_le_S := by
      intro x hx
      change x ∈ ({c.t * d.bg.t1, c.t, d.bg.t1, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · exact (c.S : Subgroup G).mul_mem htS ht1S
      · exact htS
      · exact ht1S
      · exact (c.S : Subgroup G).one_mem
    V2_le_S := by
      intro x hx
      change x ∈ ({c.t * d.bg.t2, c.t, d.bg.t2, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · exact (c.S : Subgroup G).mul_mem htS ht2S
      · exact htS
      · exact ht2S
      · exact (c.S : Subgroup G).one_mem
  }⟩


end CFSG.GorensteinWalter
