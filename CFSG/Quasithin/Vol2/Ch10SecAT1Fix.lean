module

public import CFSG.Quasithin.Vol2.Ch10SecAT1TorusMain
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5One
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_isHallTwoPrimeOf_B0 (hyp : Ch10.Hyp10 G T L I) :
    ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D (B0 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSB, hS2, hSidx⟩ := isSylowTwoOf_T0_inf_B0 hyp
  have hN : ((T0 T L ⊓ B0 T L).subgroupOf (B0 T L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr fun b hb =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨(oTwoUpper_le _ hb).2, Subgroup.le_normalizer hb⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hS2
  have hNcard : Nat.card ((T0 T L ⊓ B0 T L).subgroupOf (B0 T L)) = 2 ^ j := by
    rw [← hj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv
  have hodd : Odd ((T0 T L ⊓ B0 T L).subgroupOf (B0 T L)).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSidx)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (T0 T L ⊓ B0 T L).subgroupOf (B0 T L))
    (by rw [hNcard]; exact (Nat.coprime_two_left.mpr hodd).pow_left j)
  refine ⟨H.map (B0 T L).subtype, Subgroup.map_subtype_le _, ?_, j, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ← hH.symm.index_eq_card]
    exact hodd
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _), hH.index_eq_card,
      hNcard]

theorem exists_mem_centralizer_T1_of_case_one
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I)
    {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n) :
    ∃ x ∈ fsuUL T L I, x ∉ fsuCVM T L I ∧ x ∈ Subgroup.centralizer (T1 T L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  have hloc := hyp.fsu.maximal.1
  obtain ⟨D, hD⟩ := exists_isHallTwoPrimeOf_B0 hyp
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hUt := (ha t ht htn).2.2
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I) (fsuL0_le_normalizer hloc)
  set Y := fsuUL T L I ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) with hYdef
  have hYV : Y ≤ fsuVM T L I := inf_le_left.trans (fsuUL_le_fsuVM T L I)
  have hT0Y : T0 T L ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    intro y hy
    exact mem_centralizer_T0 h37 h38 h322 hyp ht htn (hYV hy) hy.2
      (Subgroup.centralizer_le (fun _ hx => hx.2) (hUt hy.1))
  have hB0Y : B0 T L ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hL0U (oTwoUpper_le _ hb).1,
      le_normalizer_centralizer le_rfl (mem_normalizer_inf_of_mem (le_fsuL0 T L)
        (fsuL0_le_normalizer hloc) (oTwoUpper_le _ hb).1 (oTwoUpper_le _ hb).2)⟩
  have hDY : D ≤ Subgroup.normalizer (Y : Set G) := hD.1.trans hB0Y
  have hKD := commutator_B0_le hyp hD hT0Y hDY
  set K := ⁅Y, B0 T L⁆ with hKdef
  have hKY : K ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hB0Y
  have hS : ∀ {w : G}, w ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) →
      ∀ s ∈ T ⊓ L, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I := by
    intro w hw s hs
    rw [Subgroup.mem_centralizer_iff.mp hw s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  by_cases hK : K = ⊥
  · exfalso
    obtain ⟨h, hhL, hhN, hhodd, hhU⟩ := exists_torus_element h37 h38 hyp h1
    have hhB0 : h ∈ B0 T L := mem_oTwoUpper_of_odd ⟨le_fsuL0 T L hhL, hhN⟩ hhodd
    obtain ⟨v, hvU, hvC, hvS⟩ := exists_mem_centralizer_of_case_one hyp h1
    have hhv : h * v * h⁻¹ * v⁻¹ ∈ fsuCVM T L I := by
      have hvY : v ∈ Y := Subgroup.mem_inf.mpr ⟨hvU, hvS⟩
      have h2 : ⁅v, h⁆ ∈ K := Subgroup.commutator_mem_commutator hvY hhB0
      rw [hK, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      rw [← h2, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact hhU (centralizes_of_case_one h37 h38 hyp h1 (le_fsuL0 T L hhL) hhodd
      (mem_normalizer_inf_of_mem (le_fsuL0 T L) (fsuL0_le_normalizer hloc) (le_fsuL0 T L hhL)
        hhN) hvU hvC (hS hvS) hhv)
  have hKT : K ≤ T := hKY.trans (hYV.trans (fsuVM_le_T hyp))
  have hT1U : T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fun r hr => fsuM_le_normalizer_fsuVM T L I
      (le_fsuM T L (Subgroup.mem_inf.mp hr).1)) (fun r hr => (Subgroup.mem_inf.mp hr).2)
  have hT1Y : T1 T L ≤ Subgroup.normalizer (Y : Set G) := fun r hr =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hT1U hr, le_normalizer_centralizer le_rfl
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (Subgroup.mem_inf.mp hr).1, (Subgroup.mem_inf.mp hr).2⟩)⟩
  have hT1B0 : T1 T L ≤ Subgroup.normalizer (B0 T L : Set G) :=
    inf_le_left.trans (le_normalizer_B0 T L)
  have hP : IsPGroup 2 ↥(K ⊔ T1 T L) := hyp.fsu.sylow.1.to_le (sup_le hKT inf_le_left)
  have hPK : K ⊔ T1 T L ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_commutator hT1Y hT1B0)
  obtain ⟨k, hkK, hk1, hkC⟩ := exists_ne_one_mem_centralizer hP le_sup_left hPK hK
  refine ⟨k, (hKY hkK).1, fun hkC0 => hk1 ?_,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hkC⟩
  have hYab : IsMulCommutative ↥Y :=
    ⟨⟨fun a b => Subtype.ext (comm_of_mem_fsuVM hyp (hYV a.2) (hYV b.2))⟩⟩
  have h1' := commutator_inf_centralizer_eq_bot (W := Y) (D := D)
    (fun y hy => (isElemAbelian_fsuVM hyp).2 y (hYV hy)) hD.2.1 hDY
  have h2 : k ∈ ⁅Y, D⁆ ⊓ Subgroup.centralizer (D : Set G) :=
    ⟨hKD hkK, Subgroup.mem_centralizer_iff.mpr fun d hd =>
      Subgroup.mem_centralizer_iff.mp hkC0.2 d (oTwoUpper_le _ (hD.1 hd)).1⟩
  rw [h1', Subgroup.mem_bot] at h2
  exact h2

theorem exists_mem_centralizer_T1_of_fsuCVM_eq_bot (hyp : Ch10.Hyp10 G T L I)
    (hC0 : fsuCVM T L I = ⊥) :
    ∃ x ∈ fsuUL T L I, x ∉ fsuCVM T L I ∧ x ∈ Subgroup.centralizer (T1 T L : Set G) := by
  have hT1U : T1 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fun r hr => fsuM_le_normalizer_fsuVM T L I
      (le_fsuM T L (Subgroup.mem_inf.mp hr).1)) (fun r hr => (Subgroup.mem_inf.mp hr).2)
  have hP : IsPGroup 2 ↥(fsuUL T L I ⊔ T1 T L) := hyp.fsu.sylow.1.to_le
    (sup_le ((fsuUL_le_fsuVM T L I).trans (fsuVM_le_T hyp)) inf_le_left)
  obtain ⟨x, hxU, hx1, hxC⟩ := exists_ne_one_mem_centralizer hP le_sup_left
    (sup_le Subgroup.le_normalizer hT1U) (commutator_fsuVM_ne_bot hyp.fsu)
  exact ⟨x, hxU, by rw [hC0, Subgroup.mem_bot]; exact hx1,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hxC⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
