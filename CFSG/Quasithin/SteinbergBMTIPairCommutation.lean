module

public import CFSG.Quasithin.SteinbergBMTIPairCalculus

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

private theorem mem_conjugate_iff_conj' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem conjugate_TI {D : Subgroup G}
    (hTI : ∀ x : G, D ⊓ CFSG.conjugate D x = ⊥ ∨ CFSG.conjugate D x = D) (g : G) :
    ∀ x : G, CFSG.conjugate D g ⊓ CFSG.conjugate (CFSG.conjugate D g) x = ⊥ ∨
      CFSG.conjugate (CFSG.conjugate D g) x = CFSG.conjugate D g := by
  intro x
  have key : ∀ z : G, z ∈ CFSG.conjugate (CFSG.conjugate D g) x ↔
      g * z * g⁻¹ ∈ CFSG.conjugate D (g * x * g⁻¹) := fun z => by
    rw [mem_conjugate_iff_conj', mem_conjugate_iff_conj', mem_conjugate_iff_conj',
      show g * x * g⁻¹ * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * z * x⁻¹) * g⁻¹ by group]
  rcases hTI (g * x * g⁻¹) with h | h
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    replace hz1 : g * z * g⁻¹ ∈ D := mem_conjugate_iff_conj'.mp hz1
    replace hz2 := (key z).mp hz2
    have hmem : g * z * g⁻¹ ∈ D ⊓ CFSG.conjugate D (g * x * g⁻¹) := ⟨hz1, hz2⟩
    rw [h, mem_bot] at hmem
    rw [mem_bot]
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [hmem]; group
  · right
    ext z
    rw [key, h, mem_conjugate_iff_conj']

theorem nq_elementary_TI_pair_commutation [Finite G] {U : Subgroup G}
    (hUe : CFSG.IsElementaryAbelian 2 U)
    (hTI : ∀ x : G, U ⊓ CFSG.conjugate U x = ⊥ ∨ CFSG.conjugate U x = U) {g : G}
    (hg : CFSG.conjugate U g ≠ U) :
    (CFSG.conjugate U g ⊓ centralizer (U : Set G) ≠ ⊥ → ⁅U, CFSG.conjugate U g⁆ = ⊥) ∧
      (IsPGroup 2 (U ⊔ CFSG.conjugate U g : Subgroup G) →
        CFSG.conjugate U g ⊓ normalizer (U : Set G) ≠ ⊥ → ⁅U, CFSG.conjugate U g⁆ = ⊥) := by
  set A := CFSG.conjugate U g with hAdef
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.map _
  obtain ⟨hUc, hU2⟩ := elementaryAbelian_two_facts hUe
  obtain ⟨hAc, hA2⟩ := elementaryAbelian_two_facts hAe
  have hUA : U ⊓ A = ⊥ := (hTI g).resolve_right hg
  have hATI := conjugate_TI hTI g
  have h : ElementaryTIPair U A := ⟨hUc, hU2, hAc, hA2, hUA, hTI, hATI⟩
  have hcard : Nat.card U = Nat.card A :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  refine ⟨fun hC => ?_, fun h2 hB => ?_⟩
  ·
    obtain ⟨⟨a, ha, haC⟩, ha1'⟩ := ne_bot_iff_exists_ne_one.mp hC
    have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
    have hUN : U ⊓ normalizer (A : Set G) = U := by
      refine inf_eq_left.mpr fun u hu => ?_
      exact mem_normalizer_of_commute_of_TI hATI ha ha1 (mem_centralizer_iff.mp haC u hu)
    exact h.commutator_eq_bot hUN (h.eq_of_eq hcard hUN)
  ·
    have h' := h.symm
    by_cases hBA : A ⊓ normalizer (U : Set G) = A
    · rw [commutator_comm]
      exact h'.commutator_eq_bot hBA (h'.eq_of_eq hcard.symm hBA)
    exfalso
    have hBlt : A ⊓ normalizer (U : Set G) < A := lt_of_le_of_ne inf_le_left hBA
    have hClt : U ⊓ normalizer (A : Set G) < U := h'.lt_of_lt hcard.symm hBlt
    obtain ⟨a, ha, haB⟩ := IsConcreteLE.exists_of_lt hBlt
    obtain ⟨u, hu, huC⟩ := IsConcreteLE.exists_of_lt hClt
    set Y := (A ⊓ normalizer (U : Set G)) ⊔ (U ⊓ normalizer (A : Set G)) with hY
    set X := U ⊔ A with hX
    have hYX : Y ≤ X :=
      sup_le (inf_le_left.trans le_sup_right) (inf_le_left.trans le_sup_left)
    have hXN : X ≤ normalizer (Y : Set G) := by
      refine sup_le h'.le_normalizer_sup ?_
      rw [hY, sup_comm]
      exact h.le_normalizer_sup
    have : (Y.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hYX).mpr hXN
    have hY1 : Y.subgroupOf X ≠ ⊥ := by
      obtain ⟨⟨b, hb⟩, hb1'⟩ := ne_bot_iff_exists_ne_one.mp hB
      intro hbot
      have hbY : (⟨b, hYX (mem_sup_left hb)⟩ : X) ∈ Y.subgroupOf X := mem_sup_left hb
      rw [hbot, mem_bot] at hbY
      exact hb1' (Subtype.ext (show b = 1 from congrArg Subtype.val hbY))
    have := h2.isNilpotent
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hY1
    obtain ⟨⟨⟨y, hyX⟩, hyY, hyZ⟩, hy1'⟩ := ne_bot_iff_exists_ne_one.mp hZ
    have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext (Subtype.ext h))
    have hyB : y ∈ A ⊓ normalizer (U : Set G) := by
      rw [← h'.sup_inf_centralizer ha haB]
      exact ⟨hyY, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hyZ ⟨a, mem_sup_right ha⟩)).symm⟩
    have hyC : y ∈ U ⊓ normalizer (A : Set G) := by
      rw [← h.sup_inf_centralizer hu huC]
      refine ⟨?_, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hyZ ⟨u, mem_sup_left hu⟩)).symm⟩
      have hyY' : y ∈ Y := hyY
      rw [hY, sup_comm] at hyY'
      exact hyY'
    have hmem : y ∈ (A ⊓ normalizer (U : Set G)) ⊓ (U ⊓ normalizer (A : Set G)) := ⟨hyB, hyC⟩
    rw [h'.inf_eq_bot, mem_bot] at hmem
    exact hy1 hmem

end CFSG.Quasithin.SteinbergBM
