module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedClass

import CFSG.RankThree.GF2n.Stroth78.Sec3SevenFix

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem sq_mem_CHbar_of_fix (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {Y : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u) {y : Hbar z} (hy : y ∈ Y) :
    y ^ 2 ∈ CHbar S a := by
  obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective y
  refine (mem_CHbar_iff S a _).mpr ⟨ℓ ^ 2, ?_, by rw [QuotientGroup.mk_pow]⟩
  have hmem : ⁅a, (ℓ : G)⁆ ∈ ZQ z :=
    commutator_mem_ZQ_of_fix S ℓ ⟨a, haQ⟩ (hfix _ hy)
  have h1 := congrArg Subtype.val (hZ _ hy ⟨⁅a, (ℓ : G)⁆, hmem⟩)
  have h2 := rhoZ_mk S ℓ ⟨⁅a, (ℓ : G)⁆, hmem⟩
  have hc : (ℓ : G) * ⁅a, (ℓ : G)⁆ * (ℓ : G)⁻¹ = ⁅a, (ℓ : G)⁆ := h2.symm.trans h1
  have hsq : ⁅a, (ℓ : G)⁆ * ⁅a, (ℓ : G)⁆ = 1 := by
    have := ZQ_mul_self S ⟨⁅a, (ℓ : G)⁆, hmem⟩
    exact congrArg Subtype.val this
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hid : ⁅a, ((ℓ ^ 2 : ↥(H z)) : G)⁆ =
      ⁅a, (ℓ : G)⁆ * ((ℓ : G) * ⁅a, (ℓ : G)⁆ * (ℓ : G)⁻¹) := by
    rw [pow_two ℓ, Subgroup.coe_mul]
    simp only [commutatorElement_def]
    group
  rw [hid, hc, hsq]

theorem mem_CHbar_of_odd_orderOf (S : Setting z E F) {a : G} (haQ : a ∈ Q z)
    {Y : Subgroup (Hbar z)}
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S haQ) = aVec S haQ)
    (hZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u) {y : Hbar z} (hy : y ∈ Y)
    (hodd : Odd (orderOf y)) : y ∈ CHbar S a := by
  obtain ⟨k, hk⟩ := hodd
  have hy' : y ^ (k + 1) ∈ Y := Y.pow_mem hy _
  have h := sq_mem_CHbar_of_fix S haQ hfix hZ hy'
  have hpow : (y ^ (k + 1)) ^ 2 = y := by
    rw [← pow_mul]
    have : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    calc y ^ ((k + 1) * 2) = y ^ (2 * k + 1) * y := by rw [← pow_succ]; ring_nf
      _ = y := by rw [this, one_mul]
  rwa [hpow] at h

theorem conj_mem_Rbar_of_mem_CHbar (S : Setting z E F) (a : G) {y r : Hbar z}
    (hy : y ∈ CHbar S a) (hr : r ∈ Rbar S a) : y * r * y⁻¹ ∈ Rbar S a := by
  obtain ⟨c, hcC, rfl⟩ := (mem_CHbar_iff S a y).mp hy
  rw [← map_R0_eq_Rbar S a] at hr ⊢
  obtain ⟨r0, hr0, rfl⟩ := Subgroup.mem_map.mp hr
  refine Subgroup.mem_map.mpr ⟨c * r0 * c⁻¹, ?_, ?_⟩
  · obtain ⟨hr0Z, hr0H⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hr0)
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact conj_mem_centerIn_QaOf S hcC hr0Z
    · have := (H z).mul_mem ((H z).mul_mem c.2 hr0H) ((H z).inv_mem c.2)
      exact this
  · simp [QuotientGroup.mk'_apply]

theorem commute_of_mem_CHbar_of_card_Rbar_eq_two (S : Setting z E F) (a : G)
    (hR : Nat.card ↥(Rbar S a) = 2) {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    {y : Hbar z} (hy : y ∈ CHbar S a) : y * α = α * y := by
  have hmem := conj_mem_Rbar_of_mem_CHbar S a hy hα
  have hne : y * α * y⁻¹ ≠ 1 := by
    intro h
    apply hα1
    have := congrArg (fun t => y⁻¹ * t * y) h
    simpa [mul_assoc] using this
  have hsub : ({1, α, y * α * y⁻¹} : Set (Hbar z)) ⊆ (Rbar S a : Set (Hbar z)) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact one_mem _
    · exact hα
    · exact hmem
  by_contra hne'
  have hneq : y * α * y⁻¹ ≠ α := by
    intro h
    apply hne'
    have := congrArg (fun t => t * y) h
    simpa [mul_assoc] using this
  have h3 : ({1, α, y * α * y⁻¹} : Set (Hbar z)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, α, y * α * y⁻¹, hα1.symm, hne.symm, hneq.symm, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at hle
  have hle' : 3 ≤ Nat.card ↥(Rbar S a) := hle
  omega

end CFSG.RankThree.GF2n.Stroth78
