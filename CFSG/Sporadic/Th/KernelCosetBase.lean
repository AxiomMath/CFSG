
module

public import CFSG.Sporadic.Th.SimpleBase
public import CFSG.Sporadic.Th.KernelInputsBase

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge TauCeti Pointwise MulAction

abbrev Om : Type := P ⧸ K

noncomputable abbrev pt (v : P) : Om := (v : Om)

theorem smul_pt (g v : P) : g • pt v = pt (g * v) := rfl

theorem pt_eq_pt {v w : P} : pt v = pt w ↔ v⁻¹ * w ∈ K := QuotientGroup.eq

theorem mem_stabK {v k : P} : k ∈ stabK v ↔ k ∈ K ∧ k • pt v = pt v := by
  rw [stabK, Subgroup.mem_inf, smul_pt, pt_eq_pt]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨j, hj, rfl⟩
    have e : (MulAut.conj v j * v)⁻¹ * v = j⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    simp only [MulEquiv.coe_toMonoidHom] at e ⊢
    rw [e]
    exact K.inv_mem hj
  · intro hk
    refine ⟨v⁻¹ * k * v, ?_, by simp [MulAut.conj_apply]; group⟩
    have := K.inv_mem hk
    rwa [show ((k * v)⁻¹ * v)⁻¹ = v⁻¹ * k * v by group] at this

noncomputable abbrev orb (v : P) : Set Om := MulAction.orbit K (pt v)

theorem map_stabilizer (v : P) : (MulAction.stabilizer K (pt v)).map K.subtype = stabK v := by
  ext k
  rw [mem_stabK, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hK, hk⟩
    exact ⟨⟨k, hK⟩, hk, rfl⟩

theorem card_stabilizer (v : P) : Nat.card (MulAction.stabilizer K (pt v)) = Nat.card (stabK v) := by
  rw [← map_stabilizer, Subgroup.card_map_of_injective K.subtype_injective]

theorem card_orb_mul (v : P) : (orb v).ncard * Nat.card (stabK v) = Nat.card K := by
  rw [← card_stabilizer, ← MulAction.index_stabilizer, mul_comm]
  exact Subgroup.card_mul_index _

theorem subSizes_mul_mD : ∀ D : Fin 11, D ≠ 0 → subSizes D * mD D = 634023936 := by
  decide

theorem sum_subSizes : ∑ D, subSizes D = 143127000 := by
  simp [Fin.sum_univ_succ, subSizes]

theorem mD_pos (D : Fin 11) : 0 < mD D := by
  fin_cases D <;> decide

section Orbits

variable {v : Fin 11 → P} (hv0 : v 0 = 1)
  (hcov : ∀ g : P, ∃ D, ∃ k ∈ K, ∃ k' ∈ K, g = k * v D * k')
  (hstab : ∀ D, mD D ≤ Nat.card (stabK (v D))) (hK : Nat.card K ≤ 634023936)

theorem orb_one : orb 1 = {pt 1} := by
  ext p
  constructor
  · rintro ⟨k, rfl⟩
    change (k : P) • pt 1 = pt 1
    rw [smul_pt, pt_eq_pt]
    simp
  · rintro rfl
    exact MulAction.mem_orbit_self _

include hcov in
theorem mem_orb_cover (p : Om) : ∃ D, p ∈ orb (v D) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨D, k, hk, k', hk', rfl⟩ := hcov g
  refine ⟨D, ⟨k, hk⟩, ?_⟩
  change k • pt (v D) = pt (k * v D * k')
  rw [smul_pt, pt_eq_pt]
  simpa [mul_assoc] using hk'

include hv0 hstab hK in
theorem ncard_orb_le (D : Fin 11) : (orb (v D)).ncard ≤ subSizes D := by
  by_cases hD : D = 0
  · subst hD
    rw [hv0, orb_one, Set.ncard_singleton]
    rfl
  have h1 := card_orb_mul (v D)
  have h2 : (orb (v D)).ncard * mD D ≤ subSizes D * mD D := by
    rw [subSizes_mul_mD D hD]
    calc (orb (v D)).ncard * mD D ≤ (orb (v D)).ncard * Nat.card (stabK (v D)) :=
          Nat.mul_le_mul_left _ (hstab D)
      _ = Nat.card K := h1
      _ ≤ 634023936 := hK
  exact Nat.le_of_mul_le_mul_right h2 (mD_pos D)

end Orbits

noncomputable def lab (v : Fin 11 → P) (hcov : ∀ p : Om, ∃ D, p ∈ orb (v D)) (p : Om) : Fin 11 :=
  Classical.choose (hcov p)

theorem mem_orb_lab (v : Fin 11 → P) (hcov : ∀ p : Om, ∃ D, p ∈ orb (v D)) (p : Om) :
    p ∈ orb (v (lab v hcov p)) :=
  Classical.choose_spec (hcov p)

theorem orbitData [Finite P] (hP : Nat.card P = thOrder) {v : Fin 11 → P} (hv0 : v 0 = 1)
    (hcov : ∀ g : P, ∃ D, ∃ k ∈ K, ∃ k' ∈ K, g = k * v D * k')
    (hstab : ∀ D, mD D ≤ Nat.card (stabK (v D))) (hK : Nat.card K ≤ 634023936) :
    Nat.card Om = 143127000 ∧ Nat.card K = 634023936 ∧
      ∃ hc : ∀ p : Om, ∃ D, p ∈ orb (v D),
        (∀ D, (orb (v D)).ncard = subSizes D) ∧ ∀ p D, p ∈ orb (v D) ↔ lab v hc p = D := by
  classical
  have hc : ∀ p : Om, ∃ D, p ∈ orb (v D) := mem_orb_cover hcov
  have : Fintype Om := Fintype.ofFinite Om
  let C : Fin 11 → Finset Om := fun D => Finset.univ.filter fun p => lab v hc p = D
  have hCsub : ∀ D, C D ⊆ (orb (v D)).toFinset := by
    intro D p hp
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Set.mem_toFinset, ← hp]
    exact mem_orb_lab v hc p
  have hCle : ∀ D, (C D).card ≤ subSizes D := fun D =>
    ((Finset.card_le_card (hCsub D)).trans (by rw [← Set.ncard_eq_toFinset_card'])).trans
      (ncard_orb_le hv0 hstab hK D)
  have hsumC : ∑ D, (C D).card = Nat.card Om := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := lab v hc) (fun _ _ => Finset.mem_univ _)).symm
  have hOm_le : Nat.card Om ≤ 143127000 := by
    rw [← hsumC, ← sum_subSizes]
    exact Finset.sum_le_sum fun D _ => hCle D
  have hmul : Nat.card Om * Nat.card K = 143127000 * 634023936 := by
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup, hP]
    rfl
  have hOm : Nat.card Om = 143127000 := by
    refine le_antisymm hOm_le (Nat.le_of_not_lt fun hlt => ?_)
    have := Nat.mul_lt_mul_of_lt_of_le hlt hK (by norm_num)
    omega
  have hKc : Nat.card K = 634023936 := by
    rw [hOm] at hmul
    omega
  have hCeq : ∀ D, (C D).card = subSizes D := by
    have hs : ∑ D, (C D).card = ∑ D, subSizes D := by rw [hsumC, hOm, sum_subSizes]
    exact fun D => (Finset.sum_eq_sum_iff_of_le fun D _ => hCle D).1 hs D (Finset.mem_univ _)
  have hO : ∀ D, (orb (v D)).toFinset = C D := by
    intro D
    refine (Finset.eq_of_subset_of_card_le (hCsub D) ?_).symm
    rw [hCeq, ← Set.ncard_eq_toFinset_card']
    exact ncard_orb_le hv0 hstab hK D
  refine ⟨hOm, hKc, hc, fun D => ?_, fun p D => ?_⟩
  · rw [Set.ncard_eq_toFinset_card', hO, hCeq]
  · have := congrArg (p ∈ ·) (hO D)
    simp only [Set.mem_toFinset, C, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact Iff.of_eq this

end CFSG.Sporadic.Th.Kernel
