
module

public import CFSG.Sporadic.Fi22.InvFixBase

public import CFSG.Sporadic.Fi22.Nfp
public import CFSG.Sporadic.Fi22.InvCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

theorem inv_parts : stabChecks orb = true ∧
    (∀ w ∈ fixWords, (∀ k ∈ w.1, k < 3510) ∧
      fixExact (wordTab orb (genTables orb (-2)) w.1) w.2 = true) ∧
    ∀ k < (tabS 0).size, ∀ B ∈ tabS 1, fixLeaf (tabS 0)[k]! B = true := by
  have h : invChecks orb 3 = true := inv_certificate
  unfold invChecks attainChecks at h
  simp only [Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, fun k hk => Array.all_eq_true'.1 (parAll_eq_true h.2 k hk)⟩

theorem card_fixed_of_mem_slvl
    {g : J} (hg : g ∈ slvl 0) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter fun i : Fin 3510 => g • i = i).card ∈ ({54, 182, 694} : Set ℕ) := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  subst hh''
  rw [mul_one] at hg2 hg1 ⊢
  have hmem : (tabS 1)[k1]! ∈ tabS 1 := by
    rw [getElem!_pos _ k1 (by rw [tabS_size]; exact hk1)]; exact Array.getElem_mem _
  have hR := Rep.compT (rep_tabS (by rw [sylBase_size]; norm_num) hk0)
    (rep_tabS (by rw [sylBase_size]; norm_num) hk1)
  refine fixLeaf_spec (fun i hi => ?_)
    (inv_parts.2.2 k0 (by rw [tabS_size]; exact hk0) _ hmem) hg2 hg1
  rw [← hR i hi]
  unfold compT
  rw [ap_ofFn _ hi]
  rfl

theorem card_fixed_involution
    {g : J} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter fun i : Fin 3510 => g • i = i).card ∈ ({54, 182, 694} : Set ℕ) := by
  obtain ⟨c, hc⟩ := exists_conj_mem_slvl (orderOf_eq_prime hg2 hg1)
  rw [← card_fixed_conj c g]
  refine card_fixed_of_mem_slvl hc ?_ ?_
  · rw [conj_pow, hg2, mul_one, mul_inv_cancel]
  · rwa [Ne, conj_eq_one_iff]

theorem exists_card_fixed
    {n : ℕ} (hn : n ∈ ({54, 182, 694} : Set ℕ)) :
    ∃ g : J, g ^ 2 = 1 ∧ g ≠ 1 ∧ (Finset.univ.filter fun i : Fin 3510 => g • i = i).card = n := by
  have key : ∀ w ∈ fixWords, ∃ g : J, g ^ 2 = 1 ∧ g ≠ 1 ∧
      (Finset.univ.filter fun i : Fin 3510 => g • i = i).card = w.2 := fun w hw =>
    ⟨_, fixExact_spec (rep_wordTab w.1 (inv_parts.2.1 w hw).1) (inv_parts.2.1 w hw).2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact key ([0, 8, 31], 54) (by simp [fixWords])
  · exact key ([0, 8], 182) (by simp [fixWords])
  · exact key ([0], 694) (by simp [fixWords])

theorem card_fixed_involution_eq :
    {n | ∃ g : J, g ^ 2 = 1 ∧ g ≠ 1 ∧
      (Finset.univ.filter fun i : Fin 3510 => g • i = i).card = n} = {54, 182, 694} := by
  ext n
  constructor
  · rintro ⟨g, hg2, hg1, rfl⟩
    exact card_fixed_involution hg2 hg1
  · exact exists_card_fixed

theorem card_fixed_involution_D :
    ∀ g : J, g ^ 2 = 1 → g ≠ 1 →
    Nat.card {x : D // g * (x : J) * g⁻¹ = x} ∈ ({54, 182, 694} : Set ℕ) := by
  intro g hg2 hg1
  have e : {x : D // g * (x : J) * g⁻¹ = x} ≃ {i : Fin 3510 // g • i = i} :=
    (Equiv.subtypeEquiv ptD fun i => by rw [ptD_val, smul_eq_iff]).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_fixed_involution hg2 hg1

end CFSG.Sporadic.Fi22
