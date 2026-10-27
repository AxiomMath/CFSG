
module

public import Certificates.Data.CFSGNative.Fi22.Inv
public import CFSG.Sporadic.Fi22.Classes

@[expose] public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_filter_fin_eq_countP (p : ℕ → Bool) :
    (Finset.univ.filter fun v : Fin 3510 => p v.val = true).card =
      (List.range 3510).countP p := by
  have h : (Finset.univ.filter fun v : Fin 3510 => p v.val = true).map Fin.valEmbedding =
      (Finset.range 3510).filter fun i => p i = true := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, hv⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter, Finset.range, Multiset.range]

theorem card_fixed_eq_countP (g : J) :
    (Finset.univ.filter fun i : Fin 3510 => g • i = i).card =
      (List.range 3510).countP fun i => idx 3510 g i == i := by
  rw [← card_filter_fin_eq_countP]
  refine congrArg Finset.card (Finset.filter_congr fun v _ => ?_)
  rw [beq_iff_eq, ← smul_val_eq_idx, Fin.val_inj]

theorem card_fixed_conj (c g : J) :
    (Finset.univ.filter fun i : Fin 3510 => (c * g * c⁻¹) • i = i).card =
      (Finset.univ.filter fun i : Fin 3510 => g • i = i).card := by
  refine Finset.card_equiv (MulAction.toPerm c⁻¹) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.toPerm_apply]
  refine (smul_left_cancel_iff c⁻¹).symm.trans ?_
  rw [smul_smul, smul_smul, show c⁻¹ * (c * g * c⁻¹) = g * c⁻¹ by group]

theorem fixLeaf_spec
    {A B : Table} {g : J} (hAB : ∀ i < 3510, ap A (ap B i) = idx 3510 g i)
    (h : fixLeaf A B = true) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    (Finset.univ.filter fun i : Fin 3510 => g • i = i).card ∈ ({54, 182, 694} : Set ℕ) := by
  have hinv : allIn 0 3510 (fun i => ap A (ap B (ap A (ap B i))) == i) = true := by
    rw [allIn_eq_true]
    intro i _ hi
    rw [beq_iff_eq, hAB i hi, hAB _ (idx_lt g hi), ← idx_mul, ← pow_two, hg2, idx_one]
  have hid : allIn 0 3510 (fun i => ap A (ap B i) == i) = false := by
    rw [Bool.eq_false_iff]
    intro hall
    apply hg1
    apply eq_one_of_idx
    intro i hi
    have := allIn_eq_true.1 hall i (Nat.zero_le _) hi
    rwa [beq_iff_eq, hAB i hi] at this
  have hc : (List.range 3510).countP (fun i => ap A (ap B i) == i) =
      (Finset.univ.filter fun i : Fin 3510 => g • i = i).card := by
    rw [card_fixed_eq_countP]
    refine List.countP_congr fun i hi => ?_
    rw [hAB i (List.mem_range.1 hi)]
  unfold fixLeaf at h
  rw [hinv, hid, hc] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem fixExact_spec
    {P : Table} {g : J} (hP : Rep 3510 P g) {c : ℕ} (h : fixExact P c = true) :
    g ^ 2 = 1 ∧ g ≠ 1 ∧ (Finset.univ.filter fun i : Fin 3510 => g • i = i).card = c := by
  unfold fixExact at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨eq_one_of_idx (idx_sq_of_invoOK hP h1), fun e => ?_, ?_⟩
  · rw [idOK_of_eq_one hP e] at h2
    exact absurd h2 (by decide)
  · rw [card_fixed_eq_countP, ← h3]
    refine List.countP_congr fun i hi => ?_
    rw [hP i (List.mem_range.1 hi)]

end CFSG.Sporadic.Fi22
