module

public import CFSG.Quasithin.Background.RonanH143E
public import CFSG.Quasithin.Background.RonanH143Syl

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

theorem isElemAbelian_of_le {A B : Subgroup P24} (h : A ≤ B) (hB : IsElemAbelian 2 B) :
    IsElemAbelian 2 A :=
  ⟨⟨⟨fun a b => by
      have h1 := hB.1.is_comm.comm (⟨a, h a.2⟩ : B) ⟨b, h b.2⟩
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      simpa using h2⟩⟩, fun x hx => hB.2 x (h hx)⟩

theorem isElemAbelian_NQ2 : IsElemAbelian 2 NQ2 := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    apply Subtype.ext
    show (a : P24) * b = b * a
    rw [hs, ht, nq2Perm_mul, nq2Perm_mul]
    congr 1
    simp only [xor32, Nat.xor_comm]
  · obtain ⟨t, rfl⟩ := hx
    rw [pow_two, nq2Perm_sq]

theorem isE2k_NQ2 : IsE2k 5 NQ2 := ⟨isElemAbelian_NQ2, by rw [card_NQ2]; norm_num⟩

theorem no_centralizes_fixO : ∀ (t : Fin 16) (j : Fin 8), ∃ s : Fin 16,
    koPerm t * dPerm j * ePerm * koPerm s ≠ koPerm s * (koPerm t * dPerm j * ePerm) := by
  decide +kernel

theorem centralizes_NQ_mem_NQ2 : ∀ (t : Fin 16) (j : Fin 8),
    (∀ u : Fin 16, koPerm t * dPerm j * ePerm * nqPerm u = nqPerm u * (koPerm t * dPerm j * ePerm)) →
    (koPerm t * dPerm j * ePerm) * (koPerm t * dPerm j * ePerm) = 1 →
    ∃ v : Fin 32, koPerm t * dPerm j * ePerm = nq2Perm v := by
  decide +kernel

theorem eq_NQ2_of_isE2k_five (A : Subgroup P24) (hA : A ≤ P2) (hE : IsE2k 5 A) : A = NQ2 := by
  have hnot : ¬ A ≤ PO := fun h => not_isE2k_five_PO A h hE
  obtain ⟨x, hxA, hxPO⟩ := Set.not_subset.1 hnot
  obtain ⟨y, hy, hxy⟩ := hA hxA
  have hx' : x = y * ePerm := by
    rcases hxy with h | h
    · exact absurd (h ▸ hy) hxPO
    · exact h
  have hrel : PO.relIndex A ≤ 2 := by
    have h2 : PO.relIndex P2 = 2 := index_PO_P2_sylw
    rw [← h2]
    exact Subgroup.relIndex_le_of_le_right hA (by rw [h2]; norm_num)
  have hidx : (PO ⊓ A).relIndex A = PO.relIndex A := Subgroup.inf_relIndex_right PO A
  have hidx1 : (A ⊓ PO).relIndex A ≠ 1 := by
    intro h1
    rw [inf_comm, hidx] at h1
    apply hnot
    rw [Subgroup.relIndex_eq_one] at h1
    exact h1
  have hidx_pos : (A ⊓ PO).relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx2 : (A ⊓ PO).relIndex A = 2 := by
    have : (A ⊓ PO).relIndex A ≤ 2 := by
      rw [inf_comm, hidx]
      exact hrel
    omega
  have hA₀card : Nat.card ↥(A ⊓ PO) = 16 := by
    have h := relIndex_mul_card_sylw (inf_le_left : A ⊓ PO ≤ A)
    rw [hidx2, hE.2] at h
    have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
    omega
  have hE4 : IsE2k 4 (A ⊓ PO) := ⟨isElemAbelian_of_le inf_le_left hE.1, by rw [hA₀card]; norm_num⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := hE.1.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact hE.1.2 a ha
  obtain ⟨t, j, rfl⟩ := hy
  have hxe : x = koPerm t * dPerm j * ePerm := hx'
  have hNQ2 : (A ⊓ PO = NQ) → A = NQ2 := by
    intro hNQ
    have hxNQ2 : x ∈ NQ2 := by
      obtain ⟨v, hv⟩ := centralizes_NQ_mem_NQ2 t j (fun u => by
        rw [← hxe]
        exact (hcomm x hxA _ (by
          have : nqPerm u ∈ A ⊓ PO := by rw [hNQ]; exact ⟨u, rfl⟩
          exact this.1)))
        (by rw [← hxe]; exact hsq x hxA)
      rw [hxe]
      exact ⟨v, hv⟩
    have hle : A ≤ NQ2 := by
      intro a haA
      by_cases haPO : a ∈ PO
      · have : a ∈ A ⊓ PO := ⟨haA, haPO⟩
        rw [hNQ] at this
        exact NQ_le_NQ2 this
      · obtain ⟨y', hy', hay'⟩ := hA haA
        have ha' : a = y' * ePerm := by
          rcases hay' with h | h
          · exact absurd (h ▸ hy') haPO
          · exact h
        have hxa : x⁻¹ * a ∈ A ⊓ PO := by
          refine ⟨A.mul_mem (A.inv_mem hxA) haA, ?_⟩
          have : x⁻¹ * a = ePerm * (((koPerm t * dPerm j))⁻¹ * y') * ePerm⁻¹ := by
            rw [hxe, ha', mul_inv_rev, ePerm_inv]
            group
          rw [this]
          exact ePerm_conj_mem_PO (PO.mul_mem (PO.inv_mem ⟨t, j, rfl⟩) hy')
        rw [hNQ] at hxa
        have : a = x * (x⁻¹ * a) := by group
        rw [this]
        exact NQ2.mul_mem hxNQ2 (NQ_le_NQ2 hxa)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hE.2, card_NQ2]; norm_num)
  rcases eq_NQ_or_fixO_of_isE2k_four (A ⊓ PO) inf_le_right hE4 with hNQ | hKO
  · exact hNQ2 hNQ
  · exfalso
    obtain ⟨s, hs⟩ := no_centralizes_fixO t j
    apply hs
    rw [← hxe]
    have hsA : koPerm s ∈ A := by
      have : koPerm s ∈ A ⊓ PO := by rw [hKO]; exact (mem_fixO_iff _).2 ⟨s, rfl⟩
      exact this.1
    exact hcomm x hxA _ hsA

theorem isE2k_five_P2_iff (A : Subgroup P24) : (A ≤ P2 ∧ IsE2k 5 A) ↔ A = NQ2 := by
  constructor
  · rintro ⟨hA, hE⟩
    exact eq_NQ2_of_isE2k_five A hA hE
  · rintro rfl
    exact ⟨NQ2_le_P2, isE2k_NQ2⟩

end CFSG.Quasithin.RonanH143
