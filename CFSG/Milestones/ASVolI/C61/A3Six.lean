module

public import CFSG.Milestones.ASVolI.C61.A3Star
public import CFSG.Milestones.ASVolI.C61.A3Suzuki

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

theorem burnsideC56_a3_six {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (hcs : burnsideC56_CS G T M H S L) (h3 : IsAltType L 3) (hj : conjJoin S L = L) :
    C61Six T H S L := by
  obtain ⟨c, hl⟩ := burnsideC56_a3Local hcs h3 hj
  unfold C61Six
  by_cases hD : H ⊓ Subgroup.centralizer (L : Set G) = ⊥
  ·
    refine Or.inr (Or.inl ⟨h3, hj, burnsideC56_a3_perm_four hcs hj hl hD, ?_⟩)
    have hUne : blockU L ≠ ⊥ := by
      intro h
      have := hl.card_U
      rw [h, Subgroup.card_bot] at this
      omega
    refine burnsideC56_suzuki hcs.T_two (hl.U_le_S.trans hcs.le_T) hl.card_U hl.U_exp ?_
    intro t ht
    have htN : t ∈ normalizer (blockU L : Set G) :=
      A3Dich.mem_normalizer_of_forall_comm fun u hu =>
        (Subgroup.mem_centralizer_iff.mp ht.2 u hu).symm
    have htS : t ∈ S := by
      have e := hcs.l244 (blockU L) hUne hl.U_le_S hl.H_normalizes_U
      have : t ∈ T ⊓ normalizer (blockU L : Set G) := ⟨ht.1, htN⟩
      rw [e] at this
      exact this
    have : t ∈ S ⊓ centralizer (blockU L : Set G) := ⟨htS, ht.2⟩
    rw [hl.S_cent_U, hD, sup_bot_eq] at this
    exact this
  ·
    have hD' : S ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
      intro h
      apply hD
      rw [eq_bot_iff, ← h]
      intro d hd
      exact ⟨hl.D_le_S hd, hd.2⟩
    obtain ⟨hrel, hJ⟩ := C56.burnsideC56_a3_index_two hcs hj h3 hD'
    exact Or.inl ⟨hrel, hJ, fun _ _ => burnsideC56_a3_perm_four_prod hcs h3 hj hl hD⟩

end CFSG.QuasithinUnique.burnsideC56_P
