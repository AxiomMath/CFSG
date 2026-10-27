module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223BlkEpi
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem alt_block_facts {X : Subgroup G} (hX : IsShort2 X) {n : ℕ} (hn : n = 5 ∨ n = 7)
    (h : IsAltType X n) :
    ⁅X, X⁆ = X ∧ GenByOrderThree X ∧ ¬ Group.IsSolvable ↥X ∧ quasithinV2 X ≠ ⊥ ∧
      3 ∣ Nat.card X := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  have h5 : 5 ≤ Nat.card (Fin n) := by rcases hn with rfl | rfl <;> simp
  have : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  have : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top h5⟩
  have h3A : 3 ∣ Nat.card (alternatingGroup (Fin n)) := by
    rcases hn with rfl | rfl <;> (rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
  have h3X : 3 ∣ Nat.card X := h3A.trans (Subgroup.card_dvd_of_surjective hαs)
  have hperf : ⁅X, X⁆ = X := commutator_eq_self_of_epi hX.1 hαs hαk
  have hgen : GenByOrderThree X := genByOrderThree_of_epi_simple hX.1 hαs hαk h3X
  have hns : ¬ Group.IsSolvable ↥X := by
    have hP : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hperf
    have hle : 3 ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos h3X
    have : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    exact Group.IsPerfect.not_isSolvable ↥X
  have hU : blockU X ≤ z2Of X := fun u hu =>
    Subgroup.subset_closure ⟨hX.2.2.1.1 hu, hX.2.2.1.2 u hu⟩
  have hbU : blockU X ≠ ⊥ := fun h0 => by
    have hlt : blockZ X < blockU X := hX.2.2.2.2.1
    rw [h0] at hlt
    exact not_lt_bot hlt
  have hV2 : quasithinV2 X ≠ ⊥ := by
    intro h0
    rw [quasithinV2_eq_commutator] at h0
    have hle : ⁅blockU X, X⁆ ≤ ⁅z2Of X, X⁆ := Subgroup.commutator_mono hU le_rfl
    apply hbU
    rw [← C1.commutator_blockU hX]
    exact le_bot_iff.1 (h0 ▸ hle)
  exact ⟨hperf, hgen, hns, hV2, h3X⟩

end CFSG.Quasithin.S15223
