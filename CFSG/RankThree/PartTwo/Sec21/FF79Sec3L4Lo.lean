module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4LoSyl
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4LoPsl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Open CFSG.Open.StatedAPI

theorem card_psl_dvd (K : Type) [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 2 K)) ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← card_statedSL_two]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((StatedScalars (Fin 2) K).subgroupOf
    (StatedSL 2 K))]
  exact Dvd.intro _ rfl

theorem aux_of_equiv {L : Type} [Group L] {K : Type} [Field K] [Finite K]
    (e : L ≃* StatedProj (StatedSL 2 K))
    (hg : ∃ g : StatedProj (StatedSL 2 K), orderOf g = 9)
    (h27 : ¬ 27 ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ g : L, orderOf g = 9 ∧ ¬ 27 ∣ Nat.card L := by
  obtain ⟨g, hg⟩ := hg
  refine ⟨e.symm g, (e.symm.orderOf_eq g).trans hg, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact fun hd => h27 (hd.trans (card_psl_dvd K))

theorem lnq_syl_cyclic9 (L : Type) [Group L] [Finite L]
    (h : IsLnq 2 2 6 (⊤ : Subgroup L) ∨ IsLnq 2 5 3 (⊤ : Subgroup L)) :
    ∀ S : Subgroup L, IsSylowOf 3 S ⊤ → IsCyclic S ∧ Nat.card S = 9 := by
  intro S hS
  have key : ∃ g : L, orderOf g = 9 ∧ ¬ 27 ∣ Nat.card L := by
    rcases h with h | h
    · obtain ⟨-, K, hKf, hKfin, hKc, ⟨e⟩⟩ := h
      have hK : Nat.card K = 64 := by rw [hKc]; norm_num
      obtain ⟨g, hg⟩ := exists_orderOf_nine_card64 hK
      exact aux_of_equiv (Subgroup.topEquiv.symm.trans e) ⟨g, hg⟩ (by rw [hK]; norm_num)
    · obtain ⟨-, K, hKf, hKfin, hKc, ⟨e⟩⟩ := h
      have hK : Nat.card K = 125 := by rw [hKc]; norm_num
      obtain ⟨g, hg⟩ := exists_orderOf_nine_card125 hK
      exact aux_of_equiv (Subgroup.topEquiv.symm.trans e) ⟨g, hg⟩ (by rw [hK]; norm_num)
  obtain ⟨g, hg, h27⟩ := key
  exact sylow3_cyclic_of_order9 g hg h27 S hS

end CFSG.RankThree.PartTwo.Sec21.FF79
