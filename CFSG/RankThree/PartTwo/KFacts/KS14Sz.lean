module

public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.KFacts.KS14SzSpor

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open TauCeti CFSG.Blueprint CFSG.Assembly

theorem three_dvd_card_alternatingGroup {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have h3 : (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  have ho : orderOf (⟨_, h3.mem_alternatingGroup⟩ : alternatingGroup (Fin n)) = 3 := by
    rw [Subgroup.orderOf_mk, h3.orderOf]
  rw [← ho]
  exact orderOf_dvd_natCard _

theorem suzukiModel_of_inCatalog_of_not_three_dvd (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : InCatalog S)
    (h3 : ¬ 3 ∣ Nat.card S) : ∃ f : ℕ, SuzukiModel S 2 f := by
  obtain ⟨i, ⟨e⟩⟩ := hcat
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | d | s
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exfalso
    refine h3 ?_
    rw [Nat.card_congr e.toEquiv]
    exact three_dvd_card_alternatingGroup (by omega)
  · rcases three_dvd_card_or_suzukiModel_of_lie d e with h | h
    · exact absurd h h3
    · exact h
  · exact absurd (sporThreeDvd s S hnab ⟨e⟩) h3

theorem suzukiModel_of_isKGroup_section {X : Type} [Group X] [Finite X] (hK : CFSG.IsKGroup X)
    (h3 : ¬ 3 ∣ Nat.card X) (H : Subgroup X) (N : Subgroup H) [N.Normal]
    [IsSimpleGroup (H ⧸ N)] (hnab : ∃ a b : H ⧸ N, a * b ≠ b * a) :
    ∃ f : ℕ, SuzukiModel (H ⧸ N) 2 f := by
  refine suzukiModel_of_inCatalog_of_not_three_dvd _ hnab (hK H N inferInstance) fun h => h3 ?_
  have h1 : Nat.card (H ⧸ N) ∣ Nat.card H := Subgroup.card_quotient_dvd_card N
  exact h.trans (h1.trans (Subgroup.card_subgroup_dvd_card H))

end CFSG.RankThree.PartTwo.KFacts.KS14
