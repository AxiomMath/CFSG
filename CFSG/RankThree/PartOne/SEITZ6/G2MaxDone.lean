module

public import CFSG.RankThree.PartOne.SEITZ6.G2Core
public import CFSG.RankThree.PartOne.SEITZ6.G2Odd

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZ3

theorem maxSL2SL2G2_of_top
    (hgold : CFSG.Goldschmidt.TopStatement) : MaxSL2SL2G2 := by
  intro K _ _ _ h4 N hN
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hn : 2 ≤ (m : ℕ) := by
    by_contra h
    push Not at h
    have : (m : ℕ) = 1 := by have := m.pos; omega
    rw [hK, this] at h4
    norm_num at h4
  set f : (adjointGroup .G2 K) →* (adjointGroup .G2 K) := (MulAut.conj (Wg K)).toMonoidHom
    with hf
  have hinj : Function.Injective f := (MulAut.conj (Wg K)).injective
  have hL : Lp K ≤ N.map f := Subgroup.map_mono hN
  rcases core_max hgold hn hK (N.map f) hL (fun R _ hRn hodd =>
    odd_core_trivial hn hK hL hRn hodd) with h | h
  · left
    exact Subgroup.map_injective hinj h
  · right
    refine Subgroup.map_injective hinj ?_
    rw [h, Subgroup.map_top_of_surjective f (MulEquiv.surjective _)]

end CFSG.RankThree.PartOne.SEITZ6
