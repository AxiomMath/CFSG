module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Defs
import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.exists_isSylowOf_ge (h : Hyp1921 G A M N L) :
    ∃ Q : Subgroup G, IsSylowOf 3 Q N ∧ A ≤ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ :=
    ((isE27_of_mem_partTwoE h.mem_partTwoE).isPGroup.comap_subtype (K := N)).exists_le_sylow
  refine ⟨(S : Subgroup N).map N.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, h.mem_scriptM_N.2 hx⟩, hS hx, rfl⟩

theorem Hyp1921.isSylowOf_inf_Q_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) :
    IsSylowOf 3 (Q ⊓ L) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hQ.inf_of_le_normalizer (le_of_mem_oTwoComponentsIn h.mem_oTwoComponentsIn) hNL

theorem Hyp1921.card_inf_Q_of (h : Hyp1921 G A M N L)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) :
    Nat.card (Q ⊓ L : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient_iso
  rw [(h.isSylowOf_inf_Q_of hNL hQ).card_eq, Sec20.factorization_three_of_nonempty_quotient e]
  all_goals norm_num

theorem Hyp1921.inf_pCoreOf_eq_bot_Q (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) : (Q ⊓ L : Subgroup G) ⊓ CFSG.Open.pCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : IsPGroup 3 (Q ⊓ L : Subgroup G) := hQ.isPGroup.to_inf_left
  have h2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  exact Subgroup.card_eq_one.mp (Sec20.card_inf_eq_one_of_isPGroup h3 h2)

end CFSG.RankThree.PartTwo.Late
