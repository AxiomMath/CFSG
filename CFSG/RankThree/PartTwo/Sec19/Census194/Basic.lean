module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Assembly.LowTwoRank

theorem card_pCoreOf_normalizer_sylow {Y : Type} [Group Y] [Finite Y] (T : Sylow 2 Y) :
    Nat.card (CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((T : Subgroup Y) : Set Y))) =
      Nat.card (T : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Y := Subgroup.normalizer ((T : Subgroup Y) : Set Y) with hN
  have hTN : (T : Subgroup Y) ≤ N := Subgroup.le_normalizer
  have hnorm : (((T : Subgroup Y)).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).mpr le_rfl
  have hT2 : IsPGroup 2 (((T : Subgroup Y)).subgroupOf N) := T.isPGroup'.comap_subtype
  have hle : (T : Subgroup Y) ≤ CFSG.Open.pCoreOf 2 N := by
    have h1 : ((T : Subgroup Y).subgroupOf N) ≤ CFSG.pCore 2 N := le_sSup ⟨hnorm, hT2⟩
    intro x hx
    exact ⟨⟨x, hTN hx⟩, h1 (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hC2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 N) :=
    (CFSG.pCore_isPGroup (p := 2) (G := N)).map N.subtype
  obtain ⟨Q, hQ⟩ := hC2.exists_le_sylow
  have hcardQ : Nat.card (Q : Subgroup Y) = Nat.card (T : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  exact le_antisymm (hcardQ ▸ Subgroup.card_le_of_le hQ) (Subgroup.card_le_of_le hle)

end CFSG.RankThree.PartTwo.Sec19
