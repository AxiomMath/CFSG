module

public import CFSG.LocalAnalysis.StandardType.GGPZCutsDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_rank_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (h : GGPZPrem p B Bs x L D J y K labJ labX X m z) : 2 ≤ labJ.rank := by
  obtain ⟨hH, -, -, -, -, -, hrow, hbr, hcard, -⟩ := h
  have hB := GGConfig.card_B_eq hH.1
  have hbeta : p ∈ LargeEvenBeta 4 G := hH.1.1.2.2.2.2.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := by
    unfold LargeEvenBeta at hbeta
    exact hbeta.2.2.2
  have hBBs : B ≤ Bs := hH.1.2.1.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
  rw [hB, hcard] at hle
  have hm4 : 4 ≤ m := by
    have h4' : LargeEvenTwoLocalRank p G ≤ m :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle
    omega
  obtain ⟨hrowTN, -⟩ := hrow
  rcases hbr with ⟨htag, hm⟩ | ⟨htag, hm⟩
  · rcases hrowTN with ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩
    · rw [hXe] at hm
      simp only at hm
      omega
    · rw [hXe] at hm
      simp only at hm
      omega
    · rw [hXe] at htag
      rcases htag with h | h <;> simp at h
    · rw [hXe] at htag
      rcases htag with h | h <;> simp at h
  · rcases hrowTN with ⟨-, -, -, hXe⟩ | ⟨-, -, -, hXe⟩ | ⟨hJe, -, -, -⟩ | ⟨hJe, -, -, -⟩
    · rw [hXe] at htag
      rcases htag with h | h <;> simp at h
    · rw [hXe] at htag
      rcases htag with h | h <;> simp at h
    · have : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
      omega
    · have : labJ.rank = 4 := congrArg LargeEvenLabel.rank hJe
      omega

end CFSG.StandardType

end
