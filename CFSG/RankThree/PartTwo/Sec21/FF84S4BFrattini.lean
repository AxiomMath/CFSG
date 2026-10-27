module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Sylow
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

private theorem not_three_dvd_card_of_isPGroup_two' {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk]
  intro h
  have h3 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem B_frattini_B {S B : Subgroup G} (hS : IsPGroup 2 S) (hB : IsPGroup 3 B) (hBS : B ≤ Nor S)
    (hSN : S ⊓ Nor B = S ⊓ CenS B) :
    Nor (S ⊔ B) ⊓ Nor S = (S ⊔ B) ⊓ Nor S ⊔ Nor B ⊓ Nor S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLS : S ⊔ B ≤ Nor S := sup_le (fun x hx => Subgroup.le_normalizer hx) hBS
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (S ⊔ B) := by
    rw [sup_comm]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Syl.isSylowOf_sup hB
      (not_three_dvd_card_of_isPGroup_two' hS) hBS
  have hLM : S ⊔ B ≤ Nor (S ⊔ B) ⊓ Nor S := le_inf Subgroup.le_normalizer hLS
  have hFr := CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf
    (H := Nor (S ⊔ B) ⊓ Nor S) (L := S ⊔ B) (P := B) hLM inf_le_left hsyl
  have hNB : Nor B ⊓ Nor S ≤ Nor (S ⊔ B) ⊓ Nor S := fun x hx =>
    Subgroup.mem_inf.2 ⟨Subgroup.inf_normalizer_le_normalizer_sup S B
      (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩),
      (Subgroup.mem_inf.1 hx).2⟩
  have hRHS : (S ⊔ B) ⊓ Nor S ⊔ Nor B ⊓ Nor S = S ⊔ B ⊔ Nor B ⊓ Nor S := by
    rw [inf_eq_left.2 hLS]
  rw [hRHS]
  refine le_antisymm (hFr.le.trans (sup_le_sup_left ?_ _))
    (sup_le hLM hNB)
  exact le_inf inf_le_right ((inf_le_left).trans inf_le_right)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
