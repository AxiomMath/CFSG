module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Open.StatedAPI
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem qTwoS34_su_eq_statedSU (hF : Nat.card K = (2 ^ 1) ^ 2) (n : ℕ) :
    Su K 2 1 n = ↥(CFSG.Open.StatedSU n (2 ^ 1) K) := by
  dsimp only [Su]
  rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (F := K) (p := 2) (f := 1) hF n]

theorem qTwoS34_card_Su_two (hK : Nat.card K = 4) : Nat.card (Su K 2 1 2) = 6 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  rw [qTwoS34_su_eq_statedSU (K := K) hF 2]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 2 (2 ^ 1) K) : ℤ) = 6 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 2) (by norm_num)]
    decide
  exact_mod_cast hval

theorem qTwoS34_card_Su_three (hK : Nat.card K = 4) : Nat.card (Su K 2 1 3) = 216 := by
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hdata := CFSG.RankThree.PartOne.KFU.unitaryFieldData_two (K := K) (f := 1) hF (by norm_num)
  rw [qTwoS34_su_eq_statedSU (K := K) hF 3]
  have hval : (Nat.card ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) : ℤ) = 216 := by
    rw [CFSG.RankThree.PartOne.KFU.card_statedSU_eq (K := K) (f := 1) hdata (n := 3) (by norm_num)]
    decide
  exact_mod_cast hval

theorem qTwoS34_coordBlockSU_inf {N : ℕ} (A B : Finset (Fin N)) :
    coordBlockSU K 2 1 A ⊓ coordBlockSU K 2 1 B = coordBlockSU K 2 1 (A ∩ B) := by
  ext g
  simp only [Subgroup.mem_inf, mem_coordBlockSU_iff]
  constructor
  · rintro ⟨hA, hB⟩ i j hij
    rcases hij with hi | hj
    · by_cases hiA : i ∈ A
      · exact hB i j (Or.inl fun h => hi (Finset.mem_inter.mpr ⟨hiA, h⟩))
      · exact hA i j (Or.inl hiA)
    · by_cases hjA : j ∈ A
      · exact hB i j (Or.inr fun h => hj (Finset.mem_inter.mpr ⟨hjA, h⟩))
      · exact hA i j (Or.inr hjA)
  · intro h
    refine ⟨?_, ?_⟩ <;> intro i j hij
    · exact h i j (hij.elim (fun hi => Or.inl fun hmem => hi (Finset.mem_inter.mp hmem).1)
        (fun hj => Or.inr fun hmem => hj (Finset.mem_inter.mp hmem).1))
    · exact h i j (hij.elim (fun hi => Or.inl fun hmem => hi (Finset.mem_inter.mp hmem).2)
        (fun hj => Or.inr fun hmem => hj (Finset.mem_inter.mp hmem).2))

theorem qTwoS34_coordBlockSU_mono {n : ℕ} {J J' : Finset (Fin n)} (hJJ' : J ⊆ J') :
    coordBlockSU K 2 1 J ≤ coordBlockSU K 2 1 J' := by
  intro g hg
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  exact hg i j (by tauto)

end CFSG.StandardType.QTwo

end
