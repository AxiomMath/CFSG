module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKHJ
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCase2
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCase3
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKJ
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem step138KStr_of
    (hspor : SporadicModels131) (h415 : Sec4.Item4_15) (h48 : Sec4.Item4_8)
    (hsetAt : Item13SetupAt) (h133 : Item133) (hENeD : Step138ENeD) (hNC : Step138NoCompF)
    (hKF : KF138TypeTwo) : Step138KStr := by
  intro G _ _ A c L E hH hPGL F hF
  obtain ⟨x, y, t, hfr⟩ := exists_frame138_t hH hF hPGL
  have hcΩ := zpowers_not_mem_omegaA hsetAt hH hfr.hdE hfr.hdL hfr.hdc
  have hdΩ := hENeD G A c L E hH hPGL
  obtain ⟨h, -, -, -, -, -, -, hST, -⟩ := hH
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  obtain ⟨X, hX⟩ := omegaA_nonempty h.toPartTwoStanding h.partTwoS_eq hXF.1 hXF.2
  obtain ⟨-, hX3, e, rfl, -⟩ := id hX
  obtain ⟨K, hK⟩ := hsetAt G h.toPartTwoStanding h.partTwoS_eq E hXF.1 hXF.2 e hX
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp hX).1
  have he3 : e ^ 3 = 1 := hfr.hE3 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hX3
    norm_num at hX3
  have heF := mem_of_mem_omegaA h48 hNC hKF hfr hX hK
  have hec : e ∉ Subgroup.zpowers c := fun hec =>
    hcΩ (zpowers_eq_of_mem he3 he1 hfr.hc3 hfr.hc1 hec ▸ hX)
  have heL : e ∉ L := fun heL => by
    have heEL : e ∈ Subgroup.zpowers ⁅x, y⁆ := hfr.hEL ▸ Subgroup.mem_inf.mpr ⟨heE, heL⟩
    apply hdΩ
    rw [hfr.hEL, ← zpowers_eq_of_mem he3 he1 hfr.hd3 hfr.hd1 heEL]
    exact hX
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := hX
      mem_lA := hK }
  rcases h133 G E e K hD hST with h1 | ⟨-, -, hΩ3, -⟩ | ⟨hirr, hWB, -, -, -, hΩ, hΩ9, ⟨φ⟩, -⟩ |
      hPGLK | hM12 | hHJ
  · exact (false_of_case1 hfr hcΩ hdΩ hX h1).elim
  · exact (false_of_case2 hfr hcΩ hdΩ hX heF hΩ3).elim
  · have hB9 : Nat.card (E ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) φ
    exact (false_of_case3 hfr hcΩ hdΩ hD heF hirr hWB hΩ hΩ9 hB9).elim
  · exact ⟨e, K, hX, hK, heF, hec, heL, Or.inl hPGLK⟩
  · exact ⟨e, K, hX, hK, heF, hec, heL, Or.inr hM12⟩
  · exact (false_of_hj hspor h415 h48 hfr hcΩ hdΩ hX hK heF hHJ).elim

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
