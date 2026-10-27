module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs14
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Five
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Act
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.UC1K49Struct
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem inf_le_normalizer_L {D : Data G} (h71 : F07.R71 D) (hsp5 : IsStronglyPEmbedded 5 D.M)
    {L D₃ Y H : Subgroup G} (hyp : PartTwo.Hyp919c D L D₃ Y H) (hA5 : IsAlt (Bar2 L) 5)
    (hLY : L ≤ Y) (hH2 : pCoreOf 2 H ≠ ⊥) : H ⊓ D.M ≤ normalizer (L : Set G) := by
  obtain ⟨hL, hD₃L, hD₃, hD₃U, hYM, hLeq, hnorm, hidx, hHtop, hYH, hHM⟩ := hyp
  have hinf : CFSG.Open.pRank 5 (H ⊓ D.M) ≤ 1 :=
    pRank_inf_le_one_of_pCoreOf_two_ne_bot h71 Nat.prime_five (by norm_num) hsp5 hH2 hHtop hHM
  have hZ : center (Bar2 L) = ⊥ := UC22.InS3.UC49.center_bar2_eq_bot hA5
  have h5 : 5 ∣ Nat.card (Bar2 L) := by
    rw [PartTwo.S19.card_bar2_of_isAlt_five hA5]
    norm_num
  exact inf_le_normalizer_of_pRank_le_one hL Nat.prime_five (by norm_num) hZ h5
    (hLY.trans hYH) hinf

theorem exists_sylow_weaklyClosed {D : Data G} (h71 : F07.R71 D)
    (hsp5 : IsStronglyPEmbedded 5 D.M) {L D₃ Y H : Subgroup G} (hyp : PartTwo.Hyp919c D L D₃ Y H)
    (hA5 : IsAlt (Bar2 L) 5) (hLY : L ≤ Y) (hH2 : pCoreOf 2 H ≠ ⊥) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P H ∧ D₃ ≤ P ∧ P ≤ D.M ∧
      (∀ h ∈ H, D₃.map (MulAut.conj h).toMonoidHom ≤ P →
        D₃.map (MulAut.conj h).toMonoidHom = D₃) ∧
      ∃ (Q : Type) (_ : Group Q) (φ : ↥P →* Q), IsCyclic Q ∧
        ∀ x : ↥P, (x : G) ∈ L → φ x = 1 → x = 1 := by
  have hHMnorm := inf_le_normalizer_L h71 hsp5 hyp hA5 hLY hH2
  obtain ⟨hL, hD₃L, hD₃, hD₃U, hYM, hLeq, hnorm, hidx, hHtop, hYH, hHM⟩ := hyp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD₃H : D₃ ≤ H := hD₃L.trans (hLY.trans hYH)
  have hD₃p : IsPGroup 3 ↥D₃ := IsPGroup.of_card (n := 1) (by rw [hD₃]; norm_num)
  obtain ⟨P, hP, hD₃P⟩ := UC6.exists_isSylowOf_ge hD₃H hD₃p
  have hPM : P ≤ D.M :=
    PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup D.maxLocal hD₃U hD₃P hP.isPGroup
  refine ⟨P, hP, hD₃P, hPM, ?_, ?_⟩
  · intro h hhH hhP
    have hhM : h ∈ D.M :=
      PartOne.Section9.mem_of_map_conj_le_of_mem_uniqueSet D.maxLocal hD₃U (hhP.trans hPM)
    have hLmap : L.map (MulAut.conj h).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHMnorm ⟨hhH, hhM⟩)
    have hLP3 : IsPGroup 3 ↥(L ⊓ P) := hP.isPGroup.to_inf_right
    have hdiv : Nat.card ↥(L ⊓ P) ∣ 3 := card_dvd_three_of_isPGroup hA5 hLP3 inf_le_left
    have hcard_inf : Nat.card ↥(L ⊓ P) ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
    have hD₃_eq : D₃ = L ⊓ P :=
      Subgroup.eq_of_le_of_card_ge (le_inf hD₃L hD₃P) (by rwa [hD₃])
    set E : Subgroup G := D₃.map (MulAut.conj h).toMonoidHom with hE
    have hEL : E ≤ L := by
      rw [hE, ← hLmap]
      exact Subgroup.map_mono hD₃L
    have hEP : E ≤ P := by simpa [hE] using hhP
    have hEcard : Nat.card E = 3 := by
      rw [hE, Subgroup.card_map_of_injective (MulAut.conj h).injective, hD₃]
    have hE_eq : E = L ⊓ P :=
      Subgroup.eq_of_le_of_card_ge (le_inf hEL hEP) (by rw [hEcard]; exact hcard_inf)
    rw [hE_eq, ← hD₃_eq]
  · have hPN : P ≤ normalizer (L : Set G) := (le_inf hP.le hPM).trans hHMnorm
    exact exists_cyclic_hom_of_le_normalizer hA5 hP.isPGroup hPN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
