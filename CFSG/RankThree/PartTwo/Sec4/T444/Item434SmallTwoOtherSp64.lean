module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeSp64
import CFSG.RankThree.PartTwo.KFacts.KS21SylowSp64
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.LocalAnalysis.ComponentInitial

namespace Item434SmallTwoOther

theorem mem_range_conj_of_pow_three_sp64 (φ : MulAut (StatedSp 3 (GaloisField 2 2)))
    (hφ : φ ^ 3 = 1) : φ ∈ (MulAut.conj : StatedSp 3 (GaloisField 2 2) →* _).range := by
  have h := KFacts.KS21.Sp64.mem_range_conj_of_pow
    (MulAut.congr KFacts.KS21.Sp64.psEquivSp.symm φ) ⟨1, by rw [pow_one, ← map_pow, hφ, map_one]⟩
  exact (KFacts.isInnerAut_congr KFacts.KS21.Sp64.psEquivSp.symm φ).mp h

theorem center_sp64 : Subgroup.center (StatedSp 3 (GaloisField 2 2)) = ⊥ :=
  CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_sp64 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 3 (GaloisField 2 2)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic hodd
    (e₀.trans (projSpEquivStatedProj 3 (GaloisField 2 2)))

theorem false_of_sp64 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 3 (GaloisField 2 2)) : False := by
  have hZ := center_layer_eq_bot_of_sp64 h e₀
  have hD := isElemAbelian_torus_gf4 (r := 3)
  have hD27 : Nat.card (SymplecticTorusWeyl.torus 3 (GaloisField 2 2)) = 27 := by
    rw [card_torus_gf4]
    norm_num
  rcases h.card_layerStar with h9 | ⟨h27, -⟩
  · exact Item434Spor.false_of_card_nine h hZ (e₀.trans KFacts.KS21.Sp64.equivSp) hD hD27 h9
  refine false_of_gen_of_inner h hZ (e₀.trans KFacts.KS21.Sp64.equivSp)
    mem_range_conj_of_pow_three_sp64 center_sp64 fun P hP hPc => ?_
  obtain ⟨g, rfl⟩ := exists_map_conj_of_maxEA KFacts.KS21.Sp64.maxEA_Sp hD hD27 hP
    (hPc.trans h27)
  exact closure_hyperCent_map_conj closure_hyperCent_torus_gf4 g

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtSp64 : Item434SmallTwoOtherAtSp64 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoOther.false_of_sp64 hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
