module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVO8p
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import Certificates.Certificate428002
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.Assembly.RankThreeEven (projOmegaPlus)

set_option linter.unusedSectionVars false

theorem omWitData_gens_mem :
    ∀ k < omWitData.gens.size, permOfArr omWitData.n omWitData.gens[k]! ∈ autT := by
  intro k hk
  have hk10 : k < 10 := by simpa [omWitData, genArrs_size] using hk
  exact gen_mem_autT hk10

theorem omWitData_gens_mem_omega :
    ∀ k < omWitData.nGens, permOfArr omWitData.n omWitData.gens[k]! ∈ omegaT := by
  intro k hk
  have hk8 : k < 8 := by simpa [omWitData] using hk
  exact gen_mem_omegaT hk8

theorem omWitData_pOrd : omWitData.pOrd = 3 ^ 6 := rfl

theorem wit3_autT :
    ∀ a ∈ autT, a ≠ 1 → a ^ 3 = 1 → Wit3 omegaT a := by
  haveI : Finite ↥autT := Nat.finite_of_card_ne_zero (by rw [card_autT]; norm_num)
  obtain ⟨P, hPA, hPcard, hP⟩ := Certificates.certificate428002.apply
    autT omegaT omWitData_gens_mem omWitData_gens_mem_omega
  exact wit3_all_of_sylow_sub autT omegaT P omegaT_le_autT
    (fun g hg y hy => (conj_mem_omegaT hg).1 hy) hPA 6 (hPcard.trans omWitData_pOrd)
    (by rw [card_autT]; decide) hP

theorem listRow_omegaPlusT :
    ListRow ↥omegaT := by
  haveI : Finite ↥omegaT := Nat.finite_of_card_ne_zero (by rw [card_omegaT]; norm_num)
  exact listRow_of_wit3_sub omegaT_le_autT wit3_autT

theorem outerRow_omegaPlusT :
    OuterRow ↥omegaT := by
  haveI : Finite ↥omegaT := Nat.finite_of_card_ne_zero (by rw [card_omegaT]; norm_num)
  refine outerRow_of_wit3_sub omegaT_le_autT (MulEquiv.ofBijective autConj autConj_bijective)
    ?_ wit3_autT
  intro y hy
  have : autConj y ∈ (omegaT.subgroupOf autT).map autConj :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
  rw [map_autConj_omegaT] at this
  exact this

theorem rowOf_omegaPlus :
    RowOf (projOmegaPlus 4 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  have hmodel : CFSG.Open.StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1))
      .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero,
      ⟨Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  have hlm : CFSG.Blueprint.LieModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by decide, hmodel⟩
  obtain ⟨e'⟩ := nonempty_mulEquiv_omegaT hlm
  exact GoodRow.of_mulEquiv (e.trans e').symm ⟨listRow_omegaPlusT, outerRow_omegaPlusT⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
