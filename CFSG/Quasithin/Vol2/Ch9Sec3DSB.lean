module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

theorem card_vm (F : Type) [Field F] [Fintype F] :
    Nat.card (Om4.VM F) = Fintype.card F ^ 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Om4.VM F ≃ Matrix (Fin 2) (Fin 2) F),
    Nat.card_eq_fintype_card]
  change Fintype.card (Fin 2 → Fin 2 → F) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  ring

theorem oTwoQuot_facts_of_alt_five {G : Type} [Group G]
    {K : Subgroup G} (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    Nat.card (oTwoQuot ↥K) = 60 ∧ IsRankOneListed (oTwoQuot ↥K) := by
  obtain ⟨eA⟩ := hKA
  have e1 : oTwoQuot ↥K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2).symm).trans eA
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    decide
  · have hF : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (Or.inl hF)
    exact Or.inl ⟨2, by norm_num, ⟨e1.trans (e5.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 2)).symm)⟩⟩

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

end CFSG.Quasithin.H13.Ch9
