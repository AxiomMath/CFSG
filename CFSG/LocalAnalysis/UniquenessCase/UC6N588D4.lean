module

public import CFSG.Adapters.LieModelOrders
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)

namespace N588

variable {X : Type} [Group X]

theorem card_of_psl_two {p f : ℕ} (h : LieModel X .PSL 2 p f) : Nat.card X = ordA 1 (p ^ f) :=
  (h.card_eq_lieOrd (by norm_num)).trans rfl

theorem card_of_isAlt {n : ℕ} (hn : 2 ≤ n) (h : IsAlt X n) : Nat.card X = n.factorial / 2 := by
  obtain ⟨e⟩ := h
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem isAlt_six_of_psl_two {r : ℕ} (h : LieModel X .PSL 2 r 2) (hr : r = 3) : IsAlt X 6 := by
  subst hr
  exact LieModel.nonempty_mulEquiv_alternating_six h

theorem simple_card_of_isAlt_ten (h : IsAlt X 10) :
    IsSimpleGroup X ∧ Nat.card X = 1814400 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := h
    exact (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  · rw [card_of_isAlt (by norm_num) h]
    decide

theorem simple_card_of_isSpor_M11 (h : IsSpor X .M11) :
    IsSimpleGroup X ∧ Nat.card X = 7920 := by
  obtain ⟨e⟩ := h
  have e' : X ≃* CFSG.Blueprint.NativeSporadic.M11 := e
  refine ⟨(MulEquiv.isSimpleGroup_congr e').mpr
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2, ?_⟩
  rw [Nat.card_congr e'.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M11

section Tits

theorem simple_card_of_tits (h : LieModel X .Tits 0 2 1) :
    IsSimpleGroup X ∧ Nat.card X = 17971200 := by
  obtain ⟨-, hT⟩ := h.reeTitsModel (by decide)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 hT
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.Schreier.Tits.titsD_simple, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Schreier.Tits.card_titsD

end Tits

end N588

end CFSG.LocalAnalysis.UniquenessCase.UC6
