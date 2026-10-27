module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Assembly.RankThreeEven (projSL projSU)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

section Rows


theorem noCC425_of_char3 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hS : IsChevOfChar 3 S) : NoCC425 S := by
  intro s K hcc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : s ^ 3 = 1 := by rw [← hcc.orderOf_eq]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    have := hcc.orderOf_eq
    rw [h, orderOf_one] at this
    norm_num at this
  have hno := noThreeComponents_of_conj YS08.LieQ.lieQConstrainedInner_three_holds hs hna hS
    hs1 hs3
  have hfix : Sec4.autFix (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) :=
    RonanK429.RowV.autFix_conj_eq_centralizer s
  have hK : K ≤ Sec4.autFix (MulAut.conj s) := hfix ▸ hcc.le_centralizer
  have hsn : (K.subgroupOf (Sec4.autFix (MulAut.conj s))).IsSubnormal := by
    rw [hfix]
    exact hcc.isSubnormal
  have h3 : 3 ∣ Nat.card K := by
    have ho : orderOf (⟨s, hcc.mem⟩ : ↥K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hcc.orderOf_eq
    rw [← ho]
    exact orderOf_dvd_natCard _
  exact hno K (glaPComponent_of_autFix hK hcc.isQuasisimple hsn h3)

theorem rowOf425_of_char3 {X : Type} [Group X] (idx : ValidLieTypeIndex) (h3 : lieIndexChar idx.1 = 3)
    (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.lie idx).Group)) : RowOf425 X := by
  obtain ⟨eX⟩ := hX
  refine rowOf425_of_noCC fun S _ _ hs hna ⟨e⟩ => noCC425_of_char3 hs hna ?_
  exact ⟨idx, YS08.isChevIndexOfChar_of_lieIndexChar_eq h3, ⟨e.trans eX⟩⟩


theorem kT2_nine_SL3_nine : RowOf425 (projSL 3 (GaloisField 3 2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 2 ⟨3, 2, Fact.out, by norm_num⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact rowOf425_of_char3 ⟨_, hv⟩ (by simp [lieIndexChar])
    ⟨(Census.typeAGroupEquivProjSL 2 ⟨3, 2, Fact.out, by norm_num⟩ hv).symm⟩

theorem kT2_nine_SU3_nine : RowOf425 (projSU 3 3 2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.twistedA 2 ⟨3, 2, Fact.out, by norm_num⟩).Valid :=
    valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact rowOf425_of_char3 ⟨_, hv⟩ (by simp [lieIndexChar])
    ⟨(Census.typeTwistedAGroupEquivProjSU 2 ⟨3, 2, Fact.out, by norm_num⟩ hv).symm⟩

theorem kT2_nine_SL4 : RowOf425 (projSL 4 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : (LieTypeIndex.A 3 ⟨3, 1, Fact.out, Nat.one_pos⟩).Valid :=
    valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num
  exact rowOf425_of_char3 ⟨_, hv⟩ (by simp [lieIndexChar])
    ⟨(Census.typeAGroupEquivProjSL 3 ⟨3, 1, Fact.out, Nat.one_pos⟩ hv).symm⟩

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
