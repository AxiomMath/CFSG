module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporThTools
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeSMain
public import Certificates.Certificate17307

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

section ThreeA

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words ghat_card)


theorem th_not_dvd_card_centralizer_S :
    ¬ 3 ^ 10 ∣ Nat.card (Subgroup.centralizer ({thS} : Set ↥J)) := by
  haveI : Finite ↥J := finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr => (lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨e⟩ := nonempty_mulEquiv_adjointG2_of_six thEps hε ⟨0, hne⟩
  have hcardE : Nat.card ↥(Subgroup.closure (Set.range thEps)) = 4245696 :=
    (Nat.card_congr e.toEquiv).trans (ghat_card.trans (by norm_num))
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2
  have hdvd : 4245696 ∣ Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) := by
    rw [← hcardE]
    exact Subgroup.card_dvd_of_le hEC
  exact not_three_pow_ten_dvd_of_dvd_of_le Nat.card_pos hdvd hC

theorem th_three_dvd_index_S :
    3 ∣ (Subgroup.centralizer ({thS} : Set ↥J)).index := by
  haveI : Finite ↥J := finite_J
  refine three_dvd_index_of_not_pow_dvd _ (n := 10) ?_ th_not_dvd_card_centralizer_S
  rw [CFSG.Sporadic.Th.Max3.natCard_J]
  norm_num

end ThreeA

section ThreeC

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSeven
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
  CFSG.Monster.B.Fischer CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
  CFSG.HardMathSupport.Dickson.I271.TabThNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative
  CFSG.HardMathSupport.Dickson.I271


theorem th_card_centralizer_U :
    Nat.card (Subgroup.centralizer ({thU} : Set ↥CFSG.Sporadic.Th.J)) = 174960 :=
  Certificates.certificate17307.1

theorem th_three_dvd_index_U :
    3 ∣ (Subgroup.centralizer ({thU} : Set ↥CFSG.Sporadic.Th.J)).index := by
  haveI : Finite ↥CFSG.Sporadic.Th.J := finite_J
  refine three_dvd_index_of_not_pow_dvd _ (n := 10) ?_ ?_
  · rw [CFSG.Sporadic.Th.Max3.natCard_J]
    norm_num
  · rw [th_card_centralizer_U]
    norm_num

end ThreeC

section ThreeB

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271


theorem th_witness_Z :
    ∃ g : ↥J, (g * thZ * g⁻¹) * thZ = thZ * (g * thZ * g⁻¹) ∧
      g * thZ * g⁻¹ ∉ Subgroup.zpowers thZ := by
  haveI : Finite ↥J := finite_J
  obtain ⟨Q, -, hzQ, hz3, -, -, hQ⟩ := Certificates.certificate13650
  have hzo : orderOf thZ = 3 := th_orderOf.2.1
  obtain ⟨t, -, -, E, -, hE, hEcard, hEcl⟩ := hQ thZ hzQ hzo
  have hz3' : thZ ^ 3 = 1 := hz3
  have hcl : ∀ x ∈ E, x ≠ 1 → IsConj x thZ ∨ IsConj x (thZ ^ 2) := hEcl
  exact witness_of_elemAbelian_nine (z := thZ) hz3' hE hEcard hcl

end ThreeB

end CFSG.RankThree.PartTwo.Sec4.RonanK432
