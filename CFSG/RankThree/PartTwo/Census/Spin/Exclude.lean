module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.RankThree.PartTwo.Census.Spin.Witness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem le_localRank_of_hasWitness {Q : Type} [Group Q] [Finite Q] {p k : ℕ} (hp : p.Prime)
    (h : HasWitness Q p k) : k ≤ localRank p Q := by
  obtain ⟨E, P, hE, hEp, hc, hP, hP2, hEP⟩ := h
  exact le_localRank_of_le_normalizer hp hP hP2 ⟨hE, hEp⟩ hc hEP

theorem excluded433_of_hasWitness_four {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 4 ≤ k) (h : HasWitness d.Group p k) : Excluded433 (.lie d) := by
  intro G _ _ hG e
  have e' : G ≃* d.Group := e
  have : Finite d.Group := Finite.of_equiv G e'.toEquiv
  exact hG.false_of_four_le_localRank e' hp hp2 (hk.trans (le_localRank_of_hasWitness hp h))

theorem excluded433_of_hasWitness_three {d : ValidLieTypeIndex} {p k : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hk : 3 ≤ k) (h : HasWitness d.Group p k) : Excluded433 (.lie d) := by
  intro G _ _ hG e
  have e' : G ≃* d.Group := e
  have : Finite d.Group := Finite.of_equiv G e'.toEquiv
  exact hG.false_of_three_le_localRank e' hp hp3 (hk.trans (le_localRank_of_hasWitness hp h))

section Families

variable {r : ℕ} {q : PrimePower} {p k : ℕ}

theorem excluded433_B_of_four (hv : (LieTypeIndex.B r q).Valid) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 4 ≤ k) (h : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩) p k) :
    Excluded433 (.lie ⟨.B r q, hv⟩) :=
  excluded433_of_hasWitness_four hp hp2 hk h

theorem excluded433_B_of_three (hv : (LieTypeIndex.B r q).Valid) (hp : p.Prime) (hp3 : 3 < p)
    (hk : 3 ≤ k) (h : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩) p k) :
    Excluded433 (.lie ⟨.B r q, hv⟩) :=
  excluded433_of_hasWitness_three hp hp3 hk h

theorem excluded433_D_of_four (hv : (LieTypeIndex.D r q).Valid) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 4 ≤ k) (h : HasWitness (TypeDLieIndex.Group ⟨⟨.D r q, hv⟩, by simp⟩) p k) :
    Excluded433 (.lie ⟨.D r q, hv⟩) :=
  excluded433_of_hasWitness_four hp hp2 hk h

theorem excluded433_D_of_three (hv : (LieTypeIndex.D r q).Valid) (hp : p.Prime) (hp3 : 3 < p)
    (hk : 3 ≤ k) (h : HasWitness (TypeDLieIndex.Group ⟨⟨.D r q, hv⟩, by simp⟩) p k) :
    Excluded433 (.lie ⟨.D r q, hv⟩) :=
  excluded433_of_hasWitness_three hp hp3 hk h

theorem excluded433_twistedD_of_four (hv : (LieTypeIndex.twistedD r q).Valid) (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 4 ≤ k)
    (h : HasWitness (TypeTwistedDLieIndex.Group ⟨⟨.twistedD r q, hv⟩, by simp⟩) p k) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) :=
  excluded433_of_hasWitness_four hp hp2 hk h

theorem excluded433_twistedD_of_three (hv : (LieTypeIndex.twistedD r q).Valid) (hp : p.Prime)
    (hp3 : 3 < p) (hk : 3 ≤ k)
    (h : HasWitness (TypeTwistedDLieIndex.Group ⟨⟨.twistedD r q, hv⟩, by simp⟩) p k) :
    Excluded433 (.lie ⟨.twistedD r q, hv⟩) :=
  excluded433_of_hasWitness_three hp hp3 hk h

end Families

end CFSG.RankThree.PartTwo.Census.Spin
