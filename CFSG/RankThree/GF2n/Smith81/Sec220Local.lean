module

public import CFSG.RankThree.GF2n.Smith81.Sec1Main
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Consequences

variable [Finite G] {M Q Z B : Subgroup G} {z v : G}

theorem centralizer_le_M (Hs : StrothHyp M Q Z) {a : G} (ha : a ∈ Z) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro c hc
  have h := IsZConjugate.mem_normalizer_of_commute Hs (IsZConjugate.self Z) ha1 ha
    (show Commute c a from Subgroup.mem_centralizer_singleton_iff.mp hc)
  rwa [Hs.normalizer_Z.1] at h

theorem mem_H0_of_isConj_commute (Hs : StrothHyp M Q Z) {z a : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (ha : IsConj z a) (hc : Commute a z) : a ∈ H0 M Z := by
  have haM : a ∈ M := by
    have := IsZConjugate.mem_normalizer_of_commute Hs (IsZConjugate.self Z) hz1 hz hc
    rwa [Hs.normalizer_Z.1] at this
  refine ⟨haM, ?_⟩
  by_cases haQ : a ∈ Q
  · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hx' : x ∈ Subgroup.centralizer (Q : Set G) := by rw [Hs.centralizer_Q]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp hx' a haQ).symm
  · obtain ⟨g, rfl⟩ := isConj_iff.mp ha
    have hs := Sit.of_conj Hs hz hz1 haM haQ
    exact ((smith_1_12 hs).1 hs.mem).2

end Consequences

end CFSG.RankThree.GF2n.Smith81
