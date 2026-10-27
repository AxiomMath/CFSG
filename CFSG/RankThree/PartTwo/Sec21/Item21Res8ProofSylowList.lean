module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res8ProofSylow
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S11c.HNAlternating
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] def KF2110SylowNoncentralList : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → 3 ∣ Nat.card (Subgroup.center X) →
    27 ∣ Nat.card (X ⧸ Subgroup.center X) →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (X ⧸ Subgroup.center X) p e) ∨
      ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.J3) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.ON)) →
    ∀ S : Sylow 3 X, ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧
      ∃ t ∈ (S : Subgroup X), s * t ≠ t * s

open Item21Res8Proof

theorem kF2110SylowNoncentralBig_of (h43 : Sec4.Item4_3) (h41 : Sec4.Item4_1LargePrime)
    (hList : KF2110SylowNoncentralList) : KF2110SylowNoncentralBig := by
  intro G _ _ hst d hd1 hd3 J hJ hdJ h27 S hS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : IsQuasisimple (lBar J) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hJ
  obtain ⟨z, hz, hz1, hz3⟩ := exists_center_lBar hd1 hd3 hJ hdJ
  have h3Z : 3 ∣ Nat.card (Subgroup.center (lBar J)) := by
    have hord : orderOf (⟨z, hz⟩ : Subgroup.center (lBar J)) = 3 :=
      orderOf_eq_prime (Subtype.ext hz3) fun h1 => hz1 (congrArg Subtype.val h1)
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center (lBar J))
    rwa [hord] at h1
  have hCd : Subgroup.centralizer ({d} : Set G) ≠ ⊤ :=
    Sec6.centralizer_ne_top_of_ne_one hst.toTheoremFourHyp hd1
  have hS4C : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hst.toTheoremFourHyp.sectionFourHyp hCd
  obtain ⟨hJC, hJ1⟩ := PartOne.mem_thetaComponentsAt_iff.mp hJ
  have hS4' := Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h41 hS4C hJ1
  have hS4 : SectionFourHyp (lBar J) :=
    Sec4.Census.sectionFourHyp_of_mulEquiv
      (Sec14.quotThetaEquiv (Subgroup.subgroupOfEquivOfLe hJC)) hS4'
  have hcardQ : ∀ {Y : Type} [Group Y] [Finite Y],
      Nonempty (lBar J ⧸ Subgroup.center (lBar J) ≃* Y) → ¬ 27 ∣ Nat.card Y → False :=
    fun ⟨e⟩ hY => hY (Nat.card_congr e.toEquiv ▸ h27)
  have hList' := fun hfam => exists_of_lBar hS (hList (lBar J) hq h3Z h27 hfam)
  rcases h43 (lBar J) hS4 hq h3Z with hL3 | hA6 | hA7 | hG2 | hU4 | hM22 | hJ3 | hMcL | hON
  · exact hList' (Or.inl hL3)
  · exact (hcardQ hA6 (by
      rw [PartOne.HNRed.card_alternatingGroup_fin 6 (by norm_num)]
      norm_num [Nat.factorial])).elim
  · exact (hcardQ hA7 (by
      rw [PartOne.HNRed.card_alternatingGroup_fin 7 (by norm_num)]
      norm_num [Nat.factorial])).elim
  · exact hList' (Or.inr (Or.inl hG2))
  · exact hList' (Or.inr (Or.inr (Or.inl hU4)))
  · exact (hcardQ hM22 (by rw [KFacts.KS14.card_nativeM22]; norm_num)).elim
  · exact hList' (Or.inr (Or.inr (Or.inr (Or.inl hJ3))))
  · exact hList' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMcL)))))
  · exact hList' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hON)))))

end CFSG.RankThree.PartTwo.Sec21
