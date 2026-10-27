module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_inSubgroup_perfectResidual_of_projSp {Q : Type} [Group Q] [Finite Q]
    {C : Subgroup Q} {m : ℕ} (hm : 1 ≤ m) (e : C ≃* projSp 2 (GaloisField 2 m)) :
    IsQuasisimple (inSubgroup perfectResidual C) := by
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  set ψ : C ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 2 (GaloisField 2 m)) :=
    e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with hψ
  set ι : (perfectResidual C) ≃* inSubgroup perfectResidual C :=
    (perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective with hι
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour
      (ψ.trans (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2))
    have heq : perfectResidual C = commutator C := by
      refine le_antisymm ?_ (le_perfectResidual_of_isPerfect hq.1)
      refine (iInf_le _ 1).trans ?_
      rw [derivedSeries_one]
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr heq.symm).trans ι) hq
  · have h4 : 4 ≤ Nat.card (GaloisField 2 m) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h2
    have hs := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp
      (GaloisField 2 m) 2 (by norm_num) (Or.inl (Or.inr h4))
    have h4' : ∃ s : Finset (GaloisField 2 m), s.card = 4 := by
      have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField 2 m))) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact h4)
      exact ⟨s, hs⟩
    have hp := CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2
      (GaloisField 2 m) (Or.inl h4')
    have hpC : Group.IsPerfect C := hp.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
    have hsC : IsSimpleGroup C := ψ.isSimpleGroup
    have hnab : ∃ a b : C, a * b ≠ b * a := by
      by_contra hab
      push Not at hab
      have hc : commutator C = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      have hnt : Nontrivial C := hsC.toNontrivial
      rw [hpC.commutator_eq_top] at hc
      exact top_ne_bot hc
    have hqC : IsQuasisimple C := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
    have heq : perfectResidual C = ⊤ := KFacts.perfectResidual_eq_top_of_isPerfect hpC
    exact LocalCores.isQuasisimple_of_mulEquiv
      (((MulEquiv.subgroupCongr heq).trans Subgroup.topEquiv).symm.trans ι) hqC

end Item87Res2Proof


@[expose] def KF87CentRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (m : ℕ), 1 ≤ m →
    IsGammaType (L ⧸ aschbacherSolvableCore 3 L) m →
    ¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * m))) →
    x ^ 3 = 1 → (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L) = ⊥ ∨
        IsQuasisimple (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L))

theorem kF87Cent_of (hR : KF87CentRest) : KF87Cent := by
  intro G _ _ L x m hm htype hx3 hk
  by_cases hSp : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * m)))
  · right
    have hout : Sec4.InducesOuterTheta x L := by
      rcases hk with h | h
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
      · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (by omega) hx3 hout hSp
    exact Item87Res2Proof.isQuasisimple_inSubgroup_perfectResidual_of_projSp hm ι
  · exact hR G L x m hm htype hSp hx3 hk

end CFSG.RankThree.PartTwo.Sec8
