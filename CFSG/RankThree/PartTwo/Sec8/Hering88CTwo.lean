module

public import CFSG.RankThree.PartTwo.Sec8.Hering88CEng
public import CFSG.RankThree.PartTwo.Sec8.Hering88CL2
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeField
import CFSG.RankThree.PartTwo.Sec21.ReeF4Conj2ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


variable {G : Type} [Group G] [Finite G]

theorem ree_residual_native {X : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1)
    (hck : ¬ (KFacts.InducesStdKind X c .field ∨ KFacts.InducesStdKind X c .graphField))
    (hne : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨c, hcN⟩) ≠ 1) {m : ℕ} (hm : 1 ≤ m)
    (hR : IsoReeF4 (X ⧸ aschbacherSolvableCore 3 X) (3 * m)) :
    IsoSUThree (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G)))) (2 ^ (3 * m)) := by
  obtain ⟨k, K, _, _, _, hkm, hK, ⟨E⟩⟩ := hR
  have hk1 : 1 ≤ k := by omega
  have hK' : Nat.card K = 2 ^ (2 * k + 1) := by rw [hK, hkm]
  have : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K k) := Finite.of_equiv _ E.toEquiv
  have hin : KFacts.IsInnerAut (KFacts.inducedAutHom X E ⟨c, hcN⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hck (Or.inl (KFacts.InducesStdKind.largeRee k hk1 K hK'
      (KFacts.inducesKindLargeRee_field X hk1 hK'
        (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k K hK') hc3 hout E)))
  obtain ⟨w, -, hw3, hw1, ⟨eW⟩⟩ := Item8KFacts3.exists_conj_residual E
    (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial k K hK') hcN hc3 hin hne
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := Sec8.ReeF4Conj2Proof.kF83ReeCentThree_holds k K hk1 hK' w
    (orderOf_eq_prime hw3 hw1)
  rw [hkm] at hF ψ
  exact ⟨F, inferInstance, inferInstance, hF, ⟨eW.trans ψ⟩⟩

theorem kF88StepDCaseTwo_of
    (h45 : Sec4.Item4_5) (hC : KF88SwapCent) (hF : KF84Field) :
    KF88StepDCaseTwo := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hR, -, -⟩
  have hR' := hR
  obtain ⟨hAc, hA3⟩ := pair_commute_pow_three h
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact h.mem_A
    · exact (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  obtain ⟨k, Kf, _, _, _, hkm, hKf, ⟨e⟩⟩ := hR
  have hm1 : 1 ≤ m := by omega
  have hk1 : 1 ≤ k := by omega
  have hKf' : Nat.card Kf = 2 ^ (2 * k + 1) := by rw [hKf, hkm]
  have hOTC : KFacts.OutThreeCyclic (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (KFacts.outThreeCyclic_largeRee hk1 hKf').of_mulEquiv e
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne⟩ := exists_inner_d h45 hC hF h hY hIJ hx hxY hOTC
  have hck : ¬ (KFacts.InducesStdKind Y d .field ∨ KFacts.InducesStdKind Y d .graphField) := by
    rintro (h' | h')
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
  have eK := ree_residual_native hdN hd3 hck hne hm1 hR'
  have hout : Sec4.InducesOuterTheta x Y := by
    rcases hxY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := hout.choose
  have hdxc : d * x = x * d := hAc d hdA x hxA
  have hKY : inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Y :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hqu := Item86ResProof.isoSUThree_quot hm1 eK
  refine ⟨d, hdcl, hdx, ?_, ⟨m, hm1, Or.inl hqu⟩, ?_⟩
  · obtain ⟨F, _, _, hFc, ⟨φ⟩⟩ := hqu
    exact LocalCores.isQuasisimple_of_mulEquiv φ.symm
      (Item87Proof.isQuasisimple_statedSU_three hFc (by omega)).1
  · rw [← hkm] at eK
    exact Item8KFacts2Proof.inducesStdKind_field_of_ree hKY hxN
      (mem_normalizer_residual_centralizer hxN hdxc) (hA3 x hxA) hout hk1 hKf' e eK

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
