module

public import CFSG.Quasithin.H13.NQCatQuasisimple
public import CFSG.Quasithin.H13.NQRigidFacts
public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
public import CFSG.RankThree.ThinCatalog.SporadicJ1
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.NQBlockCommonResidual
public import CFSG.Quasithin.H13.NQRigidFitting4
public import CFSG.Quasithin.H13.NQRigidSeed
public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.Quasithin.SteinbergCDOddResidualTools
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
  (linear_unitary_perfect_cover_outer_derived_diagonal_bound)

theorem not_dvd_card_commutator_of_card_le_four {X : Type*} [Group X] [Finite X]
    (h : Nat.card X ≤ 4) {ℓ : ℕ} (hℓ5 : 5 ≤ ℓ) : ¬ ℓ ∣ Nat.card (commutator X) := by
  intro hd
  have h1 := Nat.le_of_dvd Nat.card_pos hd
  have h2 : Nat.card (commutator X) ≤ Nat.card X := Subgroup.card_le_card_group _
  omega

theorem card_commutator_eq_one_of_comm {X : Type*} [Group X] (h : ∀ a b : X, a * b = b * a) :
    Nat.card (commutator X) = 1 := by
  have hbot : commutator X = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  rw [hbot, Subgroup.card_bot]

theorem not_dvd_card_commutator_of_isPGroup_two {X : Type*} [Group X] [Finite X]
    (h : IsPGroup 2 X) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    ¬ ℓ ∣ Nat.card (commutator X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (h.to_subgroup (commutator X)).exists_card_eq
  rw [hk]
  intro hd
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow hd))

theorem stmtOuterDerivedCoprime_of
    (hthin : NQRigid.FactThinCentralQuotient) : NQRigid.StmtOuterDerivedCoprime := by
  intro H _ _ hHSQ J hJ ⟨h, hJh⟩ ℓ hℓ hℓ5
  have hr := hthin H hHSQ J hJ h hJh
  obtain ⟨hSQT, hcat⟩ := sqt_catalog_center_quotient hJ.1 (hHSQ.subgroup J)
  obtain ⟨hperf, hsimple, hnonab⟩ := hJ.1
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  have hS : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (J ⧸ Subgroup.center J)) ≤ 2 :=
    SectionRank.isStronglyQuasithin_iff.1 hSQT
  have hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup (J ⧸ Subgroup.center J)) ≤ 1 := by
    rw [← SectionRank.pRank_eq_open_pRank_top]
    exact hr 3 Nat.prime_three (by norm_num)
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hcl | hexc | hspor
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  ·
    have hle : Nat.card (Outer (J ⧸ Subgroup.center J)) ≤ 4 := by
      rcases (show n = 6 ∨ n = 5 ∨ 7 ≤ n by omega) with rfl | hn'
      · rw [Nat.card_congr (equivalence e).toEquiv]
        exact Sporadic.SchreierLemmas.outer_alternating_six.1
      · exact (Nat.le_of_dvd (by norm_num)
          (outer_card_dvd_two_of_equiv_outside_six hn' e)).trans (by norm_num)
    exact not_dvd_card_commutator_of_card_le_four
      ((card_outer_le_of_perfect J (MulEquiv.refl _)).trans hle) hℓ5
  ·
    obtain ⟨t, n, p, f, hm⟩ := hcl
    have hp : p.Prime := hm.1.1
    have hodd : p ≠ 2 → t = .PSL ∨ t = .PSU := fun hp2 => by
      rcases SectionRank.sqt_odd_classical_restriction hS hp2 hm with ⟨ht, -⟩ | ⟨ht, -⟩ |
        ⟨ht, -⟩
      · exact .inl ht
      · exact .inl ht
      · exact .inr ht
    cases t with
    | PSL =>
      have hb := (linear_unitary_perfect_cover_outer_derived_diagonal_bound J .PSL n p f 1
        (.inl ⟨rfl, rfl⟩) hm).2.1
      have hd : Int.gcd n ((p : ℤ) ^ f - 1) = Nat.gcd n (p ^ f - 1) := by
        rw [← Int.gcd_natCast_natCast, Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), Nat.cast_pow,
          Nat.cast_one]
      rw [hd] at hb
      obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      intro hdvd
      have hdvd' := hdvd.trans hb
      have hℓn : ℓ ∣ n := hdvd'.trans (Nat.gcd_dvd_left _ _)
      have hℓq : ℓ ∣ p ^ f - 1 := hdvd'.trans (Nat.gcd_dvd_right _ _)
      have hn5 : 5 ≤ n := hℓ5.trans (Nat.le_of_dvd (by omega) hℓn)
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hrank := (SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hp hn
        (r := ℓ) (by omega) (H := StatedSL n K) (.inl ⟨hK, rfl, hℓq⟩)
        ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) le_rfl).1
      have h2 := hS ℓ hℓ (by omega)
      rw [SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e] at h2
      omega
    | PSU =>
      have hb := (linear_unitary_perfect_cover_outer_derived_diagonal_bound J .PSU n p f (-1)
        (.inr ⟨rfl, rfl⟩) hm).2.1
      have hd : Int.gcd n ((p : ℤ) ^ f - -1) = Nat.gcd n (p ^ f + 1) := by
        rw [← Int.gcd_natCast_natCast, sub_neg_eq_add, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      rw [hd] at hb
      obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      intro hdvd
      have hdvd' := hdvd.trans hb
      have hℓn : ℓ ∣ n := hdvd'.trans (Nat.gcd_dvd_left _ _)
      have hℓq : ℓ ∣ p ^ f + 1 := hdvd'.trans (Nat.gcd_dvd_right _ _)
      have hn5 : 5 ≤ n := hℓ5.trans (Nat.le_of_dvd (by omega) hℓn)
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hrank := (SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hp
        (by omega : 2 ≤ n) (r := ℓ) (by omega) (H := StatedSU n (p ^ f) K) (.inr ⟨hK, rfl, hℓq⟩)
        ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) le_rfl).1
      have h2 := hS ℓ hℓ (by omega)
      rw [SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e] at h2
      omega
    | PSp =>
      by_cases hp2 : p = 2
      · subst hp2
        exfalso
        obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
        have : CharP K 2 := ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
        obtain ⟨⟨A, hA, hAcard⟩, -⟩ :=
          LieType.unique_even_symplectic_prime_field_three_rank (K := K) (n := n) (by omega)
        have hle := LieType.SteinbergBR.le_pRank_of_card (by norm_num) A hA hAcard
        rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_top_eq_of_mulEquiv
          (by norm_num : 1 < 3) e] at hle
        omega
      · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
    | POmegaOdd =>
      have hp2 : p ≠ 2 := hm.1.2.2.2
      rcases hodd hp2 with h | h <;> exact absurd h (by decide)
    | POmegaPlus =>
      by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
        have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
          Finite.of_equiv _ e.toEquiv
        exact (QuasithinUnique.Setup.Family.even_orthogonal_plus_not_sqt hK hn
          (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
      · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
    | POmegaMinus =>
      by_cases hp2 : p = 2
      · subst hp2
        obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hm
        have : Finite (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
          Finite.of_equiv _ e.toEquiv
        exact (QuasithinUnique.Setup.Family.even_orthogonal_minus_not_sqt hK hn b c hbc
          (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
      · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hm.2.elim
  ·
    rcases (sqt_exceptional_central_quotient_outer_prime_control J hSQT hexc).1 with hc | h2
    · rw [card_commutator_eq_one_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b]
      exact hℓ.not_dvd_one
    · exact not_dvd_card_commutator_of_isPGroup_two h2 hℓ (by omega)
  ·
    rcases sqt_sporadic_perfect_cover_outer_J4_alternative J inferInstance hSQT hspor with
      he | ⟨hc, -, -⟩
    · exfalso
      obtain ⟨e⟩ := he
      have : Finite NativeSporadic.J4 := Finite.of_equiv _ e.toEquiv
      obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := SectionRank.J4_sylow3_cubic_witness
      have h2 := RankThree.ThinCatalog.two_le_pRank_three_of_mulEquiv
        (G := NativeSporadic.J4) e
        (RankThree.ThinCatalog.two_le_pRank_of_cubic_witness Nat.prime_three hx hz hzx hzy)
      have h3 := hr 3 Nat.prime_three (by norm_num)
      omega
    · rw [card_commutator_eq_one_of_comm fun a b => hc.is_comm.comm a b]
      exact hℓ.not_dvd_one

theorem stmtOuterDerivedCoprime_holds
    : NQRigid.StmtOuterDerivedCoprime :=
  stmtOuterDerivedCoprime_of NQRigid.factThinCentralQuotient_holds

end CFSG.Quasithin.H13.NQCat
