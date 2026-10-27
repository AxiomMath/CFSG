module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DCommon
public import CFSG.RankThree.PartTwo.Sec8.Hering88DT
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
public import CFSG.RankThree.PartTwo.Sec8.Hering88CL2
public import CFSG.RankThree.PartTwo.Sec8.Hering88COdd
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


@[expose] def KF88Case1Inner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Odd n' ∧ Case83One Y x A₀ d' n') →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) → Good88 Y x d

@[expose] def KF88Case1ThreeA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Odd n' ∧ Case83One Y x A₀ d' n') →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          IsQuasisimple (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) →
          (∃ z : imageModTheta Y
              (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))),
            (∀ y, z * y = y * z) ∧ z ≠ 1 ∧ z ^ 3 = 1) → Good88 Y x d

@[expose] def KF88Case1NontrivOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G), Sec8Pair G A c L a b X 1 →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Odd n' ∧ Case83One Y x A₀ d' n') →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≠ ⊥

namespace Hering88D

theorem outThreeCyclic_of_case1
    {Q : Type} [Group Q] {m : ℕ} (h : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) :
    KFacts.OutThreeCyclic Q := by
  rcases h with hD | ⟨K, _, _, hK, ⟨e⟩⟩
  · obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    exact (KFacts.outThreeCyclic_triality hm1 hK hσ).of_mulEquiv e
  · have hm1 : 1 ≤ m := Item86ResProof.one_le_of_isoTrialityD4_or_isoGTwoEven (Or.inr ⟨K,
      inferInstance, inferInstance, hK, ⟨e⟩⟩)
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := 3 * m) (by rw [← Nat.card_eq_fintype_card, hK])
    have hK3 : ringChar K ≠ 3 := by
      rw [ringChar.eq K 2]
      norm_num
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (KFacts.outThreeCyclic_g2 K hK3 hK4).of_mulEquiv e

theorem kF88StepDCaseOneOdd_of_inner
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hC : KF88SwapCent) (hF : KF84Field)
    (hAut : Sec4.K419AutThree) (hT : Hering88C.KF89JCentType419)
    (hI : KF88Case1Inner) : KF88StepDCaseOneOdd := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩
  have hfam : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) m ∨
      IsoGTwoEven (Y ⧸ aschbacherSolvableCore 3 Y) (3 * m) := hc1.1
  have hOTC := outThreeCyclic_of_case1 hfam
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne, E, hEA, hdE, hInv⟩ :=
    exists_inner_d_two_local h45 h84 hC hF hAut hT h hY hIJ hx hxY hOTC
  exact ⟨d, hdcl, hdx, hI G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩ d hdcl hdx
    hdA hd3 hdN hin hne ⟨E, hEA, hdE, hInv⟩⟩

theorem kF88Case1Inner_of_shapes
    (h47 : Sec4.Inputs47ClassesD4) (hF : KF84Field) (hA : KF88Case1ThreeA)
    (h1 : KF88Case1NontrivOne) : KF88Case1Inner := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY hc d hdcl hdx hdA hd3 hdN hin hne hE
  obtain ⟨A₀, d', m, hodd, hc1⟩ := hc
  have hck : ¬ (KFacts.InducesStdKind Y d .field ∨ KFacts.InducesStdKind Y d .graphField) := by
    rintro (h' | h')
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).choose_spec hin
  have hshape : Item8KFacts3.ResidualShape (imageModTheta Y
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) (3 * m) := by
    rcases hc1.1 with hD | ⟨K, _, _, hK, ⟨e⟩⟩
    · obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
      exact Item8KFacts3.d4_residualShape hdN hd3 hck hne hm1 hK hσ e
    · have hm1 : 1 ≤ m := hodd.pos
      exact Item8KFacts3.g2_residualShape Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
        Sec11.KS11Lie7Proof.g2ThreeACentMinus_holds hdN hd3 hck hne (by omega) hK e
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact h.mem_A
    · exact (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  rcases hshape with hL2 | ⟨hq, z, hzc, hz1, hz3⟩ | hs
  · obtain ⟨eK⟩ := hL2
    exact Hering88C.good88_of_l2 h47 hodd hxY (hA3 x hxA) (hAc d hdA x hxA) (Or.inl hc1.1) eK
  · exact hA G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩ d hdcl hdx hdA hd3 hdN
      hin hne hE hq ⟨z, hzc, hz1, hz3⟩
  · exfalso
    have hbot : imageModTheta Y
        (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) = ⊥ :=
      Subgroup.eq_bot_of_subsingleton _
    obtain ⟨-, -, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      exact h1 G A c L a b X h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, hc1⟩ d hdcl hdx hdA hd3 hdN
        hin hne hE hbot
    · exact imageModTheta_residual_centralizer_ne_bot hF h hn2 hIJ hdcl hbot

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
