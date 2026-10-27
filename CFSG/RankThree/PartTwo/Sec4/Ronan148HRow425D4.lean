module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425G2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11
open scoped MatrixGroups

section D4

open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


variable {K : Type} [Field K]

theorem false_of_threeB_d4 [Finite K] {q : ℕ} {σ : K ≃+* K} (hK : Nat.card K = q ^ 3)
    (hσ : ∀ c, σ c = c ^ q) (h3 : ¬ 3 ∣ q) (hσ3 : σ ^ 3 = 1)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzC : z ∈ Subgroup.centralizer ((d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {J : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hJq : CFSG.IsQuasisimple J) (hzJ : z ∈ J) : False := by
  obtain ⟨hcomm, -⟩ := KS11Lie6Proof.d4ThreeBCent_holds K q σ hK hσ h3 z hzC hz3 hz1
  have hJS : J ≤ d4ShortSL2 K σ.toRingHom :=
    le_of_commutators_mem hJC (Subgroup.isPerfect_iff.mp hJq.1) hcomm
  have hzS := hJS hzJ
  obtain ⟨e⟩ := nonempty_mulEquiv_d4ShortSL2 hσ3
  set B := e.symm ⟨z, hzS⟩ with hB
  have heB : e B = ⟨z, hzS⟩ := MulEquiv.apply_symm_apply e _
  have hB3 : B ^ 3 = 1 := by
    rw [hB, ← map_pow]
    have : (⟨z, hzS⟩ : d4ShortSL2 K σ.toRingHom) ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hz3)
    rw [this, map_one]
  have hBc : ∀ A, A * B = B * A := by
    intro A
    apply e.injective
    rw [map_mul, map_mul, heB]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp hzC _ (e A).2
  have h1 := eq_one_of_central_of_pow_three hB3 hBc
  apply hz1
  have : (⟨z, hzS⟩ : d4ShortSL2 K σ.toRingHom) = 1 := by rw [← heB, h1, map_one]
  exact congrArg Subtype.val this

theorem isSLThreePiAt_d4 [Finite K] [CharP K 2] {n : ℕ} {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hσ3 : σ ^ 3 = 1) (hn : 2 ≤ n)
    (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (J : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hJC : J ≤ Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hJq : CFSG.IsQuasisimple J)
    (hJs : (J.subgroupOf (Subgroup.centralizer
      ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))).IsSubnormal)
    (hzJ : z ∈ J) : IsSLThreePiAt J (2 ^ n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have h3q : ¬ 3 ∣ 2 ^ n := fun h =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ n) σ hK hσ h3q z hz3 hz1
  set e := MulAut.conj g with he'
  obtain ⟨hJ'C, hJ's⟩ := map_le_centralizer_isSubnormal e hJC hJs
  have eJ : J ≃* J.map (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := J.equivMapOfInjective _ e.injective
  have hJ'q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJq
  have hez : e z = g * z * g⁻¹ := rfl
  have hz'3 : e z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz'1 : e z ≠ 1 := by
    rw [Ne, map_eq_one_iff _ e.injective]
    exact hz1
  have hz'J : e z ∈ J.map (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := ⟨z, hzJ, rfl⟩
  refine isSLThreePiAt_of_mulEquiv eJ ?_
  rcases hg with hS | hC
  · rw [← hez] at hS
    set J₁ := J.map (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hJ₁
    have hR : ∀ (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
        (R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        R ≤ Subgroup.centralizer ({c * e z * c⁻¹} :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
        (∀ a ∈ Subgroup.centralizer ({c * e z * c⁻¹} :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          ∀ b ∈ Subgroup.centralizer ({c * e z * c⁻¹} :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), a * b * a⁻¹ * b⁻¹ ∈ R) →
        CFSG.IsQuasisimple R → Nonempty (J₁ ≃* R) := by
      intro c R hRC hcomm hRq
      set e₂ := MulAut.conj c
      obtain ⟨hJ''C, hJ''s⟩ := map_le_centralizer_isSubnormal e₂ hJ'C hJ's
      have eJ' : J₁ ≃* J₁.map (e₂ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := J₁.equivMapOfInjective _ e₂.injective
      have hJ''q := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ' hJ'q
      have hez₂ : e₂ (e z) = c * e z * c⁻¹ := rfl
      rw [hez₂] at hJ''C hJ''s
      have hle := le_of_commutators_mem hJ''C (Subgroup.isPerfect_iff.mp hJ''q.1) hcomm
      have heq := eq_of_le_of_isQuasisimple hle hRC hJ''s hRq hJ''q
      exact ⟨eJ'.trans (MulEquiv.subgroupCongr heq)⟩
    rcases Nat.even_or_odd n with hev | hodd
    · have hmod : 2 ^ n % 3 = 1 := by
        obtain ⟨m, rfl⟩ := hev
        rw [← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      obtain ⟨c, R, -, hRC, hcomm, hRq, F, _, _, hF, ⟨eR⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model Nat.prime_two (by omega) (by norm_num) hmod hK hσ hS
          hz'3 hz'1
      obtain ⟨eJR⟩ := hR c R hRC hcomm hRq
      exact ⟨F, inferInstance, inferInstance, Or.inl ⟨hF, hmod, ⟨eJR.trans (eR.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F))⟩⟩⟩
    · have hmod : 2 ^ n % 3 = 2 := by
        obtain ⟨m, rfl⟩ := hodd
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have h2q : 2 < 2 ^ n := by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      obtain ⟨c, R, -, hRC, hcomm, hRq, U, hU, eR, -⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Item219LieProof.d4_threeA_model_unitary Nat.prime_two (by omega) (by norm_num) hmod h2q
          hK hσ hS hz'3 hz'1
      obtain ⟨eJR⟩ := hR c R hRC hcomm hRq
      have : CharP (AlgebraicClosure K) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
      obtain ⟨F, _, _, hF, ⟨eU⟩⟩ :=
        CFSG.OddStandard.GH71.S55.nonempty_statedSU_mulEquiv (Ω := AlgebraicClosure K)
          (ℓ := 2) (f := n) (by omega) hU
      exact ⟨F, inferInstance, inferInstance, Or.inr ⟨hF, hmod,
        ⟨eJR.trans (eR.trans eU.symm)⟩⟩⟩
  · rw [← hez] at hC
    exact (false_of_threeB_d4 hK hσ h3q hσ3 hC hz'3 hz'1 hJ'C hJ'q hz'J).elim

theorem noThreeCover_trialityD4 (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    NoThreeCover (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  have hmodel : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
      .trialityD4 0 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, Or.inr ⟨rfl, ⟨_, hq⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  exact Ronan148L.noThreeCover_of_table rfl rfl
    (CFSG.LieType.Steinberg.CentralExt.GriessExceptional.trialityD4_row hmodel).2

end D4

section Row


theorem rowOf425_d4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    q.p = 2 → RowOf425 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group := by
  intro q hq hq2
  by_cases hf1 : q.exponent = 1
  ·
    refine Ronan148L.rowOf425_of_lie_card ⟨_, hq⟩ ⟨MulEquiv.refl _⟩ (M := 211341312) (B := 596)
      (fun S _ _ ⟨e⟩ => ?_) (by norm_num) (by norm_num) (by decide +kernel)
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨_, hq⟩ S ⟨e⟩]
    show CFSG.Open.orderTrialityD4 q.card ∣ 211341312
    rw [TauCeti.PrimePower.card_def, hq2, hf1]
    decide
  · have hn : 2 ≤ q.exponent := by have := q.exponent_pos; omega
    intro S _ _ _ _ ⟨eSX⟩
    have hTw := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hq hq2 (by decide) eSX
    rw [hq2] at hTw
    have hCh : ChevalleyExceptionalModel S .trialityD4 2 q.exponent :=
      ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, hTw⟩
    obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, -, -, ⟨eC⟩⟩ :=
      Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hCh
    refine row425_of_three eC (NoThreeCover.of_mulEquiv eSX (noThreeCover_trialityD4 q hq))
      (p := 2) (f := q.exponent) ?_ ?_
    · intro X _ ⟨eXS⟩
      have hTw' := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hq hq2 (by decide) (eXS.trans eSX)
      rw [hq2] at hTw'
      exact Or.inr ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, hTw'⟩
    · intro z hz3 hz1 J hJC hJq hJs hzJ
      exact isSLThreePiAt_d4 hK hσ hσ3 hn z hz3 hz1 J hJC hJq hJs hzJ

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
