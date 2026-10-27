module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Pure
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarD4Cent
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (ordTrialityD4)

namespace Item1120V0Bar

section Main


theorem v0FamD4 : V0FamD4 := by
  intro Z _ _ hZq α σ J ξ γ hα3 hJα hJT hξJ hξsyl hξ9 hσ3 hσα hσJ hσξ hγ3 hP3 hLB
  obtain ⟨n, qT, hq, hp2, hn, ⟨e0⟩⟩ := hZq
  have hn1 : 1 ≤ n := by
    rw [← hn]
    exact qT.exponent_pos
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_trialityD4 qT hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hcomm : Nonempty (Z ≃* _root_.commutator Z) :=
    nonempty_mulEquiv_commutator_of_isPerfect hperf
  have hZeven : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid), q'.p = 2 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨qT, hq, hp2, ⟨e0⟩⟩, hcomm⟩
  have hZ' : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid), q'.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨qT, hq, by rw [hp2]; decide, ⟨e0⟩⟩, hcomm⟩
  have hZc : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.trialityD4 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨qT, hq, ⟨e0⟩⟩, hcomm⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424D4Even_holds Z hZeven α J hα3 hno hJα hJT
  obtain ⟨z, rfl⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := hα3
  have hcen : Subgroup.center Z = ⊥ := KS11Lie3Proof.center_eq_bot_d4 Z hZc
  have hcent : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (MonoidHom.mem_ker.mp hx)
    rw [hcen, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  have hz3' : z ^ 3 = 1 := hcent (by rw [map_pow, hz3, map_one])
  obtain ⟨K, _, _, σK, hKcard, hσK, ⟨E⟩⟩ :=
    Item1118Res3Proof.exists_d4_model_pow e0 hcomm.some
  rw [hp2, hn] at hKcard hσK
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hσK3 : σK ^ 3 = 1 := by
    apply RingEquiv.ext
    intro c
    haveI : Fintype K := Fintype.ofFinite K
    have h1 : σK (σK (σK c)) = c := by
      rw [hσK, hσK, hσK, ← pow_mul, ← pow_mul]
      have h2 : 2 ^ n * (2 ^ n * 2 ^ n) = Fintype.card K := by
        rw [← Nat.card_eq_fintype_card, hKcard]
        ring
      rw [h2, FiniteField.pow_card]
    exact h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hsimple : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σK.toRingHom) :=
    isSimpleGroup_graphFixedRootGroup_d4 (ℓ := 2) hn1 hKcard hσK
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    have hT := KS11Lie2Proof.hasType424_of_mem hJα hJT
    rw [map_one, Sec4.Item426.fixSub_one] at hT
    exact KS11Lie4Proof.not_hasType424_d4 hσK3
      ((hT.of_mulEquiv Subgroup.topEquiv).of_mulEquiv E)
  have hez3 : E z ^ 3 = 1 := by rw [← map_pow, hz3', map_one]
  have hez1 : E z ≠ 1 := fun h => hz1 (E.injective (h.trans (map_one E).symm))
  obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ n) σK hKcard hσK h3 (E z) hez3 hez1
  set e' : Z ≃* graphFixedRootGroup TwistTag.D4 K σK.toRingHom := E.trans (MulAut.conj g)
    with he'
  have hmem : e' z ∈ KS11Lie4Proof.d4ShortSL2 K σK.toRingHom ∨ e' z ∈ Subgroup.centralizer
      ((KS11Lie4Proof.d4ShortSL2 K σK.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) := hg
  obtain ⟨hzM, hB⟩ := KS11Lie4Proof.threeBAt_d4 KS11Lie6Proof.d4ThreeACent_holds
    KS11Lie6Proof.d4ThreeBCent_holds hKcard hσK h3 hσK3 e' hz3' hz1 hmem hJα hJT
  have hJS : J = (KS11Lie4Proof.d4ShortSL2 K σK.toRingHom).comap e'.toMonoidHom :=
    hB.eq hJα
  have hθc := hB.thetaCentral hJα
  have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJα
  have hσfix : ∀ j ∈ J, σ j = j := fixes_of_mem_theta hJp σ hθc hσJ
  have hout : σ ∈ (MulAut.conj : Z →* MulAut Z).range :=
    KS11Lie6Proof.centJ119D4Out_holds Z hZ' z σ J hz3 hσ3 hσα.symm hJα hJT hσfix
  obtain ⟨b, rfl⟩ := hout
  have hb3 : ∃ k : ℕ, b ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hσ3
    refine ⟨k, hcent ?_⟩
    rw [map_pow, hk, map_one]
  have hbJ : ∀ j ∈ J, b * j = j * b := by
    intro j hj
    have h1 := hσfix j hj
    rw [MulAut.conj_apply] at h1
    calc b * j = (b * j * b⁻¹) * b := by group
      _ = j * b := by rw [h1]
  have hbξ : b * ξ = ξ * b := hcent (by rw [map_mul, map_mul]; exact hσξ)
  have hξ3 : ∃ k : ℕ, ξ ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hξsyl.isPGroup ⟨ξ, Subgroup.mem_zpowers ξ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥ :=
    zpowers_inf_zpowers_eq_bot hJT hξJ hξ3 hbJ hb3
  obtain ⟨k, _, _, hkchar, hkcard, ⟨Φ⟩⟩ := nonempty_mulEquiv_centralizer_d4ShortSL2
    (K := K) (σ := σK) (ℓ := 2) (f := n) hn1 (by norm_num) hKcard hσK
  set CS := Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σK.toRingHom :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) :
      Set (graphFixedRootGroup TwistTag.D4 K σK.toRingHom)) with hCS
  set M : Subgroup Z := CS.comap e'.toMonoidHom with hM
  have hMeq : M ≃* Matrix.SpecialLinearGroup (Fin 2) k :=
    (G2eComapMulEquiv e' CS).trans Φ.symm
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) k) := Finite.of_equiv M hMeq.toEquiv
  have hM3 : ∀ P : Sylow 3 M, IsCyclic P := fun P =>
    KS11LieProof.isCyclic_sylow_of_mulEquiv hMeq.symm
      (fun Q => isCyclic_sylow_three_sl2 (by rw [ringChar.eq k 2]) Q) P
  have hzM' : z ∈ M := hzM
  obtain ⟨ζ, hζM, hzζ, hζ3, hζord⟩ := exists_big_elt_of_cyclic_sylow hM3 hzM' hz3'
  have hζJ : ∀ j ∈ J, ζ * j = j * ζ := by
    intro j hj
    have hj' : e' j ∈ KS11Lie4Proof.d4ShortSL2 K σK.toRingHom := by
      rw [hJS] at hj
      exact hj
    have hζ' : e' ζ ∈ CS := hζM
    have h1 := Subgroup.mem_centralizer_iff.mp hζ' (e' j) hj'
    apply e'.injective
    rw [map_mul, map_mul]
    exact h1.symm
  have hle := hLB ζ hζ3
    (by
      rw [MulAut.conj_apply]
      calc z * ζ * z⁻¹ = ζ * z * z⁻¹ := by rw [hzζ]
        _ = ζ := by group)
    (fun j hj => by
      calc ζ * j * ζ⁻¹ = j * ζ * ζ⁻¹ := by rw [hζJ j hj]
        _ = j := by group)
  rw [orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent ζ,
    orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent b] at hle
  have hcardM : Nat.card M = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr hMeq.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      hkcard]
  have hζo : orderOf ζ = 3 ^ ((2 ^ n) ^ 2 - 1).factorization 3 := by
    rw [hζord, hcardM, factorization_card_SL2 (by omega) hq2 h3]
  have hcardJ : Nat.card J = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hJS, Nat.card_congr (G2eComapMulEquiv e'
      (KS11Lie4Proof.d4ShortSL2 K σK.toRingHom)).toEquiv]
    exact KS11Lie4Proof.card_d4ShortSL2 hσK3
  have hξord : orderOf ξ = 3 ^ (((2 ^ n) ^ 2 - 1).factorization 3 + 1) := by
    rw [orderOf_eq_three_pow_of_isSylowOf hξsyl, hcardJ, hKcard,
      factorization_card_SL2_cube hq2 h3]
  have hcardZ : Nat.card Z = ordTrialityD4 (2 ^ n) := by
    rw [Nat.card_congr e0.toEquiv, KSListsProof.card_trialityD4_carrier qT hq,
      TauCeti.PrimePower.card_def, hp2, hn]
  have hcard : 3 ^ (Nat.card Z).factorization 3 ≤ 3 * (orderOf b * orderOf ξ) := by
    rw [hcardZ, factorization_ordTrialityD4 hq2 h3]
    have hbge : 3 ^ ((2 ^ n) ^ 2 - 1).factorization 3 ≤ orderOf b := by
      rw [← hζo]
      exact hle
    calc 3 ^ (2 * ((2 ^ n) ^ 2 - 1).factorization 3 + 2)
        = 3 * (3 ^ ((2 ^ n) ^ 2 - 1).factorization 3 *
            3 ^ (((2 ^ n) ^ 2 - 1).factorization 3 + 1)) := by
          rw [pow_succ, two_mul, pow_add]
          ring
      _ ≤ 3 * (orderOf b * orderOf ξ) := by
          rw [hξord]
          exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul hbge le_rfl)
  exact v0_conclusion_of_inner hcent hP3 hbξ hdisj hcard

end Main

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
