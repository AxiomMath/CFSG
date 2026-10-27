module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCStep0C
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLinkFacts
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.RankThree.PartTwo.KFacts.K71Sp4
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec8.HeringD4Tools
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofUnitary
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp projSU projImage)
open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley
open Hering88N


structure YbarFacts (Q : Type) [Group Q] : Prop where
  center : ∀ z : Q, (∀ y : Q, z * y = y * z) → z = 1
  cyc : KFacts.OutThreeCyclic Q
  link : (InnerFacts Q ∧ ¬ 25 ∣ Nat.card Q) ∨ PerfFacts Q

theorem ybarFacts_of {Q : Type} [Group Q] (hY : YbarOne Q) : YbarFacts Q := by
  rcases hY with hD | hG | hSp | hR
  ·
    obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    refine ⟨center_trivial_of_eq_bot (Hering88F.center_eq_bot_of_case1 (Or.inl hD)),
      (KFacts.outThreeCyclic_triality hm1 hK hσ).of_mulEquiv e,
      Or.inl ⟨InnerFacts.of_mulEquiv e (innerFacts_triality hK hσ), fun h25 => ?_⟩⟩
    exact Hering88N.five_not_dvd_card_of_case1 odd_one (Or.inl hD) ((by norm_num : 5 ∣ 25).trans h25)
  ·
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := id hG
    have hK8 : Nat.card K = 2 ^ 3 := by rw [hK]
    have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK8
    have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
    have hK4 : 4 ≤ Nat.card K := by rw [hK8]; norm_num
    refine ⟨center_trivial_of_eq_bot (Hering88F.center_eq_bot_of_case1 (Or.inr hG)),
      (KFacts.outThreeCyclic_g2 K hK3 hK4).of_mulEquiv e,
      Or.inl ⟨InnerFacts.of_mulEquiv e (innerFacts_g2 hK8), fun h25 => ?_⟩⟩
    exact Hering88N.five_not_dvd_card_of_case1 odd_one (Or.inr hG) ((by norm_num : 5 ∣ 25).trans h25)
  ·
    obtain ⟨e⟩ := hSp
    set e' : Q ≃* StatedProj (StatedSp 2 (GaloisField 2 (3 * 1))) :=
      e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with he'
    refine ⟨center_trivial_of_mulEquiv e' center_statedProj_sp4,
      (KFacts.outThreeCyclic_psp4Even (GaloisField 2 (3 * 1))).of_mulEquiv e',
      Or.inl ⟨InnerFacts.of_mulEquiv e innerFacts_projSp_eight, fun h25 => ?_⟩⟩
    have hc : Nat.card Q = 1056706560 := by
      rw [Nat.card_congr e.toEquiv]
      exact Item812Res2.card_projSp_two_three
    rw [hc] at h25
    norm_num at h25
  ·
    obtain ⟨k, K, _, _, _, hkm, hK, ⟨e⟩⟩ := hR
    obtain rfl : k = 1 := by omega
    have hK' : Nat.card K = 2 ^ (2 * 1 + 1) := by rw [hK]
    exact ⟨center_trivial_of_mulEquiv e (center_trivial_of_eq_bot
        (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial 1 K hK')),
      (KFacts.outThreeCyclic_largeRee le_rfl hK').of_mulEquiv e,
      Or.inr (PerfFacts.of_mulEquiv e (perfFacts_reeGamma hK'))⟩

section Outer

variable {G : Type} [Group G] [Finite G]

theorem outer_residual_triality {Y : Subgroup G} {d : G}
    (hD : IsoTrialityD4 (Y ⧸ aschbacherSolvableCore 3 Y) 1) (hd3 : d ^ 3 = 1)
    (hout : Sec4.InducesOuterTheta d Y) :
    inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) Y) = ⊥ ∨
      ∀ y : barCentralizer (Subgroup.zpowers d) Y, y ^ 3 = 1 →
        y ∈ perfectResidual (barCentralizer (Subgroup.zpowers d) Y) := by
  classical
  obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
  obtain ⟨hN, -⟩ := id hout
  set α := KFacts.inducedAutHom Y e ⟨d, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one Y e hN hd3
  have hαout : ¬ KFacts.IsInnerAut α := (KFacts.not_isInnerAut_inducedAutHom_iff Y e hN).mpr hout
  have hfix := KFacts.map_barCentralizer_eq hN e (Sec4.autFix α) (fun z => Iff.rfl)
  set C := barCentralizer (Subgroup.zpowers d) Y with hC
  set φ : C ≃* Sec4.autFix α := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hfix) with hφ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv le_rfl hK hσ hα3 hαout
    with ⟨β, hβ⟩ | he₂
  · exact Or.inr (Item8KFacts2Proof.residualFacts_of_isoGTwoEven le_rfl
      (KFacts.isoGTwoEven_barCentralizer_of_conj_fieldActor le_rfl hK hσ e hN β hβ)).1
  · left
    obtain ⟨e₂⟩ := he₂
    obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds 1 odd_one K σ hK hσ
    have hPi : Sec4.PiField false 2 1 F := ⟨Nat.prime_two, le_rfl, hF⟩
    haveI := Sec13.isSolvable_projImage_glPi_two hPi (by norm_num)
    have ε := φ.trans (e₂.trans e₃)
    exact HeringD4.inSubgroup_perfectResidual_eq_bot_of_solvable C
      (solvable_of_solvable_injective (f := ε.toMonoidHom) ε.injective)

theorem outer_residual {Y : Subgroup G} {d : G} (hY : YbarOne (Y ⧸ aschbacherSolvableCore 3 Y))
    (hd3 : d ^ 3 = 1) (hout : Sec4.InducesOuterTheta d Y) :
    inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) Y) = ⊥ ∨
      ∀ y : barCentralizer (Subgroup.zpowers d) Y, y ^ 3 = 1 →
        y ∈ perfectResidual (barCentralizer (Subgroup.zpowers d) Y) := by
  rcases hY with hD | hG | hSp | hR
  · exact outer_residual_triality hD hd3 hout
  ·
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
    obtain ⟨-, k, _, _, hk, ⟨φ⟩⟩ := KFacts.barCentralizer_mulEquiv_g2 (n := 1) one_ne_zero hK hd3
      hout e
    exact Or.inr (Item8KFacts2Proof.residualFacts_of_isoGTwoEven le_rfl
      ⟨k, inferInstance, inferInstance, hk, ⟨φ⟩⟩).1
  ·
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero hd3 hout hSp
    exact Or.inr (Item8KFacts2Proof.ResidualFacts.of_mulEquiv ι
      (Item8KFacts2Proof.residualFacts_projSp le_rfl)).1
  ·
    obtain ⟨k, K, _, _, _, hkm, hK, ⟨e⟩⟩ := hR
    have hk1 : 1 ≤ k := by omega
    have hK' : Nat.card K = 2 ^ (2 * k + 1) := by rw [hK, hkm]
    obtain ⟨b', k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk1 hK' e hd3 hout
    exact Or.inr (Item8KFacts2Proof.ResidualFacts.of_mulEquiv φ
      (Item8KFacts2Proof.residualFacts_reeGamma hk₀)).1

end Outer

theorem iside_ree {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    (hRee : IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) 1) :
    25 ∣ Nat.card (sec8I L a ⧸ aschbacherSolvableCore 3 (sec8I L a)) := by
  classical
  have hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    (Item86ResProof.sigF4_of_reeF4 le_rfl hRee).not_isUnitaryTwo le_rfl 3
  have ha3 : a ^ 3 = 1 := (Hering88C.pair_commute_pow_three h).2 a h.a_mem
  have hk := h.inducesStdKind
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have haout : Sec4.InducesOuterTheta a L := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h' (by decide)
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  rw [hIdef]
  have hWM : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ L :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G))) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
  have hRT : CFSG.Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2
      (2 * k₀ + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
  obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
  obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 haout
  obtain rfl : b' = 0 := by omega
  have hk2 : Nat.card k' = 2 := by simpa using hk'
  have hS := isSimpleGroup_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
  have hN := card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS
  obtain ⟨hge, hle⟩ := card_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
  have hC : Nat.card (barCentralizer (Subgroup.zpowers a) L) = 35942400 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr (ReeTag.reeFixedEquivReeGamma k' 0).symm.toEquiv]
    exact (card_commutator_reeFixed_zero hk2).1
  have hdvd : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L)) ∣
      35942400 := hC ▸ Subgroup.card_dvd_of_le (Item87Proof.residual_le _)
  rw [hN]
  set N := Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L))
  obtain ⟨i, hi⟩ := hdvd
  have hi3 : i < 3 := by
    by_contra h3
    push Not at h3
    have : N * 3 ≤ N * i := Nat.mul_le_mul_left N h3
    omega
  interval_cases i
  · omega
  · have hN1 : N = 35942400 := by omega
    rw [hN1]
    norm_num
  · have hN2 : N = 17971200 := by omega
    rw [hN2]
    norm_num

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
