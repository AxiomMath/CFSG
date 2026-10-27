module

public import CFSG.RankThree.PartTwo.Sec8.HeringPair84UL
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Hering88Cases
import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even
import CFSG.RankThree.PartTwo.Sec8.Hering88NAlphaPrime
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofXNormal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner

public section

namespace CFSG.RankThree.PartTwo.Sec8.Rudvalis88

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LieType.Ree
open Item86ResProof

theorem five_dvd_two_pow_odd_sq_add_one (b : ℕ) : 5 ∣ (2 ^ (2 * b + 1)) ^ 2 + 1 := by
  have h : (2 ^ (2 * b + 1)) ^ 2 + 1 = 4 * 16 ^ b + 1 := by
    rw [← pow_mul, show (2 * b + 1) * 2 = 4 * b + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  rw [h]
  have h16 : 16 ^ b % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem five_dvd_ordTwistedF4 (b : ℕ) : 5 ∣ CFSG.Open.ordTwistedF4 (2 ^ (2 * b + 1)) := by
  have hq : 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [ordTwistedF4_eq_factored' hq]
  exact (((dvd_pow (five_dvd_two_pow_odd_sq_add_one b) two_ne_zero).mul_left _).mul_right _).mul_right
    _

theorem not_isUnitaryTwo_of_isGammaTypeRee {X : Type} [Group X] {n m : ℕ} (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hRee : IsGammaTypeRee X n) : ¬ IsUnitaryTwo X (3 * m) := by
  intro hU
  have hU' : UnitarySig X (3 * m) := by
    rcases hU with he | hS
    · obtain ⟨e⟩ := he
      exact unitarySig_of_projSU (by omega) e
    · exact unitarySig_of_isoSUThree (by omega) hS
  exact (sigF4_of_reeF4 hn hRee).false_of_sigU (sigU_of_unitarySig hU') hn

variable {G : Type} [Group G] [Finite G]

section Ree

theorem five_dvd_card_residual_of_ree {M : Subgroup G} {a : G} {n : ℕ}
    (hRee : IsGammaTypeRee (M ⧸ aschbacherSolvableCore 3 M) n) (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind M a .field ∨ KFacts.InducesStdKind M a .graphField) :
    5 ∣ Nat.card (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)))) := by
  classical
  have haN : a ∈ Subgroup.normalizer (M : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haout : Sec4.InducesOuterTheta a M := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
  have hWM : inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ≤ M :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta M
      (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G))) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  obtain ⟨k₀, hk₀, -, ⟨e₀⟩⟩ := hRee
  have hRT : CFSG.Blueprint.ReeTitsModel (M ⧸ aschbacherSolvableCore 3 M) .twistedF4 2
      (2 * k₀ + 1) :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
  obtain ⟨-, a', ha'1, -, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
  obtain ⟨b', k', _, _, _, hk', -, ⟨φ⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 haout
  rcases Nat.eq_zero_or_pos b' with rfl | hb1
  ·
    have hk2 : Nat.card k' = 2 := by simpa using hk'
    have hS := Hering88N.isSimpleGroup_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
    rw [Hering88N.card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS]
    obtain ⟨hge, hle⟩ := Hering88N.card_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
    have hC : Nat.card (barCentralizer (Subgroup.zpowers a) M) = 35942400 := by
      rw [Nat.card_congr φ.toEquiv,
        Nat.card_congr (ReeTag.reeFixedEquivReeGamma k' 0).symm.toEquiv]
      exact (Hering88N.card_commutator_reeFixed_zero hk2).1
    have hdvd : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M)) ∣
        35942400 := hC ▸ Subgroup.card_dvd_of_le (Item87Proof.residual_le _)
    set N := Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M))
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
  ·
    haveI : Group.IsPerfect (ReeTag.F4.reeGamma k' b') :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hk'⟩
    haveI : IsSimpleGroup (ReeTag.F4.reeGamma k' b') :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb1 hk'
    have hCperf : Group.IsPerfect (barCentralizer (Subgroup.zpowers a) M) :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    have hCres : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) =
        barCentralizer (Subgroup.zpowers a) M :=
      inSubgroup_perfectResidual_of_isPerfect hCperf
    have hS : IsSimpleGroup (inSubgroup perfectResidual
        (barCentralizer (Subgroup.zpowers a) M)) := by
      rw [hCres]
      exact φ.isSimpleGroup
    rw [Hering88N.card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS, hCres,
      card_of_mulEquiv_reeGamma b' k' hk' φ]
    exact five_dvd_ordTwistedF4 b'

end Ree

section Std

variable {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}

theorem sec8Std_of_sec8Pair (h83 : Item83) (h45 : Sec4.Item4_5) (h : Sec8Pair G A c L a b X n) :
    Sec8Std G A c L a b n := by
  have hA81 : Nat.card A = 81 := h.card_eq
  have h27 : 27 < Nat.card A := by rw [hA81]; norm_num
  have hbΓ : IsGammaIndex A L b n := h.isGammaIndex
  have hn1 : 1 ≤ n := one_le_of_isGammaIndex hbΓ
  obtain ⟨A₀, d₀, n₀, hD⟩ := h83 G A c L a h.toHyp81 h27
  have hnn : n = n₀ := eq_of_isGammaType hn1 hD.odd.pos (isGammaType_of_isGammaIndex hbΓ)
    (isGammaType_of_data83 hD)
  subst hnn
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.mem_partTwoF.1 h.mem_A
      h.ne_one L h.mem_thetaComponentsAt
  have hbA : b ∈ A := hbΓ.1
  have hEv : KF89D4SecondCentEven := kF89D4SecondCentEven_of_y0 kF89D4SecondCentY0Even_holds
  exact
    { toHyp81 := h.toHyp81
      data83 :=
        { le_normalizer := fun u hu =>
            Item812Res2.mem_normalizer_zpowers_of_commute (hAc u hu c h.mem_A)
          c_mem := h.mem_A
          a_mem := h.a_mem
          isElemAbelian := h.mem_partTwoF.1
          card_eq := hA81
          sectionCentralizer_eq := h.sectionCentralizer_eq
          d_mem := hbA
          d_ne_one := hbΓ.2.1
          innerDiag := Item812Res8.innerDiag_of_isGammaIndex hEv hbΓ (hAL hbA)
            (h.mem_partTwoF.1.2 b hbA)
          odd := hD.odd
          ne_bot := Item812Res7.ne_bot_of_isGammaIndex hbΓ hD.odd
          cases := Item812Res7.cases83_of_cases83 hD.cases hbΓ h.gTwo }
      gTwo := h.gTwo }

theorem partner_isGammaIndex_of_projSL (h83 : Item83) (h45 : Sec4.Item4_5)
    (h418 : Item418Theta) (hL82 : Item82TwoList) (h : Sec8Pair G A c L a b X n)
    (hK : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n)))) :
    IsGammaIndex A X c n := by
  have hS := sec8Std_of_sec8Pair h83 h45 h
  have hb : b ∈ Subgroup.closure ({c, b} : Set G) := Subgroup.subset_closure (by simp)
  by_cases hU : ∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m
  · exact Item8KFacts3.pair84GammaUL_of' h45 h418 hL82 G A c L a b n hS b X hb h.pairRel hU
      h.not_unitary
  · push Not at hU
    exact Item84KFacts4.pair84GammaNL_of' h45 h418 hL82 G A c L a b n hS hU hK b X hb h.pairRel
      h.not_unitary

end Std

section Case1

variable {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}

theorem false_of_ree_of_case1 (h : Sec8Pair G A c L a b X n)
    (hRee : IsGammaTypeRee (L ⧸ aschbacherSolvableCore 3 L) n) {Y : Subgroup G}
    (hIY : sec8I L a ≤ Y) {x : G} {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m)
    (hc1 : Case83One Y x A₀ d' m) : False := by
  classical
  have hn1 : 1 ≤ n := one_le_of_isGammaIndex h.isGammaIndex
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 :=
    not_isUnitaryTwo_of_isGammaTypeRee (m := 1) hn1 le_rfl hRee
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  have h5 := five_dvd_card_residual_of_ree hRee ha3 h.inducesStdKind
  rw [← hIdef] at h5
  exact Hering88N.five_not_dvd_card_of_case1 hodd hc1.1
    ((h5.trans (Hering88N.card_quot_theta_dvd_card_imageModTheta hIY)).trans
      (Subgroup.card_subgroup_dvd_card _))

end Case1

end CFSG.RankThree.PartTwo.Sec8.Rudvalis88

end
