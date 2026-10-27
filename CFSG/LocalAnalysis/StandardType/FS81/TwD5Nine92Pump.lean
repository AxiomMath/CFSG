module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Layer
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92JFacts
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Syl
public import CFSG.Mathlib.GroupTheory.PComponentProductCard
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate709602
public import Certificates.Certificate709610

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

theorem nineJ_glapComponent_centralizer_inf {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hchar : IsCharTwoType G)
    (hfus : Fus42 B b₀) :
    GLAPComponent 3 (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer ({B.b 2} : Set G)) (nineJ K (B.b 2)) := by
  set J : Subgroup G := nineJ K (B.b 2) with hJ
  set Y : Subgroup G :=
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({B.b 2} : Set G) with hY
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal := hstd.2.1.2.2.1
  have hJY : J ≤ Y :=
    (Subgroup.commutator_le_self _).trans (le_inf (inf_le_left.trans hKC) inf_le_right)
  have hJnorm : (J.subgroupOf Y).Normal := nineJ_subgroupOf_normal hKC hKn
  have hJcomp : CFSG.Assembly.IsComponentOf J Y :=
    ⟨hJY, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJY).mpr hJnorm.isSubnormal,
      isQuasisimple_nineJ hstd hB hrec⟩
  have hJO : ¬ J ≤ CFSG.Open.lBalancePrimeCore 3 Y :=
    nineJ_not_le_primeCore hstd hB hrec hchar hfus Y
  have hL : CFSG.Open.lBalanceIsPComponent 3 Y J :=
    CFSG.StandardType.lBalanceIsPComponent_of_isComponentOf hJcomp hJO
  exact (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff).2 ⟨hJY, hL⟩

theorem le_glapLayer_centralizer_of_stdTwD5 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hchar : IsCharTwoType G)
    (hfus : Fus42 B b₀) :
    K ≤ GLAPLayer 3 (Subgroup.centralizer ({b₀} : Set G)) := by
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal := hstd.2.1.2.2.1
  have hmark : IsTwD5 K := hstd.2.1.2.2.2.2.1
  have hKq : CFSG.Assembly.IsQuasisimple K := by
    obtain ⟨hperf, lab, hlab, R, _, I, F, θ, hRsimple, -, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists hmark
    exact ⟨hperf, @MulEquiv.isSimpleGroup _ _ _ _ hRsimple θ⟩
  let C : Subgroup G := Subgroup.centralizer ({b₀} : Set G)
  have hKcomp : CFSG.Assembly.IsComponentOf K C :=
    ⟨hKC, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hKC).mpr hKn.isSubnormal, hKq⟩
  have h3K : 3 ∣ Nat.card K := by
    have h6 : 6 ∣ Nat.card ↥(nineJ K (B.b 2)) := six_dvd_card_nineJ hstd hB hrec hchar hfus
    have hJK : nineJ K (B.b 2) ≤ K := (Subgroup.commutator_le_self _).trans inf_le_left
    exact (dvd_trans (by norm_num : 3 ∣ 6) h6).trans (Subgroup.card_dvd_of_le hJK)
  have hKnot : ¬ K ≤ CFSG.Open.lBalancePrimeCore 3 C := by
    intro hle
    have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.lBalancePrimeCore 3 C : Subgroup G)) :=
      @CFSG.ComponentClassification.LBalance.primeCore_coprime G _ 3 ⟨Nat.prime_three⟩
        (inferInstance : Finite G) C
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
      (h3K.trans (Subgroup.card_dvd_of_le hle))
  have hL : CFSG.Open.lBalanceIsPComponent 3 C K :=
    CFSG.StandardType.lBalanceIsPComponent_of_isComponentOf hKcomp hKnot
  have hcomp : GLAPComponent 3 C K :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff).2 ⟨hKC, hL⟩
  rw [GLAPLayer]
  exact le_sSup hcomp

theorem nineJ_glapComponent_layerCentralizer {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hchar : IsCharTwoType G)
    (hfus : Fus42 B b₀) :
    GLAPComponent 3 (GLAPLayer 3 (Subgroup.centralizer ({b₀} : Set G)) ⊓
      Subgroup.centralizer ({B.b 2} : Set G)) (nineJ K (B.b 2)) := by
  have hY := nineJ_glapComponent_centralizer_inf hstd hB hrec hchar hfus
  have hKW : K ≤ GLAPLayer 3 (Subgroup.centralizer ({b₀} : Set G)) :=
    le_glapLayer_centralizer_of_stdTwD5 hstd hB hrec hchar hfus
  have hJW : nineJ K (B.b 2) ≤ GLAPLayer 3 (Subgroup.centralizer ({b₀} : Set G)) ⊓
      Subgroup.centralizer ({B.b 2} : Set G) :=
    le_inf ((Subgroup.commutator_le_self _).trans (inf_le_left.trans hKW))
      ((Subgroup.commutator_le_self _).trans inf_le_right)
  refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down
    Nat.prime_three hY hJW ?_
  exact le_inf (inf_le_left.trans (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_le 3 _))
    inf_le_right

theorem nineJ_statedClassicalModel_two_and_center {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    StatedClassicalModel ↥(nineJ K (B.b 2)) .POmegaPlus 4 2 1 ∧
      Subgroup.center ↥(nineJ K (B.b 2)) = ⊥ := by
  classical
  obtain ⟨φ, B', F, j, hB', hjinj, hj, heven, hU, hφB'⟩ :=
    exists_frame_coordinates_of_recOutTwD5 hstd hB hrec
  let i₂ : Fin 5 := 1
  let a : G := B.b i₂.succ
  have haK : a ∈ K := hB.2.2 _ (Fin.succ_ne_zero i₂)
  have hx : ((φ ⟨a, haK⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) = frameRot F (j i₂) ∨
      ((φ ⟨a, haK⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
        (frameRot F (j i₂))⁻¹ :=
    phi_eq_or_eq_inv_frameRot hB' hj hφB' i₂ haK
  obtain ⟨hx3, hxU, hxfix⟩ := frameRot_facts_of_eq_or_eq_inv F (j i₂) hx
  have hAOrth : Subgroup.map ((orthDerived Q5).subtype.comp φ.toMonoidHom)
      ((E ⊓ K).subgroupOf K) ≤ orthDerived Q5 := by
    rintro _ ⟨k, -, rfl⟩
    exact (φ k).2
  have hAO : Subgroup.map ((orthDerived Q5).subtype.comp φ.toMonoidHom)
      ((E ⊓ K).subgroupOf K) ≤ TauCeti.QuadraticMap.orthogonalGroup Q5 :=
    hAOrth.trans (Subgroup.commutator_le_self _)
  obtain ⟨U, Ψ, hU2, hP, hdimW, hWplus, hT⟩ :=
    exists_nineJ_restrict_plus (φ := φ) (F := F) (j := j) hAO hU haK hx3 hxU hxfix
  obtain ⟨T3, hT3, hTs⟩ := hT
  obtain ⟨eW⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hP (n := 4)
    (by rw [hdimW]) hWplus
  have hLie := CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus (m := 4) (f := 1)
    (by norm_num) (by norm_num) (by simp) eW Ψ
  have hClass : StatedClassicalModel ↥(nineJ K a) .POmegaPlus 4 2 1 :=
    (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hLie
  have hne : ∃ v : ↥(perpOf Q5 U), (Q5.restrict (perpOf Q5 U)) v ≠ 0 :=
    exists_map_ne_zero_of_polar_ne_zero (Q := Q5)
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_of_nondegenerate hP) hT3 hTs
  have hZ : Subgroup.center ↥(nineJ K a) = ⊥ := by
    have h1 := Subgroup.map_center_eq Ψ
    rw [CFSG.SeitzReduction.OmegaPilot.center_orthDerived_eq_bot' hP ⟨T3, hT3, hTs⟩ hne] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ Ψ.injective).mp h1
  exact ⟨hClass, hZ⟩

theorem center_eq_bot_of_d4two_quotient
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hodd : Odd (Nat.card (Subgroup.center X))) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    (e : X ⧸ Subgroup.center X ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K))) :
    Subgroup.center X = ⊥ := by
  have hK' : Nat.card K = 2 ^ 1 := by simpa using hK
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK'
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_split_orthogonal
    (n := 4) (by norm_num) hodd e

theorem nineJ_primeCore_eq_bot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    GLAPPrimeCore 3 ↥(nineJ K (B.b 2)) = ⊥ := by
  have : IsSimpleGroup ↥(nineJ K (B.b 2)) := nineJ_simple_of_recOutTwD5 hstd hB hrec
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥(nineJ K (B.b 2))) with
    hbot | htop
  · exact hbot
  · exfalso
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥(nineJ K (B.b 2)))) :=
      CFSG.pPrimeCore_coprime_card
    have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥(nineJ K (B.b 2))) := by
      rw [htop, Subgroup.card_top]
      exact three_dvd_card_nineJ hstd hB hrec
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3

theorem three_pow_five_dvd_card_nineJ {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (5 + 1)} (hstd : StdTwD5 b₀ K E)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    3 ^ 5 ∣ Nat.card ↥(nineJ K (B.b 2)) := by
  have hJmodel : StatedClassicalModel ↥(nineJ K (B.b 2)) .POmegaPlus 4 2 1 :=
    (nineJ_statedClassicalModel_two_and_center hstd hB hrec).1
  have hord : Nat.card ↥(nineJ K (B.b 2)) = ordD 4 (2 ^ 1) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hJmodel).2.2.2.1 rfl
  rw [hord]
  decide

theorem center_quotient_eq_bot_of_three_component
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)}
    (hstd : StdTwD5 b₀ K E) (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    {M : Subgroup G} (hM : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) M)
    {Z : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)} [Z.Normal]
    (hZc : Z ≤ Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M))
    (e0 : ↥(nineJ K (B.b 2)) ≃* (↥M ⧸ GLAPPrimeCore 3 ↥M) ⧸ Z) :
    Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ := by
  classical
  let Q : Type := ↥M ⧸ GLAPPrimeCore 3 ↥M
  have hJdata := nineJ_statedClassicalModel_two_and_center hstd hB hrec
  have hJmodel : StatedClassicalModel ↥(nineJ K (B.b 2)) .POmegaPlus 4 2 1 := hJdata.1
  have hZeq : Z = Subgroup.center Q :=
    CFSG.GroupTheory.eq_center_of_simple_quotient hJdata.2 hZc e0
  have hPerfQ : Group.IsPerfect Q := by
    have hBar : Group.IsPerfect ↥(barX 3 (Subgroup.centralizer ({B.b 2} : Set G)) M) := by
      rw [Group.isPerfect_def]
      exact hM.2.2.1.2.2.1
    have := hBar
    exact Group.IsPerfect.ofSurjective
      (f := (quotEquivBarX Nat.prime_three hM.1 hM.2.1).symm.toMonoidHom)
      (quotEquivBarX Nat.prime_three hM.1 hM.2.1).symm.surjective
  have hQcore : GLAPPrimeCore 3 Q = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥M) 3
  have hOddCenter : Odd (Nat.card (Subgroup.center Q)) := by
    have hP := CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot
      Nat.prime_three hQcore
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
    rw [hn]
    exact Odd.pow (n := n) (show Odd (3 : ℕ) by norm_num)
  obtain ⟨-, Kf, hKf, hKfFin, hKfcard, hIso⟩ := hJmodel
  let : Field Kf := hKf
  let : Finite Kf := hKfFin
  obtain ⟨eJ⟩ := hIso
  have hKf2 : Nat.card Kf = 2 := by simpa using hKfcard
  have e : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedOmega (StatedQuadPlus 4 Kf)) :=
    (QuotientGroup.quotientMulEquivOfEq hZeq.symm).trans (e0.symm.trans eJ)
  exact center_eq_bot_of_d4two_quotient hOddCenter hKf2 e

theorem three_pow_ten_dvd_card_sup_conj {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {B : Basis3 G (5 + 1)} {t : G} (ht : t ∈ Subgroup.centralizer ({B.b 2} : Set G))
    {M : Subgroup G} (hM : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) M)
    (hMne : GLBConj t M ≠ M)
    (hZ : Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥)
    (hcardQ : Nat.card (↥M ⧸ GLAPPrimeCore 3 ↥M) = Nat.card ↥(nineJ K (B.b 2)))
    (h3pow5 : 3 ^ 5 ∣ Nat.card ↥(nineJ K (B.b 2))) :
    3 ^ 10 ∣ Nat.card ↥(M ⊔ GLBConj t M) ∧
      M ⊔ GLBConj t M ≤ Subgroup.centralizer ({B.b 2} : Set G) := by
  have htb : t * B.b 2 = B.b 2 * t := Subgroup.mem_centralizer_singleton_iff.mp ht
  have hHconj : GLBConj t (Subgroup.centralizer ({B.b 2} : Set G)) =
      Subgroup.centralizer ({B.b 2} : Set G) := by
    have h := centralizer_singleton_gLBConj t (B.b 2)
    have ht' : t⁻¹ * (B.b 2) * t = B.b 2 := by
      calc t⁻¹ * (B.b 2) * t = t⁻¹ * ((B.b 2) * t) := by group
        _ = t⁻¹ * (t * (B.b 2)) := by rw [← htb]
        _ = B.b 2 := by group
    rw [ht'] at h
    exact h.symm
  have hM' : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) (GLBConj t M) := by
    have h := glaPComponent_gLBConj hM t
    rwa [hHconj] at h
  have hprod := CFSG.GroupTheory.card_quotient_mul_card_quotient_dvd_card_sup
    hM hM' (Ne.symm hMne) hZ
  have hQ'card : Nat.card (↥(GLBConj t M) ⧸ GLAPPrimeCore 3 ↥(GLBConj t M)) =
      Nat.card (↥M ⧸ GLAPPrimeCore 3 ↥M) :=
    (Nat.card_congr (CFSG.LocalAnalysis.GLTheoremB.conjQuotEquiv 3 t M).toEquiv).symm
  have hpow10 : 3 ^ 10 ∣ Nat.card ↥(M ⊔ GLBConj t M) := by
    rw [hQ'card, hcardQ] at hprod
    have h55 : 3 ^ 5 * 3 ^ 5 ∣ Nat.card ↥(nineJ K (B.b 2)) * Nat.card ↥(nineJ K (B.b 2)) :=
      Nat.mul_dvd_mul h3pow5 h3pow5
    rw [show (3 : ℕ) ^ 10 = 3 ^ 5 * 3 ^ 5 by norm_num]
    exact h55.trans hprod
  exact ⟨hpow10, sup_le hM.1 hM'.1⟩

theorem false_of_three_component_diagonal
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    {M : Subgroup G} (hM : GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) M)
    {t : G} (ht : t ∈ Subgroup.centralizer ({B.b 2} : Set G)) (hMne : GLBConj t M ≠ M)
    {Z : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)} [hZn : Z.Normal]
    (hZc : Z ≤ Subgroup.center (↥M ⧸ GLAPPrimeCore 3 ↥M))
    (hZiso : Nonempty ((↥(nineJ K (B.b 2)) ⧸ GLAPPrimeCore 3 ↥(nineJ K (B.b 2))) ≃*
      ((↥M ⧸ GLAPPrimeCore 3 ↥M) ⧸ Z))) : False := by
  classical
  let J : Subgroup G := nineJ K (B.b 2)
  let Q : Type := ↥M ⧸ GLAPPrimeCore 3 ↥M
  have hJcenter : Subgroup.center ↥J = ⊥ :=
    (nineJ_statedClassicalModel_two_and_center hstd hB hrec).2
  have hJcore : GLAPPrimeCore 3 ↥J = ⊥ := nineJ_primeCore_eq_bot hstd hB hrec
  obtain ⟨eJZ⟩ := hZiso
  have eJZ' : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* (Q ⧸ Z) := eJZ
  have e0 : ↥J ≃* Q ⧸ Z :=
    (QuotientGroup.quotientBot).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hJcore).symm.trans eJZ')
  have hQcenter : Subgroup.center Q = ⊥ :=
    center_quotient_eq_bot_of_three_component hstd hB hrec hM hZc e0
  have hZeq : Z = Subgroup.center Q := CFSG.GroupTheory.eq_center_of_simple_quotient hJcenter hZc e0
  have hZbot : Z = ⊥ := by rw [hZeq, hQcenter]
  have hcardQ : Nat.card Q = Nat.card ↥J := by
    have h1 : Nat.card Q = Nat.card (Q ⧸ (⊥ : Subgroup Q)) :=
      (Nat.card_congr QuotientGroup.quotientBot.toEquiv).symm
    have h2 : Nat.card (Q ⧸ (⊥ : Subgroup Q)) = Nat.card (Q ⧸ Z) :=
      (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZbot)).symm
    exact h1.trans (h2.trans (Nat.card_congr e0.toEquiv).symm)
  have h3pow5 : 3 ^ 5 ∣ Nat.card ↥J := three_pow_five_dvd_card_nineJ hstd hB hrec
  obtain ⟨hpow10, hHle⟩ :=
    three_pow_ten_dvd_card_sup_conj ht hM hMne hQcenter hcardQ h3pow5
  have h9 : 3 ^ 9 ∣ Nat.card ↥(M ⊔ GLBConj t M) :=
    (show 3 ^ 9 ∣ 3 ^ 10 by norm_num).trans hpow10
  exact not_three_pow_nine_dvd_card_of_le_centralizer_b_two hstd hB hrec hfus hHle h9

theorem exists_pComponent_centralizer_b_two
    {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) (hKproper : KProper InCatalog G)
    (hchar : IsCharTwoType G) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    ∃ L : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({B.b 2} : Set G)) L ∧
      nineJ K (B.b 2) ≤ L ∧ b₀ ∈ Subgroup.normalizer (L : Set G) ∧
      GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b₀} : Set G)) (nineJ K (B.b 2)) := by
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.2.1
  have hKproper' : CFSG.IsKProper G :=
    CFSG.ComponentClassification.CatalogueKProper.isKProper_of_kProper hKproper
  have hJY := nineJ_glapComponent_centralizer_inf hstd hB hrec hchar hfus
  have hJinput := nineJ_glapComponent_layerCentralizer hstd hB hrec hchar hfus
  have hb0ord : orderOf b₀ = 3 := hstd.2.1.1
  have hb0ne : b₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb0ord
    norm_num at hb0ord
  have hb2ne : B.b 2 ≠ 1 := by
    intro h
    have hord := B.ord 2
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hb0pow : b₀ ^ 3 = 1 := by
    rw [← hb0ord]
    exact pow_orderOf_eq_one b₀
  have hb2pow : (B.b 2) ^ 3 = 1 := by
    rw [← B.ord 2]
    exact pow_orderOf_eq_one (B.b 2)
  have hcomm : b₀ * B.b 2 = B.b 2 * b₀ := by
    have h := B.comm 0 2
    rw [hB.2.1] at h
    exact h.eq
  have h12 := CFSG.HardMathSupport.Solomon.Coordinator.input18_3_12_of_schreier
    hSch G hKproper' b₀ (B.b 2) hb0ne hb2ne
    hb0pow hb2pow hcomm (nineJ K (B.b 2)) hJinput
  rcases h12 with ⟨hLcomp, hb0N⟩ | ⟨M, hM, hM1, hM2, hKconj, Z, hZ, hZc, hZiso⟩
  · refine ⟨_, hLcomp, ?_, hb0N, ?_⟩
    · exact le_iSup₂_of_le 1 (Subgroup.one_mem _) (gLBConj_one (nineJ K (B.b 2))).ge
    · refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down
        Nat.prime_three hJY ?_ ?_
      · exact le_inf (le_iSup₂_of_le 1 (Subgroup.one_mem _)
          (gLBConj_one (nineJ K (B.b 2))).ge)
          ((Subgroup.commutator_le_self _).trans (inf_le_left.trans hKC))
      · exact le_inf inf_le_right (inf_le_left.trans hLcomp.1)
  · exfalso
    have : Z.Normal := hZ
    exact false_of_three_component_diagonal hstd hB hrec hfus hM
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm) hM1 hZc hZiso

end CFSG.StandardType.FrameRoute.FS81

end
