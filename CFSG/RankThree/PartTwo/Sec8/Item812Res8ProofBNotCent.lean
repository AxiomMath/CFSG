module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofJTwo
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofOmegaD4
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofSp4
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.Quasithin.Background.FFC2G2
public import CFSG.LieType.Simplicity.TitsModel
import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (projSL projSp)

namespace Item812Res8

theorem le_of_two_pow_dvd {a b r : ℕ} (hr : Odd r) (h : 2 ^ a ∣ 2 ^ b * r) : a ≤ b := by
  by_contra hab
  push Not at hab
  have h1 : 2 ^ (b + 1) ∣ 2 ^ b * r := (Nat.pow_dvd_pow 2 hab).trans h
  rw [pow_succ] at h1
  have h2 : 2 ∣ r := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  exact (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h2)

variable {G : Type} [Group G] [Finite G]

theorem imageModTheta_le_barCentralizer_of_trivial {L I : Subgroup G} {b : G} (hIL : I ≤ L)
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hθ : NoThetaNormal (imageModTheta L I))
    (htriv : ∀ i ∈ I, b * i * b⁻¹ * i⁻¹ ∈
      ((aschbacherSolvableCore 3 I).map I.subtype : Subgroup G)) :
    imageModTheta L I ≤ barCentralizer (Subgroup.zpowers b) L := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  set f := Item87Proof.modThetaHom hIL with hf
  set ρ := f.rangeRestrict with hρ
  have hρs : Function.Surjective ρ := f.rangeRestrict_surjective
  have hθR : NoThetaNormal f.range := Item87Proof.NoThetaNormal.of_mulEquiv
    (MulEquiv.subgroupCongr (Item87Proof.range_modThetaHom hIL)) hθ
  set M := (aschbacherSolvableCore 3 I).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 I).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := hθR M hMn hMs hM3
  have hρθ : ∀ t ∈ aschbacherSolvableCore 3 I,
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) (Subgroup.inclusion hIL t) = 1 := by
    intro t ht
    have h1 : ρ t ∈ M := Subgroup.mem_map_of_mem ρ ht
    rw [hM1, Subgroup.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [hρ, MonoidHom.coe_rangeRestrict] at h2
    exact h2
  rw [barCentralizer_zpowers_eq_autFix hbN]
  rintro _ ⟨⟨i, hiL⟩, hiI, rfl⟩
  have hiI' : i ∈ I := Subgroup.mem_subgroupOf.mp hiI
  rw [Sec4.mem_autFix, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  obtain ⟨t₀, ht₀, ht₀e⟩ := htriv i hiI'
  have ht₀e' : (t₀ : G) = b * i * b⁻¹ * i⁻¹ := ht₀e
  have htL : (t₀ : G) ∈ L := hIL t₀.2
  have h1 := hρθ t₀ ht₀
  rw [QuotientGroup.mk'_apply] at h1
  have hbi : b * i * b⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp hbN i).mp hiL
    exact this
  have h2 : (Sec4.compAction L ⟨b, hbN⟩ ⟨i, hiL⟩ : L) =
      (Subgroup.inclusion hIL t₀) * ⟨i, hiL⟩ := by
    apply Subtype.ext
    change b * i * b⁻¹ = (t₀ : G) * i
    rw [ht₀e']
    group
  rw [h2, QuotientGroup.mk_mul, h1, one_mul]

theorem false_of_trivial_of_card {L I : Subgroup G} {a b : G} (hIL : I ≤ L)
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hIimg : imageModTheta L I =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L))
    (hθ : NoThetaNormal (perfectResidual (barCentralizer (Subgroup.zpowers a) L)))
    (htriv : ∀ i ∈ I, b * i * b⁻¹ * i⁻¹ ∈
      ((aschbacherSolvableCore 3 I).map I.subtype : Subgroup G))
    {N : ℕ} (hN : Nat.card (imageModTheta L
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) = N)
    (hnd : ¬ Nat.card (perfectResidual (barCentralizer (Subgroup.zpowers a) L)) ∣ N) : False := by
  have eI : imageModTheta L I ≃* perfectResidual (barCentralizer (Subgroup.zpowers a) L) :=
    (MulEquiv.subgroupCongr hIimg).trans (inSubgroupPerfectResidualEquiv _)
  have hθI : NoThetaNormal (imageModTheta L I) := Item87Proof.NoThetaNormal.of_mulEquiv eI hθ
  have hle := imageModTheta_le_barCentralizer_of_trivial hIL hbN hθI htriv
  have hperf : Group.IsPerfect (imageModTheta L I) := by
    rw [hIimg]
    exact Item87Proof.isPerfect_residual _
  have hle2 := KFacts.le_inSubgroup_perfectResidual hperf hle
  have himgB := KFacts.imageModTheta_perfectResidual_centralizer_eq hbN
    ⟨1, by rw [pow_one]; exact hb3⟩
  rw [← himgB] at hle2
  apply hnd
  rw [← Nat.card_congr eI.toEquiv, ← hN]
  exact Subgroup.card_dvd_of_le hle2

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
theorem not_dvd_card_perfectResidual_projSp {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nat.card (perfectResidual (projSp 2 (GaloisField 2 m))) ∣
      2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    have hF2 : Nat.card (GaloisField 2 1) = 2 := by rw [hF, pow_one]
    set H := projSp 2 (GaloisField 2 1)
    have E : H ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
      (Sec4.projSpEquivStatedProj 2 _).trans
        (CFSG.RankThree.PartOne.KCSpComm.statedProjEquivSympFour hF2)
    obtain ⟨hq, -⟩ := CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour E
    obtain ⟨⟨e6⟩, -⟩ := CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour E
    have heq : perfectResidual H = commutator H :=
      le_antisymm (perfectResidual_le_commutator H)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hq.1)
    rw [heq, Nat.card_congr e6.toEquiv, KFacts.card_alternatingGroup_six]
    norm_num
  · set F := GaloisField 2 m
    set H := projSp 2 F
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hSP : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have eH : StatedSp 2 F ≃* H := KFacts.statedSpEquivProjSpOfCharTwo F
    set eP : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
      MulEquiv.ofBijective (proj 2 F) ⟨KFacts.proj_injective_of_charTwo, proj_surjective⟩
    have hS : IsSimpleGroup (StatedSp 2 F) := MulEquiv.isSimpleGroup eP
    have hZ : Subgroup.center (StatedSp 2 F) = ⊥ := KFacts.center_statedSp_eq_bot
    have hnc : ∃ u v : H, u * v ≠ v * u := by
      by_contra hc
      push Not at hc
      have hct : ∀ u v : StatedSp 2 F, u * v = v * u := fun u v => by
        apply eH.injective
        rw [map_mul, map_mul]
        exact hc _ _
      have htop : Subgroup.center (StatedSp 2 F) = ⊤ :=
        eq_top_iff.mpr fun u _ => Subgroup.mem_center_iff.mpr fun v => hct v u
      rw [hZ] at htop
      have hnt : Nontrivial (StatedSp 2 F) := IsSimpleGroup.toNontrivial
      exact (bot_ne_top htop)
    have hSH : IsSimpleGroup H := MulEquiv.isSimpleGroup eH.symm
    have hperf : Group.IsPerfect H := Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf, Subgroup.card_top,
      Sec19.Step1911Proof.card_projSp_two hm]
    intro hd
    have hodd : Odd ((2 ^ (3 * m)) ^ 2 - 1) := by
      have h1 : 1 ≤ (2 ^ (3 * m)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h2 : Even ((2 ^ (3 * m)) ^ 2) := by
        rw [← pow_mul]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd h1 h2 odd_one
    have h2 := (Dvd.intro _ rfl : 2 ^ (m * 4) ∣ 2 ^ (m * 4) *
      (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))).trans hd
    have := le_of_two_pow_dvd hodd h2
    omega


theorem not_dvd_card_perfectResidual_g2
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) :
    ¬ Nat.card (perfectResidual (adjointGroup .G2 K)) ∣ 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
  have hq : 2 ≤ 2 ^ m := two_le_two_pow hm
  have h3m : 2 ^ (3 * m) = (2 ^ m) ^ 3 := by rw [mul_comm, pow_mul]
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    set H := adjointGroup .G2 K
    obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
    obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hK (Subgroup.topEquiv.trans E)
    have hcard := card_commutator_g2_two hK (Subgroup.topEquiv.trans E)
    have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    have heq : perfectResidual H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      le_antisymm (perfectResidual_le_commutator H)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
    rw [heq, hcard]
    norm_num
  · have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hperf := CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K h3
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf, Subgroup.card_top,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, h3m, CFSG.Open.ordG2]
    intro hd
    have h2 : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h6 : 64 ≤ (2 ^ m) ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 2) hq 6]
    have hpos : 0 < (2 ^ m) ^ 3 * (((2 ^ m) ^ 3) ^ 2 - 1) := by
      have : 1 < ((2 ^ m) ^ 3) ^ 2 := by nlinarith
      have : 0 < ((2 ^ m) ^ 3) ^ 2 - 1 := by omega
      positivity
    have hle := Nat.le_of_dvd hpos hd
    have e : ((2 ^ m) ^ 3) ^ 2 = (2 ^ m) ^ 6 := by ring
    rw [e] at hle
    have hpos6 : 0 < (2 ^ m) ^ 6 - 1 := by omega
    have e6 : (2 ^ m) ^ 6 = (2 ^ m) ^ 3 * (2 ^ m) ^ 3 := by ring
    have h33 : (2 ^ m) ^ 3 < (2 ^ m) ^ 6 := by rw [e6]; nlinarith
    have : (2 ^ m) ^ 3 * ((2 ^ m) ^ 6 - 1) <
        (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) := by
      calc (2 ^ m) ^ 3 * ((2 ^ m) ^ 6 - 1) < (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) :=
            Nat.mul_lt_mul_of_pos_right h33 hpos6
        _ ≤ (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem noThetaNormal_perfectResidual_g2
    {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) :
    NoThetaNormal (perfectResidual (adjointGroup .G2 K)) := by
  set H := adjointGroup .G2 K
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · obtain rfl : m = 1 := by omega
    obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK
    obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hK (Subgroup.topEquiv.trans E)
    have hcard := card_commutator_g2_two hK (Subgroup.topEquiv.trans E)
    have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
    have heq : perfectResidual H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
      le_antisymm (perfectResidual_le_commutator H)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
    refine Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr heq)
      (noThetaNormal_of_isSimpleGroup ?_)
    rw [hcard]
    norm_num
  · have h3k : 3 ≤ Nat.card K := by
      rw [hK]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K h3k
    have hZ : Subgroup.center H = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    have hS : IsSimpleGroup H := CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have h3 : 3 ∣ Nat.card H := by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, CFSG.Open.ordG2]
      refine Dvd.dvd.mul_left ?_ _
      have h4' : (2 ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4']
      exact Item87Proof.three_dvd_four_pow_sub_one m
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hq.1]
    exact Item87Proof.NoThetaNormal.of_mulEquiv Subgroup.topEquiv
      (noThetaNormal_of_isSimpleGroup h3)

theorem two_pow_dvd_card_perfectResidual_reeGamma {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    2 ^ (9 * (2 * b + 1) + 1) ∣ Nat.card (perfectResidual (ReeTag.F4.reeGamma k b)) := by
  have hq2 : 2 ≤ 2 ^ (2 * b + 1) := two_le_two_pow (by omega)
  have hcardR : 2 ^ (12 * (2 * b + 1)) ∣ Nat.card (ReeTag.F4.reeGamma k b) := by
    rw [Item86ResProof.card_of_mulEquiv_reeGamma b k hk (MulEquiv.refl _),
      Item86ResProof.ordTwistedF4_eq_factored' hq2, mul_comm 12 (2 * b + 1), pow_mul]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right dvd_rfl _) _) _) _) _
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card k = 2 := by simpa using hk
    set R := reeFixed ReeTag.F4 k 0 with hR
    set eR : R ≃* ReeTag.F4.reeGamma k 0 := ReeTag.reeFixedEquivReeGamma k 0
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hperf : Group.IsPerfect (commutator R) := hT.isPerfect hk2
    have hsup : commutator R ⊔ Subgroup.zpowers hT.g₁ = ⊤ := hT.commutator_sup_zpowers_eq_top hk2
    have hg2 := hT.g₁_sq_mem
    have heq : perfectResidual R = commutator R :=
      le_antisymm (perfectResidual_le_commutator R)
        (Item87Res2Proof.le_perfectResidual_of_isPerfect hperf)
    have : (commutator R).Normal := Subgroup.commutator_normal ⊤ ⊤
    have hQ : Nat.card (R ⧸ commutator R) ≤ 2 := by
      set g := QuotientGroup.mk' (commutator R) hT.g₁ with hgdef
      have hg2' : g ^ 2 = 1 := by
        rw [hgdef, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hg2
      have hall : ∀ y : R ⧸ commutator R, y ∈ Subgroup.zpowers g := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H y =>
          have hy : y ∈ commutator R ⊔ Subgroup.zpowers hT.g₁ := hsup ▸ Subgroup.mem_top y
          obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          refine ⟨i, ?_⟩
          have hc1 : QuotientGroup.mk' (commutator R) c = 1 :=
            (QuotientGroup.eq_one_iff c).2 hc
          change g ^ i = QuotientGroup.mk' (commutator R) (c * hT.g₁ ^ i)
          rw [map_mul, hc1, one_mul, map_zpow]
      have hcard := orderOf_eq_card_of_forall_mem_zpowers hall
      rw [← hcard]
      exact orderOf_le_of_pow_eq_one (by norm_num) hg2'
    have hQpos : 0 < Nat.card (R ⧸ commutator R) := Nat.card_pos
    have hQ2 : Nat.card (R ⧸ commutator R) ∣ 2 := by
      rcases (show Nat.card (R ⧸ commutator R) = 1 ∨ Nat.card (R ⧸ commutator R) = 2 by
        omega) with h | h <;> simp [h]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator R)
    have hR12 : 2 ^ 12 ∣ Nat.card R := by
      rw [Nat.card_congr eR.toEquiv]
      simpa using hcardR
    rw [hsplit] at hR12
    have h11 : 2 ^ 12 ∣ 2 * Nat.card (commutator R) :=
      hR12.trans (Nat.mul_dvd_mul_right hQ2 _)
    have h11' : 2 ^ 11 ∣ Nat.card (commutator R) := by
      rw [show (2 : ℕ) ^ 12 = 2 * 2 ^ 11 by norm_num] at h11
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h11
    rw [← KFacts.perfectResidual_map_mulEquiv eR, Subgroup.card_map_of_injective eR.injective,
      heq]
    exact (Nat.pow_dvd_pow 2 (by norm_num)).trans h11'
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    rw [KFacts.perfectResidual_eq_top_of_isPerfect hperf, Subgroup.card_top]
    exact (Nat.pow_dvd_pow 2 (by omega)).trans hcardR

end Item812Res8


@[expose] def KF89BNotCentIUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    (∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
    ∃ i ∈ sec8I L a, b * i * b⁻¹ * i⁻¹ ∉
      ((aschbacherSolvableCore 3 ↥(sec8I L a)).map (sec8I L a).subtype : Subgroup G)


open Item812Res8

theorem kF89BNotCentI_of
    (h45 : Sec4.Item4_5) (hU : KF89BNotCentIUnitary)
    (hR : KF89ReeTwoLocal) : KF89BNotCentI := by
  intro G _ _ A c L a b X n h
  classical
  by_cases hun : ∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m
  · exact hU G A c L a b X n h hun
  have hun3 : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 := fun h3 => hun ⟨3, h3⟩
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hun3, ↓reduceIte]
  by_contra hall
  push Not at hall
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hcA : c ∈ A := h.mem_A
  have hc1 : c ≠ 1 := h.ne_one
  have hc3 : c ^ 3 = 1 := hAab.2 c hcA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hAcC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp hc3 hc1 hAp hAcC L
      h.mem_thetaComponentsAt
  have haN := hAL haA
  have hbN := hAL hbA
  have hout : InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  have hIL : sec8I L a ≤ L := (Item812Res7.sec8I_le L a).trans inf_le_left
  have hIimg : imageModTheta L (sec8I L a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
    rw [hIdef]
    exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rw [pow_one]; exact ha3⟩
  have hn1 : 1 ≤ n := h.isGammaIndex.2.2.1
  obtain ⟨-, -, -, hcase⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  rcases hcase with ⟨⟨k, hk, hkn, ⟨e₀⟩⟩, hSU⟩ | ⟨hL2, ⟨ι⟩⟩
  ·
    have hRm := (Sec4.Census.bridgeExceptional46).reeF4 k hk
    obtain ⟨-, k₁, hk₁, hkk₁, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRm
    obtain ⟨b', k'', _, _, _, hk'', hrel, ⟨φ⟩⟩ :=
      exists_barCentralizer_mulEquiv_reeGamma' hk₁ hK (e₀.trans e₁) ha3 hout
    have hb' : 2 * b' + 1 = n := by omega
    have hθ : NoThetaNormal (perfectResidual (barCentralizer (Subgroup.zpowers a) L)) :=
      Item87Proof.NoThetaNormal.of_mulEquiv (perfectResidualCongr φ) (hR b' k'' hk'').1
    refine false_of_trivial_of_card hIL hbN hb3 hIimg hθ hall (card_of_isoSUThree hSU) ?_
    rw [Nat.card_congr (perfectResidualCongr φ).toEquiv]
    intro hd
    have h2 := (two_pow_dvd_card_perfectResidual_reeGamma hk'').trans hd
    rw [hb'] at h2
    have hodd : Odd (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) := by
      have h1 : 1 ≤ (2 ^ (3 * n)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      have h2' : Even ((2 ^ (3 * n)) ^ 2) := by
        rw [← pow_mul]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      have h3' : Even ((2 ^ (3 * n)) ^ 3) := by
        rw [← pow_mul]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact (Nat.Even.sub_odd h1 h2' odd_one).mul (h3'.add_one)
    have e9 : (2 ^ (3 * n)) ^ 3 * ((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1) =
        2 ^ (9 * n) * (((2 ^ (3 * n)) ^ 2 - 1) * ((2 ^ (3 * n)) ^ 3 + 1)) := by
      rw [← pow_mul, show 3 * n * 3 = 9 * n by ring]
      ring
    rw [e9] at h2
    have := le_of_two_pow_dvd hodd h2
    omega
  · have hN : Nat.card (imageModTheta L
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)))) =
        2 ^ (3 * n) * ((2 ^ (3 * n)) ^ 2 - 1) :=
      (Nat.card_congr ι.toEquiv).trans (Item87Proof.card_projSL_two_three hn1)
    rcases hL2 with hD | ⟨q, hq2, hqe, hG2⟩ | hUU | hS | hSp
    ·
      obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := h.gTwo (Or.inl hD)
      refine false_of_trivial_of_card hIL hbN hb3 hIimg
        (Item87Proof.NoThetaNormal.of_mulEquiv (perfectResidualCongr φ)
          (noThetaNormal_perfectResidual_g2 hn1 hk)) hall hN ?_
      rw [Nat.card_congr (perfectResidualCongr φ).toEquiv]
      exact not_dvd_card_perfectResidual_g2 hn1 hk
    ·
      obtain ⟨k, _, _, hk, ⟨φ⟩⟩ :=
        h.gTwo (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG2))
      refine false_of_trivial_of_card hIL hbN hb3 hIimg
        (Item87Proof.NoThetaNormal.of_mulEquiv (perfectResidualCongr φ)
          (noThetaNormal_perfectResidual_g2 hn1 hk)) hall hN ?_
      rw [Nat.card_congr (perfectResidualCongr φ).toEquiv]
      exact not_dvd_card_perfectResidual_g2 hn1 hk
    · exact hun ⟨3 * n, Or.inl hUU⟩
    · exact hun ⟨3 * n, Or.inr hS⟩
    ·
      obtain ⟨-, ⟨φ⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp (n := n) (by omega) ha3 hout hSp
      refine false_of_trivial_of_card hIL hbN hb3 hIimg
        (Item87Proof.NoThetaNormal.of_mulEquiv (perfectResidualCongr φ)
          (kF89Sp4TwoLocal_holds n hn1).1) hall hN ?_
      rw [Nat.card_congr (perfectResidualCongr φ).toEquiv]
      exact not_dvd_card_perfectResidual_projSp hn1

end CFSG.RankThree.PartTwo.Sec8
