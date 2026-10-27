module

public import CFSG.Quasithin.Vol2.Ch3B513NC1
public import CFSG.Quasithin.H13.VolIAltCoverG2
public import CFSG.Quasithin.H13.VolII16Restrict
public import CFSG.Quasithin.Background.SmithB57ED
public import CFSG.Quasithin.Background.B5Models
public import CFSG.Quasithin.Background.SmithB51G2DExcl
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.JonesParshallG2TwoH1
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Y13
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.JonesParshallSL5Wedge
public import CFSG.Quasithin.Background.SmithB51P5Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_sub_small (hW : ∀ w : W, w ^ 2 = 1) {G D : Subgroup (MulAut W)}
    (hD : IsFFStarMin G D) {S : Subgroup W} (hS : commV D ≤ S)
    (hmove : ∃ u ∈ S, ∃ d ∈ D, d u ≠ u) (hcard : Nat.card S ≤ 2 ^ 7) : HasGood G := by
  refine hasGood_of_offender_small hW hD hS ?_
  obtain ⟨u, hu, d, hd, hdu⟩ := hmove
  have hlt : fixV D ⊓ S < S := by
    refine lt_of_le_of_ne inf_le_right fun heq => hdu ?_
    have : u ∈ fixV D ⊓ S := by rw [heq]; exact hu
    exact this.1 d hd
  have hdvd : Nat.card ↥(fixV D ⊓ S) ∣ Nat.card S := Subgroup.card_dvd_of_le inf_le_right
  have hlt' : Nat.card ↥(fixV D ⊓ S) < Nat.card S := Subgroup.card_lt_of_lt hlt
  obtain ⟨j, hj⟩ := card_subgroup_two_pow hW S
  rw [hj] at hdvd hlt' hcard
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hi'] at hlt' ⊢
  have hij : i < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
  have hj7 : j ≤ 7 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem comm_le_self {X : Type*} [Group X] (H : Subgroup X) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)) (H.inv_mem hh)

omit [Finite W] in
theorem mem_of_pow_three_eq_one {G L T : Subgroup (MulAut W)} (hLG : L ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hT : IsPGroup 2 T) (hTG : T ≤ G)
    (hGT : G = L ⊔ T) {x : MulAut W} (hx : x ∈ G) (h3 : x ^ 3 = 1) : x ∈ L := by
  let N : Subgroup ↥G := L.subgroupOf G
  have hN : N.Normal := ⟨fun n hn g => by
    have hn' : (n : MulAut W) ∈ L := Subgroup.mem_subgroupOf.1 hn
    exact Subgroup.mem_subgroupOf.2 (hnorm g g.2 n hn')⟩
  let T' : Subgroup ↥G := T.subgroupOf G
  have hsup : N ⊔ T' = ⊤ := by
    apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLG,
      Subgroup.map_subgroupOf_eq_of_le hTG, ← hGT, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hT' : IsPGroup 2 ↥T' := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTG).symm
  let f : ↥T' →* ↥G ⧸ N := (QuotientGroup.mk' N).comp T'.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ N ⊔ T' := by rw [hsup]; trivial
    obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    refine ⟨⟨t, ht⟩, ?_⟩
    show (QuotientGroup.mk t : ↥G ⧸ N) = QuotientGroup.mk (n * t)
    rw [QuotientGroup.eq, show t⁻¹ * (n * t) = t⁻¹ * n * t by group]
    exact hN.conj_mem' n hn t
  have hQ : IsPGroup 2 (↥G ⧸ N) := hT'.of_surjective f hf
  obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk ⟨x, hx⟩)
  have h1 : x ^ (2 ^ k) ∈ L := by
    have h2 : ((⟨x, hx⟩ : ↥G) ^ (2 ^ k)) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have h3 := Subgroup.mem_subgroupOf.1 h2
    simpa using h3
  have h4 : (2 ^ k * 2 ^ k) % 3 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  have h5 : x = (x ^ (2 ^ k)) ^ (2 ^ k) := by
    rw [← pow_mul, ← Nat.div_add_mod (2 ^ k * 2 ^ k) 3, h4, pow_add, pow_mul, h3, one_pow,
      one_mul, pow_one]
  rw [h5]
  exact L.pow_mem h1 _


omit [Finite W] in
theorem commutator_le_of_g2Natural {G L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hG2 : G2Natural G U Z 1) (hmem : ∀ x ∈ G, x ^ 3 = 1 → x ∈ L) : ⁅G, G⁆ ≤ L := by
  obtain ⟨K, _, _, hK, π, hr⟩ := B5.g2NaturalDerived_of_g2Natural hG2
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK2]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hKf, pow_one])
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hKf).symm
  let φ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥subG2 :=
    (H13.VolI.g2DerivedFieldEquiv e).trans H13.VolI.g2TwoEquiv
  let ψ : ↥subG2 →* MulAut W := (⁅G, G⁆.subtype.comp π).comp φ.symm.toMonoidHom
  have hψG : ∀ s, ψ s ∈ G := fun s => comm_le_self G (π (φ.symm s)).2
  have hcube : ∀ y ∈ subG2, ∀ hy : y ∈ subG2, (⟨y, hy⟩ : ↥subG2) ^ 3 = 1 →
      ψ ⟨y, hy⟩ ∈ L := fun y _ hy hy3 =>
    hmem _ (hψG _) (by rw [← map_pow, hy3, map_one])
  have hall : ∀ y, y ∈ subG2 → ∀ hy : y ∈ subG2, ψ ⟨y, hy⟩ ∈ L := by
    intro y hy0
    have hy1 := hy0
    unfold subG2 at hy1
    induction hy1 using Subgroup.closure_induction with
    | mem z hz =>
      intro hz'
      refine hcube z hz' hz' (Subtype.ext ?_)
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_three]
      rcases hz with rfl | hz
      · have h := congrArg Subtype.val g2a_cube
        simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        have h := congrArg Subtype.val g2b_cube
        simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h
    | one =>
      intro h1
      have : (⟨1, h1⟩ : ↥subG2) = 1 := rfl
      rw [this, map_one]
      exact L.one_mem
    | mul a b ha hb iha ihb =>
      intro hab
      have ha' : a ∈ subG2 := ha
      have hb' : b ∈ subG2 := hb
      have : (⟨a * b, hab⟩ : ↥subG2) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := rfl
      rw [this, map_mul]
      exact L.mul_mem (iha ha' ha') (ihb hb' hb')
    | inv a ha iha =>
      intro hai
      have ha' : a ∈ subG2 := ha
      have : (⟨a⁻¹, hai⟩ : ↥subG2) = (⟨a, ha'⟩ : ↥subG2)⁻¹ := rfl
      rw [this, map_inv]
      exact L.inv_mem (iha ha' ha')
  intro x hx
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, π γ = ⟨x, hx⟩ := hr.1 ⟨x, hx⟩
  have : x = ψ (φ γ) := by
    show x = ((π (φ.symm (φ γ)) : ↥⁅G, G⁆) : MulAut W)
    rw [MulEquiv.symm_apply_apply, hγ]
  rw [this]
  exact hall _ (φ γ).2 (φ γ).2

theorem card_le_two_of_g2Der (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hU : commV L ∈ IrrPlus L ⊤) (h : G2NaturalDerived L (commV L) (fixV L ⊓ commV L) 1) :
    Nat.card ↥(fixV L ⊓ commV L) ≤ 2 := by
  obtain ⟨K, hKf, hKfin, hK, hR⟩ := h
  refine H13.VolI.card_le_of_restrict (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) ?_ hW hU hR
  intro W' _ _ hW' H Z hZ hcomm hR'
  rcases H13.VolI.g2NaturalCover_holds W' hW' H Z hZ hcomm ⟨K, hKf, hKfin, hK, hR'⟩ with h0 | h2
  · rw [h0, Subgroup.card_bot]
    norm_num
  · exact h2.1.le

omit [Finite W]
  in
theorem card_of_g2Der {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (h : G2NaturalDerived L U Z 1) : Nat.card U = 2 ^ 6 * Nat.card Z := by
  obtain ⟨K, _, _, hK, π, hr⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  rw [G64.RealizesVia.card_eq hr, B5.G2D.card_zornQMod, hK2]

theorem c1g2Der_holds : C1G2Der := by
  intro W _ _ hW G hne hB53 h1 hGL hU hGD
  have hC2 := card_le_two_of_g2Der hW hU hGD
  have hUc := card_of_g2Der hGD
  obtain ⟨K, _, _, hK, π, hr⟩ := hGD
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  refine hasGood_of_realizes_small hW hne hB53.2.1 le_rfl
    (FFC.zornQ_faithful _ (comm_le_self _)) hr ?_
  rw [hUc]
  calc 2 ^ 6 * Nat.card ↥(fixV G ⊓ commV G) ≤ 2 ^ 6 * 2 := Nat.mul_le_mul_left _ hC2
    _ = 2 ^ 7 := by norm_num

theorem c1g2Two_holds : C1G2Two := by
  intro W _ _ hW G hne hB53 h1 hU T hT hGT hG2
  have hLG : quasithinGenFitting G ≤ G := quasithinGenFitting_le G
  have hnorm : ∀ g ∈ G, ∀ x ∈ quasithinGenFitting G, g * x * g⁻¹ ∈ quasithinGenFitting G :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.1 (le_normalizer_quasithinGenFitting G hg) x).1 hx
  have hperf : ⁅quasithinGenFitting G, quasithinGenFitting G⁆ = quasithinGenFitting G :=
    Subgroup.isPerfect_iff.mp h1.1.1
  have hcomm : ⁅G, G⁆ = quasithinGenFitting G := by
    refine le_antisymm (commutator_le_of_g2Natural hG2 fun x hx h3 =>
      mem_of_pow_three_eq_one hLG hnorm hT.2.1 hT.1 hGT hx h3) ?_
    calc quasithinGenFitting G = ⁅quasithinGenFitting G, quasithinGenFitting G⁆ := hperf.symm
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hLG hLG
  have hGd : G2NaturalDerived (quasithinGenFitting G) (commV (quasithinGenFitting G))
      (fixV (quasithinGenFitting G) ⊓ commV (quasithinGenFitting G)) 1 := by
    have e := B5.g2NaturalDerived_of_g2Natural hG2
    rwa [hcomm] at e
  have hC2 := card_le_two_of_g2Der hW hU hGd
  have hUZ := card_of_g2Der hGd
  have hGcard : Nat.card G = 12096 := by
    obtain ⟨K, _, _, hK, π, hr⟩ := id hG2
    have hK2 : Nat.card K = 2 := by simpa using hK
    have : CharP K 2 := FFC.charP_two_of_card_pow hK
    have hinj := FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hr
    have hc : Nat.card ↥(quasithinG2 K) = Nat.card G :=
      Nat.card_congr (Equiv.ofBijective π ⟨hinj, hr.1⟩)
    rw [card_quasithinG2_1527d hK, hK2] at hc
    norm_num at hc
    exact hc.symm
  have hL8 : Nat.card ↥(quasithinGenFitting G) ≠ 20160 := by
    have := Subgroup.card_le_of_le hLG
    omega
  have hsup : commV (quasithinGenFitting G) ⊔ fixV G = ⊤ := by
    rcases h1.2.1.2.2.2.2.1 with hs | ⟨-, hlist, -⟩
    · exact hs
    · exact absurd hlist (SmithB57E.not_list5 (by rw [hUZ]; ring) hL8)
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hB53.2.1
  have hDG : D ≤ G := hD.1.1
  have hS : commV D ≤ commV (quasithinGenFitting G) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨d, hd, w, rfl⟩
    have hw : w ∈ commV (quasithinGenFitting G) ⊔ fixV G := by rw [hsup]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    have hdc : d c = c := hc d (hDG hd)
    have hdu : d u ∈ commV (quasithinGenFitting G) :=
      FFC.commV_invariant (hnorm d (hDG hd)) hu
    show d (u * c) * (u * c)⁻¹ ∈ _
    rw [map_mul, hdc, mul_inv_rev, mul_assoc, ← mul_assoc c, mul_inv_cancel, one_mul]
    exact (commV _).mul_mem hdu ((commV _).inv_mem hu)
  have hmove : ∃ u ∈ commV (quasithinGenFitting G), ∃ d ∈ D, d u ≠ u := by
    by_contra hno
    push Not at hno
    apply hD.1.2.1
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ commV (quasithinGenFitting G) ⊔ fixV G := by rw [hsup]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul, hno u hu d hd, hc d (hDG hd)]
    rfl
  refine hasGood_of_sub_small hW hD hS hmove ?_
  rw [hUZ]
  calc 2 ^ 6 * Nat.card ↥(fixV (quasithinGenFitting G) ⊓ commV (quasithinGenFitting G))
      ≤ 2 ^ 6 * 2 := Nat.mul_le_mul_left _ hC2
    _ = 2 ^ 7 := by norm_num

end CFSG.Quasithin.B513N
