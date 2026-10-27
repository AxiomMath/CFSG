module

import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem sectionFourHyp_subgroup {G : Type} [Group G] [Finite G] (hG : SectionFourHyp G)
    (H : Subgroup G) : SectionFourHyp H :=
  ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hG.kGroup H ⊥ QuotientGroup.quotientBot,
    (evenRank_subgroup_le H).trans hG.evenRank_le,
    fun p hp h3 => (localRank_subgroup_le hp H).trans_lt (hG.localRank_lt p hp h3)⟩

theorem aschbacherSolvableCore_le_center {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : aschbacherSolvableCore 3 Q ≤ Subgroup.center Q := by
  obtain ⟨hsolv, hchar, -⟩ := solvable_prime_complement_core_characterization (H := Q)
    Nat.prime_three
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (N := aschbacherSolvableCore 3 Q)
    inferInstance with h | h
  · exfalso
    have : Group.IsSolvable (⊤ : Subgroup Q) := h ▸ hsolv
    exact false_of_isQuasisimple_of_isSolvable hQ
      (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
        Subgroup.topEquiv.surjective)
  · exact h

theorem mem_thetaComponents_of_isComponent3 {H : Type*} [Group H] [Finite H] {L : Subgroup H}
    (hL : IsComponent L) : L ∈ thetaComponents 3 H :=
  ⟨hL.1.1, hL.2, (CFSG.LocalCores.quasisimple_central_quotient hL.1 _
    (aschbacherSolvableCore_le_center hL.1)).1⟩

@[expose] noncomputable def thetaQuotCongr {X Y : Type*} [Group X] [Group Y] [Finite X]
    (φ : X ≃* Y) :
    X ⧸ aschbacherSolvableCore 3 X ≃* Y ⧸ aschbacherSolvableCore 3 Y :=
  QuotientGroup.congr _ _ φ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three φ)

theorem thetaQuotCongr_mk {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X ≃* Y) (x : X) :
    thetaQuotCongr φ (x : X ⧸ aschbacherSolvableCore 3 X) =
      ((φ x : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :=
  rfl

theorem eq_one_of_thetaQuotMulAut_eq_one {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) {σ : MulAut X} (h : thetaQuotMulAut X σ = 1) : σ = 1 := by
  have : Group.IsPerfect X := hX.1
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => aschbacherSolvableCore_le_center hX ?_
  have hs := congrArg (fun τ : MulAut (X ⧸ aschbacherSolvableCore 3 X) =>
    τ (s : X ⧸ aschbacherSolvableCore 3 X)) h
  simp only [thetaQuotMulAut_mk, MulAut.one_apply] at hs
  rw [QuotientGroup.eq] at hs
  have := (aschbacherSolvableCore 3 X).inv_mem hs
  simpa using this

theorem isInnerAut_of_thetaQuotMulAut {X : Type*} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) {σ : MulAut X}
    (h : thetaQuotMulAut X σ ∈ (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →*
      MulAut (X ⧸ aschbacherSolvableCore 3 X)).range) :
    σ ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Group.IsPerfect X := hX.1
  obtain ⟨y, hy⟩ := h
  induction y using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨g', hg'⟩ := KFacts.isInnerAut_of_forall_mem_center (τ := σ) g fun s => by
      refine aschbacherSolvableCore_le_center hX ?_
      have hs := congrArg (fun τ : MulAut (X ⧸ aschbacherSolvableCore 3 X) =>
        τ (s : X ⧸ aschbacherSolvableCore 3 X)) hy
      simp only [MulAut.conj_apply, thetaQuotMulAut_mk] at hs
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.eq] at hs
      exact hs
    exact ⟨g', hg'⟩


theorem isElementaryAbelian_of_isElemAbelian {X : Type*} [Group X] {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : CFSG.IsElementaryAbelian 3 B :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hB

theorem isElemAbelian_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {B : Subgroup X}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : CFSG.Assembly.IsElemAbelian 3 (B.map f) :=
  CFSG.SectionRank.isElemAbelian_map hB _

theorem le_pRank_of_isElementaryAbelian {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : CFSG.IsElementaryAbelian 3 E) {k : ℕ} (hk : Nat.card E = 3 ^ k) :
    k ≤ CFSG.pRank 3 H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 3 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem le_pRank_mulAut {X M : Type*} [Group X] [Group M] [Finite M] (e : X ≃* M)
    {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B) {k : ℕ}
    (hk : Nat.card B = 3 ^ k) : k ≤ CFSG.pRank 3 (MulAut M) := by
  have hB' := isElementaryAbelian_of_isElemAbelian
    (isElemAbelian_map (MulAut.congr e).toMonoidHom hB)
  refine le_pRank_of_isElementaryAbelian hB' ?_
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hk]

theorem ker_conj_eq_center (X : Type*) [Group X] :
    (MulAut.conj : X →* MulAut X).ker = Subgroup.center X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff, MulEquiv.ext_iff]
  simp only [MulAut.conj_apply, MulAut.one_apply]
  constructor
  · intro h g
    calc g * x = x * g * x⁻¹ * x := by rw [h g]
      _ = x * g := by group
  · intro h g
    rw [← h g]
    group

@[expose] noncomputable def innerEquivQuotientCenter (X : Type*) [Group X] :
    X ⧸ Subgroup.center X ≃* (MulAut.conj : X →* MulAut X).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center X).symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : X →* MulAut X))

theorem le_pRank_of_le_inner {X S : Type*} [Group X] [Group S] [Finite S]
    (e : X ⧸ Subgroup.center X ≃* S) {B : Subgroup (MulAut X)}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBi : B ≤ (MulAut.conj : X →* MulAut X).range)
    {k : ℕ} (hk : Nat.card B = 3 ^ k) : k ≤ CFSG.pRank 3 S := by
  set f : (MulAut.conj : X →* MulAut X).range →* S :=
    ((innerEquivQuotientCenter X).symm.trans e).toMonoidHom
  have hf : Function.Injective f := ((innerEquivQuotientCenter X).symm.trans e).injective
  have hB1 : CFSG.Assembly.IsElemAbelian 3 (B.subgroupOf (MulAut.conj : X →* MulAut X).range) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h := congrArg Subtype.val (hB.1.1.comm ⟨_, Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp y.2⟩)
      exact h
    · simpa using hB.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hB' := isElementaryAbelian_of_isElemAbelian (isElemAbelian_map f hB1)
  refine le_pRank_of_isElementaryAbelian hB' ?_
  rw [Subgroup.card_map_of_injective hf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBi).toEquiv,
    hk]

theorem pRank_three_le_of_not_dvd {S : Type*} [Group S] [Finite S]
    (h : ¬ 3 ^ 4 ∣ Nat.card S) : CFSG.pRank 3 S ≤ 3 := by
  refine csSup_le' ?_
  rintro r ⟨B, -, hB⟩
  by_contra hr
  exact h ((Nat.pow_dvd_pow 3 (by omega : 4 ≤ r)).trans (hB ▸ Subgroup.card_subgroup_dvd_card B))

section Action

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def thetaAct {L A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    A →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
  ((thetaQuotMulAut L).comp (compAction L)).comp (Subgroup.inclusion hAN)

theorem thetaAct_apply {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) (a : A) :
    thetaAct hAN a = thetaQuotMulAut L (compAction L ⟨a, hAN a.2⟩) :=
  rfl

theorem thetaAct_eq_one_iff {L A : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (a : A) :
    thetaAct hAN a = 1 ↔ (a : G) ∈ Subgroup.centralizer (L : Set G) := by
  have hker : ∀ x : Subgroup.normalizer (L : Set G), compAction L x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (L : Set G) := fun x => by
    rw [← MonoidHom.mem_ker, compAction_ker, Subgroup.mem_subgroupOf]
  rw [thetaAct_apply]
  constructor
  · intro h
    exact (hker _).mp (eq_one_of_thetaQuotMulAut_eq_one hL h)
  · intro h
    rw [(hker ⟨a, hAN a.2⟩).mpr h, map_one]

theorem card_range_thetaAct_mul {L A : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (thetaAct hAN).range *
      Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = Nat.card A := by
  have hker : (thetaAct hAN).ker = (Subgroup.centralizer (L : Set G)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, thetaAct_eq_one_iff hL, Subgroup.mem_subgroupOf]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (thetaAct hAN)).toEquiv.symm,
    show Nat.card (A ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) =
      Nat.card (thetaAct hAN).ker by
        rw [hker, inf_comm]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
          (by rw [Subgroup.inf_subgroupOf_right])]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

theorem isElemAbelian_range_thetaAct {L A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    CFSG.Assembly.IsElemAbelian 3 (thetaAct hAN).range := by
  have htop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup A) :=
    ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (congrArg Subtype.val
      (hA.1.1.comm x.1 y.1)))⟩⟩, fun x _ => Subtype.ext (hA.2 _ x.2)⟩
  rw [MonoidHom.range_eq_map]
  exact isElemAbelian_map _ htop

theorem range_thetaAct_le_inner {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (h : ∀ a ∈ A, ¬ InducesOuterTheta a L) :
    (thetaAct hAN).range ≤ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
  rintro _ ⟨a, rfl⟩
  by_contra hc
  exact h a a.2 ⟨hAN a.2, hc⟩

end Action

section Subgroups

variable {G : Type} [Group G] [Finite G]

theorem inducesOuterTheta_subgroupOf {H L : Subgroup G} (hLH : L ≤ H) {a : G} (haH : a ∈ H)
    (h : InducesOuterTheta a L) : InducesOuterTheta (⟨a, haH⟩ : H) (L.subgroupOf H) := by
  obtain ⟨ha, hout⟩ := h
  set φ := Subgroup.subgroupOfEquivOfLe hLH
  have ha' : (⟨a, haH⟩ : H) ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup H) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp ha x)
  refine ⟨ha', fun ⟨y, hy⟩ => hout ⟨thetaQuotCongr φ y, ?_⟩⟩
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    obtain ⟨w, rfl⟩ := φ.surjective z
    have hw := congrArg (fun τ : MulAut (L.subgroupOf H ⧸
      aschbacherSolvableCore 3 (L.subgroupOf H)) =>
        thetaQuotCongr φ (τ (w : L.subgroupOf H ⧸ aschbacherSolvableCore 3 (L.subgroupOf H)))) hy
    simp only [MulAut.conj_apply, map_mul, map_inv] at hw
    rw [MulAut.conj_apply, ← thetaQuotCongr_mk, hw]
    rfl

theorem mem_thetaComponents_subgroupOf {H L : Subgroup G} (hL : IsComponent L) (hLH : L ≤ H) :
    L.subgroupOf H ∈ thetaComponents 3 H :=
  mem_thetaComponents_of_isComponent3 (CFSG.LocalCores.component_overgroup hL hLH)

end Subgroups

section Triples

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) :
    IsPGroup 3 A := CFSG.Open.IsElemAbelian.isPGroup hA

omit [Finite G] in
theorem isElemAbelian_of_le {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) : CFSG.Assembly.IsElemAbelian 3 B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem exists_card_eq_of_four_lt_pRank {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hr : 4 < CFSG.Open.pRank 3 A) : ∃ m : ℕ, 5 ≤ m ∧ Nat.card A = 3 ^ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hA)
  refine ⟨m, ?_, hm⟩
  set S := {k | ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
    with hS
  have hne : S.Nonempty := ⟨0, ⊥, bot_le, ⟨⟨⟨fun x y => Subsingleton.elim _ _⟩⟩,
    fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩, by simp⟩
  have hbdd : BddAbove S := ⟨Nat.card G, by
    rintro k ⟨E, -, -, hE⟩
    calc k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group E⟩
  have hmem := Nat.sSup_mem hne hbdd
  have hpr : CFSG.Open.pRank 3 A = sSup S := rfl
  rw [← hpr] at hmem
  obtain ⟨E, hEA, -, hE⟩ := hmem
  have hdvd : 3 ^ CFSG.Open.pRank 3 A ∣ 3 ^ m := by
    rw [← hm, ← hE]
    exact Subgroup.card_dvd_of_le hEA
  have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
  omega

theorem exists_le_card_eq_81 {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) {m : ℕ}
    (hm4 : 4 ≤ m) (hm : Nat.card A = 3 ^ m) :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 3 (n := 4)
    (by rw [hm]; exact Nat.pow_dvd_pow 3 hm4)
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, isElemAbelian_of_le hA
    (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK]
  norm_num

theorem pCore_two_eq_bot_of_le_normalizer (hG : SectionFourHyp G) {L A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {m : ℕ} (hm4 : 4 ≤ m) (hm : Nat.card A = 3 ^ m)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) : CFSG.pCore 2 L = ⊥ := by
  by_contra hP1'
  set P : Subgroup G := (CFSG.pCore 2 L).map L.subtype
  have hP1 : P ≠ ⊥ := fun h => hP1'
    ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h)
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map _
  obtain ⟨E, hEA, hE, hE81⟩ := exists_le_card_eq_81 hA hm4 hm
  refine false_of_le_normalizer hG hP1 hP2 hE hE81 fun a ha => ?_
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have haN := hAN (hEA ha)
  set σ := L.normalizerMonoidHom ⟨a, haN⟩
  have hσ : (CFSG.pCore 2 L).map (σ : L →* L) = CFSG.pCore 2 L :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) σ
  have hσy : σ y ∈ CFSG.pCore 2 L := hσ ▸ Subgroup.mem_map_of_mem _ hy
  exact ⟨σ y, hσy, rfl⟩

theorem odd_card_center_of_le_normalizer (hG : SectionFourHyp G) {L A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {m : ℕ} (hm4 : 4 ≤ m) (hm : Nat.card A = 3 ^ m)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) : Odd (Nat.card (Subgroup.center L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 2
    (even_iff_two_dvd.mp hodd)
  have hnorm : (Subgroup.zpowers (z : L)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 k) g), mul_inv_cancel_right]
    exact hx
  have h2 : IsPGroup 2 (Subgroup.zpowers (z : L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]
  have hzP : (z : L) ∈ CFSG.pCore 2 L :=
    (le_sSup ⟨hnorm, h2⟩ : Subgroup.zpowers (z : L) ≤ CFSG.pCore 2 L) (Subgroup.mem_zpowers _)
  rw [pCore_two_eq_bot_of_le_normalizer hG hA hm4 hm hAN, Subgroup.mem_bot] at hzP
  have : z = 1 := Subtype.ext hzP
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem exists_inner_of_not_inducesOuterTheta {L : Subgroup G} (hL : CFSG.IsQuasisimple L)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (h : ¬ InducesOuterTheta a L) :
    ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := by
  have hin : thetaQuotMulAut L (compAction L ⟨a, ha⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
    by_contra hc
    exact h ⟨ha, hc⟩
  obtain ⟨l, hl⟩ := isInnerAut_of_thetaQuotMulAut hL hin
  refine ⟨l, l.2, fun x hx => ?_⟩
  have := congrArg (fun σ : MulAut L => ((σ ⟨x, hx⟩ : L) : G)) hl
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [this]
  rfl

omit [Finite G] in
theorem eq_sup_of_forall_inner {L A : Subgroup G} {c : G} (hZ : Subgroup.center L = ⊥)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
  have hA := hAmax.prop
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have huniq : ∀ l₁ ∈ L, ∀ l₂ ∈ L, (∀ x ∈ L, l₁ * x * l₁⁻¹ = l₂ * x * l₂⁻¹) → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ h
    have hmem : (⟨l₂⁻¹ * l₁, L.mul_mem (L.inv_mem h₂) h₁⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have := h x x.2
      calc (x : G) * (l₂⁻¹ * l₁) = l₂⁻¹ * (l₂ * x * l₂⁻¹) * l₁ := by group
        _ = l₂⁻¹ * (l₁ * x * l₁⁻¹) * l₁ := by rw [this]
        _ = l₂⁻¹ * l₁ * x := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simp only [Subgroup.coe_one] at this
    exact (inv_mul_eq_one.mp this).symm
  have hcA : Subgroup.zpowers c ≤ A := hAc ▸ inf_le_left
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) := hAc ▸ inf_le_right
  refine ⟨le_antisymm (fun a ha => ?_) (sup_le hcA inf_le_left), ?_⟩
  · obtain ⟨l, hl, hal⟩ := hinner a ha
    have hlA : ∀ b ∈ A, b * l = l * b := by
      intro b hb
      obtain ⟨m, hm, hbm⟩ := hinner b hb
      have hbl : b * l * b⁻¹ = m * l * m⁻¹ := hbm l hl
      have hml : m * l * m⁻¹ ∈ L := L.mul_mem (L.mul_mem hm hl) (L.inv_mem hm)
      have heq : m * l * m⁻¹ = l := by
        refine huniq _ hml _ hl fun x hx => ?_
        set y := m⁻¹ * x * m with hy
        have hyL : y ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hm) hx) hm
        have hxy : x = m * y * m⁻¹ := by rw [hy]; group
        have hayL : a * y * a⁻¹ ∈ L := by
          rw [hal y hyL]
          exact L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl)
        calc m * l * m⁻¹ * x * (m * l * m⁻¹)⁻¹ = m * (l * y * l⁻¹) * m⁻¹ := by
              rw [hxy]; group
          _ = m * (a * y * a⁻¹) * m⁻¹ := by rw [hal y hyL]
          _ = b * (a * y * a⁻¹) * b⁻¹ := (hbm _ hayL).symm
          _ = a * (b * y * b⁻¹) * a⁻¹ := by
              calc b * (a * y * a⁻¹) * b⁻¹ = (b * a) * y * (b * a)⁻¹ := by group
                _ = (a * b) * y * (a * b)⁻¹ := by rw [hcomm a ha b hb]
                _ = a * (b * y * b⁻¹) * a⁻¹ := by group
          _ = a * x * a⁻¹ := by rw [hbm y hyL, ← hxy]
          _ = l * x * l⁻¹ := hal x hx
      calc b * l = b * l * b⁻¹ * b := by group
        _ = l * b := by rw [hbl, heq]
    have hl3 : l ^ 3 = 1 := by
      refine huniq _ (L.pow_mem hl 3) _ L.one_mem fun x hx => ?_
      have key : ∀ y ∈ L, l * y * l⁻¹ ∈ L := fun y hy =>
        L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl)
      have hax : a * x * a⁻¹ ∈ L := by rw [hal x hx]; exact key x hx
      have haax : a * (a * x * a⁻¹) * a⁻¹ ∈ L := by rw [hal _ hax]; exact key _ hax
      have ha3 : a ^ 3 = 1 := hA.2 a ha
      calc l ^ 3 * x * (l ^ 3)⁻¹ = l * (l * (l * x * l⁻¹) * l⁻¹) * l⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = a * (a * (a * x * a⁻¹) * a⁻¹) * a⁻¹ := by
            rw [← hal x hx, ← hal _ hax, ← hal _ haax]
        _ = a ^ 3 * x * (a ^ 3)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
        _ = 1 * x * 1⁻¹ := by rw [ha3]
    have hlA' : l ∈ A := mem_of_maximal_of_commute hAmax hl3 hlA
    have hac : a * l⁻¹ ∈ Subgroup.zpowers c := by
      rw [← hAc]
      refine ⟨A.mul_mem ha (A.inv_mem hlA'), Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hx' : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
      have := hal _ hx'
      calc x * (a * l⁻¹) = a * (l⁻¹ * x * l) * a⁻¹ * (a * l⁻¹) := by
            rw [this]; group
        _ = a * l⁻¹ * x := by group
    have : a = a * l⁻¹ * l := by group
    rw [this]
    exact Subgroup.mul_mem_sup hac ⟨hlA', hl⟩
  · rw [eq_bot_iff]
    rintro y ⟨hyc, -, hyL⟩
    have hyC := hcC hyc
    have hmem : (⟨y, hyL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC x x.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

end Triples

end CFSG.RankThree.PartTwo.Sec4
