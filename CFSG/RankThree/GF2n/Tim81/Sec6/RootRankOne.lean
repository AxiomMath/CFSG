module

public import CFSG.RankThree.GF2n.Tim81.Sec6.RootSetupBasic
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs
public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.RankThree.GF2n.Tim81.Sec6.L2Extra
import CFSG.GH74.Uniqueness.Bender.Aut
import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.ClassicalInvolution.Asc77.AscThmAFitting
import CFSG.RankThree.GF2n.Tim81.Sec6.S65Local
import CFSG.Timmesfeld.ARS.Sec5Ten
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Tools
import CFSG.Timmesfeld.Bridge.RootClosureThree

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Bridge
open CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki
open CFSG.Timmesfeld.Bridge.RootClosure
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {X : Subgroup K} {Δ : Set (Subgroup K)} {f : ℕ}

private theorem RootSetup.exists_conj_of_mem (h : RootSetup X Δ f) {A' : Subgroup (quotY X)}
    (hA' : A' ∈ quotDelta X Δ) {a b : quotY X} (ha : a ∈ A') (ha1 : a ≠ 1) (hb : b ∈ A')
    (hb1 : b ≠ 1) : ∃ y : quotY X, y * a * y⁻¹ = b := by
  obtain ⟨A, hA, rfl⟩ := hA'
  obtain ⟨B, hB, hAB⟩ := h.partner A hA
  obtain ⟨y, -, hy, -⟩ := (h.isL2Gen_quotSub hA hB hAB).exists_conj_of_ne_one ha ha1 hb hb1
  exact ⟨y, hy⟩

private theorem RootSetup.exists_conj_rootElts (h : RootSetup X Δ f) {a b : quotY X}
    (ha : a ∈ rootElts (quotDelta X Δ)) (hb : b ∈ rootElts (quotDelta X Δ)) : IsConj a b := by
  obtain ⟨A', hA', haA', ha1⟩ := ha
  obtain ⟨B', hB', hbB', hb1⟩ := hb
  obtain ⟨A₀, hA₀⟩ := h.isTransvectionClass_quot.root.conj_class
  have hA₀mem : A₀ ∈ quotDelta X Δ := by
    rw [hA₀]
    exact ⟨1, conjSub_one A₀⟩
  have hA'range : A' ∈ Set.range (conjSub A₀) := by rw [← hA₀]; exact hA'
  have hB'range : B' ∈ Set.range (conjSub A₀) := by rw [← hA₀]; exact hB'
  obtain ⟨x, hx⟩ := hA'range
  obtain ⟨y, hy⟩ := hB'range
  have hai : x⁻¹ * a * x ∈ A₀ := by
    have h' : a ∈ conjSub A₀ x := by rwa [← hx] at haA'
    rw [conjSub] at h'
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp h'
    have hya' : x * y * x⁻¹ = a := by simpa [MulAut.conj_apply] using hya
    rw [← hya']
    have hxy : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rwa [hxy]
  have hbi : y⁻¹ * b * y ∈ A₀ := by
    have h' : b ∈ conjSub A₀ y := by rwa [← hy] at hbB'
    rw [conjSub] at h'
    obtain ⟨y', hy', hy'b⟩ := Subgroup.mem_map.mp h'
    have hy'b' : y * y' * y⁻¹ = b := by simpa [MulAut.conj_apply] using hy'b
    rw [← hy'b']
    have hxy : y⁻¹ * (y * y' * y⁻¹) * y = y' := by group
    rwa [hxy]
  have hai1 : x⁻¹ * a * x ≠ 1 := by
    intro hh
    apply ha1
    have h' : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rw [← h', hh, mul_one, mul_inv_cancel]
  have hbi1 : y⁻¹ * b * y ≠ 1 := by
    intro hh
    apply hb1
    have h' : y * (y⁻¹ * b * y) * y⁻¹ = b := by group
    rw [← h', hh, mul_one, mul_inv_cancel]
  obtain ⟨w, hw⟩ := h.exists_conj_of_mem hA₀mem hai hai1 hbi hbi1
  refine isConj_iff.mpr ⟨y * w * x⁻¹, ?_⟩
  calc (y * w * x⁻¹) * a * (y * w * x⁻¹)⁻¹
      = y * (w * (x⁻¹ * a * x) * w⁻¹) * y⁻¹ := by group
    _ = y * (y⁻¹ * b * y) * y⁻¹ := by rw [hw]
    _ = b := by group

theorem RootSetup.setup_rootElts (h : RootSetup X Δ f) :
    Timmesfeld.Bridge.Asc72.Setup (quotY X) (rootElts (quotDelta X Δ)) := by
  obtain ⟨T, hT⟩ := h.nonempty
  let T' : Subgroup (quotY X) := quotSub X T
  have hT'mem : T' ∈ quotDelta X Δ := ⟨T, hT, rfl⟩
  have h4q : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card T' = 2 ^ f := h.card_quotSub hT
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨d₀, hd₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT'ne
  have hd₀1 : (d₀ : quotY X) ≠ 1 := fun hh => hd₀ (Subtype.ext hh)
  have hd₀mem : (d₀ : quotY X) ∈ rootElts (quotDelta X Δ) := ⟨T', hT'mem, d₀.2, hd₀1⟩
  refine ⟨⟨(d₀ : quotY X), ?_⟩, ?_, ?_⟩
  · ext g
    constructor
    · exact h.exists_conj_rootElts hd₀mem
    · intro hg
      obtain ⟨c, rfl⟩ := isConj_iff.mp hg
      exact (conj_mem_rootElts_iff (R := quotDelta X Δ) h.isTransvectionClass_quot.root c).mpr
        hd₀mem
  · refine ⟨?_, ?_⟩
    · intro d hd
      obtain ⟨A', hA', hdA', hd1⟩ := hd
      have hd2 : d * d = 1 := h.isTransvectionClass_quot.root.mul_self A' hA' d hdA'
      exact orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1
    · intro d hd e he
      obtain ⟨A', hA', hdA', hd1⟩ := hd
      obtain ⟨B', hB', heB', he1⟩ := he
      have hd2 : d * d = 1 := h.isTransvectionClass_quot.root.mul_self A' hA' d hdA'
      have he2 : e * e = 1 := h.isTransvectionClass_quot.root.mul_self B' hB' e heB'
      by_cases hde : d = e
      · left
        rw [show d * e = d * d by rw [← hde], hd2]
        simp
      · by_cases hAB : A' = B'
        · subst hAB
          have hc : Commuting A' A' := fun a ha b hb => by
            have ha2 : a * a = 1 := h.isTransvectionClass_quot.root.mul_self A' hA' a ha
            have hb2 : b * b = 1 := h.isTransvectionClass_quot.root.mul_self A' hA' b hb
            have hab2 : (a * b) * (a * b) = 1 :=
              h.isTransvectionClass_quot.root.mul_self A' hA' (a * b) (A'.mul_mem ha hb)
            exact (commute_iff_mul_sq_eq_one ha2 hb2).mpr (by simpa [pow_two] using hab2)
          left
          exact orderOf_dvd_of_pow_eq_one
            ((commute_iff_mul_sq_eq_one hd2 he2).mp (hc d hdA' e heB'))
        · rcases h.quot_pair A' hA' B' hB' hAB with hcomm | hL2
          · left
            exact orderOf_dvd_of_pow_eq_one
              ((commute_iff_mul_sq_eq_one hd2 he2).mp
                ((commuting_iff_commutator_eq_bot.mpr hcomm) d hdA' e heB'))
          · right
            exact hL2.odd_orderOf_mul hdA' heB' hd1 he1
  · exact CFSG.Timmesfeld.ARS.Sec5.closure_rootElts_eq_top h.isTransvectionClass_quot.root

theorem RootSetup.meetsSq_rootElts (h : RootSetup X Δ f) :
    Timmesfeld.Bridge.OddTransp.MeetsSq (rootElts (quotDelta X Δ)) := by
  obtain ⟨T, hT⟩ := h.nonempty
  let T' : Subgroup (quotY X) := quotSub X T
  have hT'mem : T' ∈ quotDelta X Δ := ⟨T, hT, rfl⟩
  have hcard : Nat.card T' = 2 ^ f := h.card_quotSub hT
  have h4q : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have h4 : 4 ≤ Nat.card T' := by rw [hcard]; exact h4q
  have hne : T' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h4
    omega
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have huT' : (u : quotY X) ∈ T' := u.2
  have hu1' : (u : quotY X) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
  have hu2 : (u : quotY X) * u = 1 :=
    h.isTransvectionClass_quot.root.mul_self T' hT'mem u u.2
  have hzple : Subgroup.zpowers (u : quotY X) ≤ T' := Subgroup.zpowers_le.mpr u.2
  have hcard_zp : Nat.card (Subgroup.zpowers (u : quotY X)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rwa [pow_two]) hu1'
  have hT'ne : T' ≠ Subgroup.zpowers (u : quotY X) := by
    intro hEq
    rw [hEq, hcard_zp] at hcard
    omega
  have hnotsub : ¬ (T' : Set (quotY X)) ⊆ (Subgroup.zpowers (u : quotY X) : Set (quotY X)) := by
    intro hle
    exact hT'ne (le_antisymm hle hzple)
  obtain ⟨v, hvT', hvzp⟩ := Set.not_subset.mp hnotsub
  have hv1 : v ≠ 1 := by
    intro h1
    exact hvzp (h1 ▸ Subgroup.one_mem _)
  have hvu : v ≠ u := by
    intro hvu
    exact hvzp (hvu ▸ Subgroup.mem_zpowers _)
  have hv2 : v * v = 1 := h.isTransvectionClass_quot.root.mul_self T' hT'mem v hvT'
  have huvT' : (u : quotY X) * v ∈ T' := T'.mul_mem u.2 hvT'
  have huv2 : ((u : quotY X) * v) * ((u : quotY X) * v) = 1 :=
    h.isTransvectionClass_quot.root.mul_self T' hT'mem _ huvT'
  have hcomm : Commute (u : quotY X) v :=
    (commute_iff_mul_sq_eq_one hu2 hv2).mpr (by simpa [pow_two] using huv2)
  have huv1 : (u : quotY X) * v ≠ 1 := by
    intro h
    have h1 : (u : quotY X) = v := by
      rw [mul_eq_one_iff_eq_inv] at h
      rwa [inv_eq_of_mul_eq_one_right hv2] at h
    exact hvu h1.symm
  exact ⟨(u : quotY X), ⟨T', hT'mem, u.2, hu1'⟩, v, ⟨T', hT'mem, hvT', hv1⟩,
    hvu.symm, hcomm, ⟨T', hT'mem, huvT', huv1⟩⟩

private theorem RootSetup.isL2Gen_quotDelta_of_ne (h : RootSetup X Δ f)
    (hnc : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ ≠ ⊥) {A' B' : Subgroup (quotY X)}
    (hA' : A' ∈ quotDelta X Δ) (hB' : B' ∈ quotDelta X Δ) (hne : A' ≠ B') :
    IsL2Gen A' B' := by
  rcases h.quot_pair A' hA' B' hB' hne with hcomm | hL2
  · obtain ⟨A, hA, rfl⟩ := hA'
    obtain ⟨B, hB, rfl⟩ := hB'
    refine absurd ((h.commutator_quotSub_eq_bot_iff hA hB).mp hcomm) (hnc A hA B hB ?_)
    intro hAB
    exact hne (by rw [hAB])
  · exact hL2

theorem RootSetup.disconnected_rootElts (h : RootSetup X Δ f)
    (hnc : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ ≠ ⊥) :
    Timmesfeld.Connectivity.Disconnected (rootElts (quotDelta X Δ)) := by
  obtain ⟨T, hT⟩ := h.nonempty
  let T' : Subgroup (quotY X) := quotSub X T
  have hT'mem : T' ∈ quotDelta X Δ := ⟨T, hT, rfl⟩
  have h4q : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hcardT' : Nat.card T' = 2 ^ f := h.card_quotSub hT
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardT'
    omega
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT'ne
  have hu1' : (u : quotY X) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
  obtain ⟨B, hB, hTB⟩ := h.partner T hT
  let B' : Subgroup (quotY X) := quotSub X B
  have hB'mem : B' ∈ quotDelta X Δ := ⟨B, hB, rfl⟩
  have hL2 : IsL2Gen T' B' := h.isL2Gen_quotSub hT hB hTB
  have hcardB' : Nat.card B' = 2 ^ f := h.card_quotSub hB
  have hB'ne : B' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardB'
    omega
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB'ne
  have hv1' : (v : quotY X) ≠ 1 := fun hh => hv1 (Subtype.ext hh)
  have hS : ∀ x ∈ {x : quotY X | x ∈ T' ∧ x ≠ 1}, ∀ y ∈ rootElts (quotDelta X Δ),
      Commute x y → y ∈ {x : quotY X | x ∈ T' ∧ x ≠ 1} := by
    rintro x ⟨hxT, hx1⟩ y ⟨C', hC', hyC', hy1⟩ hc
    refine ⟨?_, hy1⟩
    by_contra hyT
    have hC'ne : C' ≠ T' := by
      intro hCT
      exact hyT (hCT ▸ hyC')
    have hL2' : IsL2Gen T' C' := h.isL2Gen_quotDelta_of_ne hnc hT'mem hC' hC'ne.symm
    exact (hL2'.not_commute_of_ne_one hxT hx1 hyC' hy1) hc
  refine ⟨(u : quotY X), ⟨T', hT'mem, u.2, hu1'⟩, (v : quotY X),
    ⟨B', hB'mem, v.2, hv1'⟩, ?_⟩
  intro hreach
  have hvS : (v : quotY X) ∈ {x : quotY X | x ∈ T' ∧ x ≠ 1} :=
    CFSG.Timmesfeld.Connectivity.mem_of_reach (D := rootElts (quotDelta X Δ)) hS
      (x := (u : quotY X)) (y := (v : quotY X)) ⟨u.2, hu1'⟩ hreach
  have hvTnot : (v : quotY X) ∉ T' := by
    intro hvT
    have hmem : (v : quotY X) ∈ T' ⊓ B' := ⟨hvT, v.2⟩
    rw [hL2.inf_eq_bot] at hmem
    exact hv1' (Subgroup.mem_bot.mp hmem)
  exact hvTnot hvS.1

theorem RootSetup.solvable_quot (h : RootSetup X Δ f) :
    ∀ N : Subgroup (quotY X), N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hsol
  have hF : CFSG.fittingSubgroup (quotY X) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [CFSG.fittingSubgroup, sSup_le_iff]
    rintro M ⟨hM, hMnil⟩
    rw [h.no_nilpotent_quot M hM hMnil]
  haveI : N.Normal := hN
  exact CFSG.ClassicalInvolution.Asc77.AscThmA.eq_bot_of_normal_of_isSolvable_of_fitting_eq_bot
    hF N hsol

theorem RootSetup.quotSub_eq_rootCenter (h : RootSetup X Δ f)
    (hnc : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ ≠ ⊥)
    (hBen : CFSG.BenderSuzuki.IsBenderGroup (quotY X)) {T : Subgroup K} (hT : T ∈ Δ)
    (Q : Sylow 2 (quotY X)) (hTQ : quotSub X T ≤ Q) :
    quotSub X T = CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup (quotY X)) := by
  let T' : Subgroup (quotY X) := quotSub X T
  have hT'mem : T' ∈ quotDelta X Δ := ⟨T, hT, rfl⟩
  have h4q : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hcardT' : Nat.card T' = 2 ^ f := h.card_quotSub hT
  have hT'ne : T' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardT'
    omega
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT'ne
  have ht1' : (t : quotY X) ≠ 1 := fun hh => ht1 (Subtype.ext hh)
  have htQ : (t : quotY X) ∈ (Q : Subgroup (quotY X)) := hTQ t.2
  have ht2 : (t : quotY X) * t = 1 :=
    h.isTransvectionClass_quot.root.mul_self T' hT'mem t t.2
  have htord : orderOf (t : quotY X) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1'
  apply le_antisymm
  · refine le_inf hTQ ?_
    refine Subgroup.le_centralizer_iff.mpr ?_
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha2 : a * a = 1 := h.isTransvectionClass_quot.root.mul_self T' hT'mem a ha
    exact (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one
      hBen Q (hTQ ha) ha2 q hq).eq
  · intro z hz
    obtain ⟨hzQ, hzc⟩ := Subgroup.mem_inf.mp hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Subgroup.one_mem _
    · have hz2 : z * z = 1 :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.mul_self_eq_one_of_commute hBen Q hzQ
          (fun y hy => (Subgroup.mem_centralizer_iff.mp hzc y hy).symm)
      have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
      obtain ⟨c, hc⟩ := isConj_iff.mp
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hBen hzord htord)
      have hzc' : z = c⁻¹ * (t : quotY X) * c := by
        rw [← hc]
        group
      let C' : Subgroup (quotY X) := conjSub T' c⁻¹
      have hC'mem : C' ∈ quotDelta X Δ :=
        h.isTransvectionClass_quot.root.conjSub_mem hT'mem c⁻¹
      have hzC' : z ∈ C' := by
        rw [hzc']
        simpa [C'] using conj_mem_conjSub c⁻¹ t.2
      have hcommzt : Commute z (t : quotY X) :=
        (Subgroup.mem_centralizer_iff.mp hzc t htQ).symm
      by_cases hC'T : C' = T'
      · rw [hC'T] at hzC'
        exact hzC'
      · have hL2 : IsL2Gen C' T' :=
          h.isL2Gen_quotDelta_of_ne hnc hC'mem hT'mem hC'T
        exact absurd hcommzt (hL2.not_commute_of_ne_one hzC' hz1 t.2 ht1')

theorem RootSetup.injective_conjAction (h : RootSetup X Δ f) {L : Subgroup K}
    (hLX : L ⊓ cenOf X = ⊥) :
    Function.Injective (normalizerToCenterQuotientAut X L (h.le_normalizer L)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [ker_normalizerToCenterQuotientAut h.isPerfect (h.le_normalizer L)]
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr inf_le_left]
  exact hLX

private theorem RootSetup.range_conjAction_le_autCentralizer (h : RootSetup X Δ f)
    {T L : Subgroup K} (hLT : L ≤ cenOf T) :
    (normalizerToCenterQuotientAut X L (h.le_normalizer L)).range ≤
      CFSG.GH74.Uniqueness.Bender.autCentralizer (quotSub X T) := by
  rintro σ ⟨l, rfl⟩ z hz
  obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hz
  have hxT : (x : K) ∈ T := Subgroup.mem_subgroupOf.mp hxX
  have hfix : normalizerConjAutOfMem X L (h.le_normalizer L) l x = x := by
    apply Subtype.ext
    change (l : K) * (x : K) * (l : K)⁻¹ = (x : K)
    rw [(hLT l.2 x hxT).symm, mul_inv_cancel_right]
  rw [← normalizerConjAutOfMem_comp_mk, hfix]

private theorem RootSetup.card_le_card_range_conjAction (h : RootSetup X Δ f) {L : Subgroup K}
    (hLX : L ⊓ cenOf X = ⊥) :
    Nat.card L ≤ Nat.card (normalizerToCenterQuotientAut X L (h.le_normalizer L)).range := by
  let ρ := normalizerToCenterQuotientAut X L (h.le_normalizer L)
  have hinj : Function.Injective ρ := h.injective_conjAction hLX
  exact Nat.card_le_card_of_injective (MonoidHom.rangeRestrict ρ) (by
    intro a b hab
    exact hinj (Subtype.ext_iff.mp hab))

private theorem RootSetup.card_le_of_linear (h : RootSetup X Δ f)
    {T L : Subgroup K} (hT : T ∈ Δ) (hLT : L ≤ cenOf T) (hLX : L ⊓ cenOf X = ⊥)
    {n : ℕ} (hBT : BenderType (quotY X) n 1 1) (Q : Sylow 2 (quotY X))
    (hroot : quotSub X T = rootCenter (Q : Subgroup (quotY X))) :
    Nat.card L ≤ 2 * (2 ^ f) ^ 3 := by
  let ρ := normalizerToCenterQuotientAut X L (h.le_normalizer L)
  have hLR : Nat.card L ≤ Nat.card ρ.range := h.card_le_card_range_conjAction hLX
  have hRle : ρ.range ≤ autCentralizer (quotSub X T) := h.range_conjAction_le_autCentralizer hLT
  rw [hroot] at hRle
  obtain ⟨t, hC⟩ := BenderType.exists_benderCore hBT Q
  have hQeq : (Q : Subgroup (quotY X)) = rootCenter (Q : Subgroup (quotY X)) := by
    refine (Subgroup.eq_of_le_of_card_ge (rootCenter_le _) ?_).symm
    rw [hC.card_eq, hC.card_center]
    simp
  have hfixQ : ∀ σ ∈ ρ.range, ∀ x ∈ (Q : Subgroup (quotY X)), σ x = x := by
    intro σ hσ x hx
    have hxT : x ∈ quotSub X T := by
      rw [hroot, ← hQeq]
      exact hx
    rw [hroot] at hxT
    exact (mem_autCentralizer_iff.mp (hRle hσ)) x hxT
  have hcardR : Nat.card ρ.range ≤ Nat.card (rootCenter (Q : Subgroup (quotY X))) := by
    refine Nat.card_le_card_of_injective
      (fun σ : ρ.range =>
        (⟨Classical.choose (BenderType.lemma_3_6_a hBT Q σ.1 (hfixQ σ.1 σ.2)),
          (Classical.choose_spec (BenderType.lemma_3_6_a hBT Q σ.1 (hfixQ σ.1 σ.2))).1⟩ :
            rootCenter (Q : Subgroup (quotY X)))) ?_
    intro σ τ hστ
    have hσspec := Classical.choose_spec (BenderType.lemma_3_6_a hBT Q σ.1 (hfixQ σ.1 σ.2))
    have hτspec := Classical.choose_spec (BenderType.lemma_3_6_a hBT Q τ.1 (hfixQ τ.1 τ.2))
    have hval : Classical.choose (BenderType.lemma_3_6_a hBT Q σ.1 (hfixQ σ.1 σ.2)) =
        Classical.choose (BenderType.lemma_3_6_a hBT Q τ.1 (hfixQ τ.1 τ.2)) :=
      congrArg Subtype.val hστ
    apply Subtype.ext
    ext k
    rw [hσspec.2 k, hτspec.2 k, hval]
  have hrootcard : Nat.card (rootCenter (Q : Subgroup (quotY X))) = 2 ^ n := hC.card_center
  have hpow : 2 ^ n = 2 ^ f := by
    have h1 : Nat.card (quotSub X T) = 2 ^ f := h.card_quotSub hT
    rw [hroot, hrootcard] at h1
    exact h1
  calc Nat.card L ≤ Nat.card ρ.range := hLR
    _ ≤ Nat.card (rootCenter (Q : Subgroup (quotY X))) := hcardR
    _ = 2 ^ n := hrootcard
    _ = 2 ^ f := hpow
    _ ≤ 2 * (2 ^ f) ^ 3 := by
        have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        have hq3 : 2 ^ f ≤ (2 ^ f) ^ 3 := le_self_pow hq1 (by norm_num : (3 : ℕ) ≠ 0)
        calc 2 ^ f ≤ (2 ^ f) ^ 3 := hq3
          _ ≤ 2 * (2 ^ f) ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)

private theorem card_le_two_mul_card_of_normal_sup {M : Type*} [Group M] [Finite M]
    {A D R : Subgroup M} {m : ℕ} (hAnorm : (A.subgroupOf (A ⊔ D)).Normal)
    (hAD : A ⊓ D = ⊥) (hDcard : Nat.card D = 2 * m) (hm : Odd m)
    (hR : R ≤ A ⊔ D) (hR2 : IsPGroup 2 R) :
    Nat.card R ≤ 2 * Nat.card A := by
  let H : Subgroup M := A ⊔ D
  let A' : Subgroup H := A.subgroupOf H
  let D' : Subgroup H := D.subgroupOf H
  let R' : Subgroup H := R.subgroupOf H
  have hAnorm' : A'.Normal := hAnorm
  haveI : A'.Normal := hAnorm'
  have hA_le_H : A ≤ H := le_sup_left
  have hD_le_H : D ≤ H := le_sup_right
  have hRleH : R ≤ H := hR
  let S : Subgroup (H ⧸ A') := R'.map (QuotientGroup.mk' A')
  have hA'D' : A' ⊓ D' = ⊥ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxD⟩ := Subgroup.mem_inf.mp hx
      have h1 : (x : M) ∈ A := Subgroup.mem_subgroupOf.mp hxA
      have h2 : (x : M) ∈ D := Subgroup.mem_subgroupOf.mp hxD
      have hxbot : (x : M) ∈ (⊥ : Subgroup M) := by
        rw [← hAD]
        exact ⟨h1, h2⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
  have hA'D'sup : A' ⊔ D' = ⊤ := by
    have h := Subgroup.subgroupOf_sup hA_le_H hD_le_H
    rw [Subgroup.subgroupOf_self] at h
    exact h.symm
  have hD'card : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_H).toEquiv
  have hDmapcard : Nat.card (D'.map (QuotientGroup.mk' A')) = 2 * m := by
    have h := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
      (QuotientGroup.mk' A') D'
    rw [show (QuotientGroup.mk' A').ker = A' from QuotientGroup.ker_mk' A', hA'D',
      Subgroup.card_bot, Nat.mul_one] at h
    rw [hD'card, hDcard] at h
    exact h.symm
  have hSle : S ≤ D'.map (QuotientGroup.mk' A') := by
    have h1 : R' ≤ A' ⊔ D' := by rw [hA'D'sup]; exact le_top
    have h2 := Subgroup.map_mono (f := QuotientGroup.mk' A') h1
    have hAmap : A'.map (QuotientGroup.mk' A') = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    simpa [S, Subgroup.map_sup, hAmap] using h2
  have hSpg : IsPGroup 2 S := by
    have hR'pg : IsPGroup 2 R' := hR2.comap_subtype
    simpa [S] using hR'pg.map (QuotientGroup.mk' A')
  have hScard : Nat.card S ≤ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSpg
    have hdvd : Nat.card S ∣ 2 * m := hDmapcard ▸ Subgroup.card_dvd_of_le hSle
    rw [hk] at hdvd ⊢
    exact Nat.le_of_dvd two_pos
      (((Nat.coprime_two_left.mpr hm).pow_left k).dvd_of_dvd_mul_right hdvd)
  have hRcard : Nat.card R' = Nat.card S * Nat.card ↥(A' ⊓ R') := by
    have h := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf
      (QuotientGroup.mk' A') R'
    rw [show (QuotientGroup.mk' A').ker = A' from QuotientGroup.ker_mk' A'] at h
    simpa [S] using h
  have hR'card : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleH).toEquiv
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_H).toEquiv
  calc Nat.card R = Nat.card R' := hR'card.symm
    _ = Nat.card S * Nat.card ↥(A' ⊓ R') := hRcard
    _ ≤ 2 * Nat.card ↥(A' ⊓ R') := Nat.mul_le_mul_right _ hScard
    _ ≤ 2 * Nat.card A' := Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le inf_le_left)
    _ = 2 * Nat.card A := by rw [hA'card]

private theorem RootSetup.card_le_of_unitary (h : RootSetup X Δ f)
    {T L : Subgroup K} (hT : T ∈ Δ) (hL : IsPGroup 2 L) (hLT : L ≤ cenOf T)
    (hLX : L ⊓ cenOf X = ⊥)
    {n e : ℕ} (hn : 2 ≤ n) (hBT : BenderType (quotY X) n 3 e) (Q : Sylow 2 (quotY X))
    (hroot : quotSub X T = rootCenter (Q : Subgroup (quotY X))) :
    Nat.card L ≤ 2 * (2 ^ f) ^ 3 := by
  let ρ := normalizerToCenterQuotientAut X L (h.le_normalizer L)
  have hLR : Nat.card L ≤ Nat.card ρ.range := h.card_le_card_range_conjAction hLX
  have hRle : ρ.range ≤ autCentralizer (quotSub X T) := h.range_conjAction_le_autCentralizer hLT
  rw [hroot] at hRle
  obtain ⟨t, hC⟩ := BenderType.exists_benderCore hBT Q
  obtain ⟨D, hDinf, hDsup, hDnorm, hDcard, hDdihedral⟩ :=
    BenderType.lemma_3_6_c_unitary hBT Q
  let A : Subgroup (MulAut (quotY X)) :=
    Subgroup.map (MulAut.conj : quotY X →* MulAut (quotY X)) (Q : Subgroup (quotY X))
  have hAnorm : (A.subgroupOf (A ⊔ D)).Normal := by
    rw [hDsup]
    exact hDnorm
  have hRle' : ρ.range ≤ A ⊔ D := by
    rw [hDsup]
    exact hRle
  have hR2 : IsPGroup 2 ρ.range :=
    IsPGroup.of_surjective hL (MonoidHom.rangeRestrict ρ)
      (MonoidHom.rangeRestrict_surjective ρ)
  have hodd : Odd (2 ^ n + 1) := by
    have hne : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
    exact Even.add_one (Even.pow_of_ne_zero even_two hne)
  have hbound : Nat.card ρ.range ≤ 2 * Nat.card A :=
    card_le_two_mul_card_of_normal_sup hAnorm hDinf hDcard hodd hRle' hR2
  have hAcard_le : Nat.card A ≤ (2 ^ n) ^ 3 := by
    have hdvd : Nat.card A ∣ Nat.card (Q : Subgroup (quotY X)) := by
      simpa [A] using Subgroup.card_map_dvd (Q : Subgroup (quotY X))
        (MulAut.conj : quotY X →* MulAut (quotY X))
    calc Nat.card A ≤ Nat.card (Q : Subgroup (quotY X)) := Nat.le_of_dvd Nat.card_pos hdvd
      _ = (2 ^ n) ^ 3 := hC.card_eq
  have hpow : 2 ^ n = 2 ^ f := by
    have h1 : Nat.card (quotSub X T) = 2 ^ f := h.card_quotSub hT
    rw [hroot, hC.card_center] at h1
    exact h1
  calc Nat.card L ≤ Nat.card ρ.range := hLR
    _ ≤ 2 * Nat.card A := hbound
    _ ≤ 2 * (2 ^ n) ^ 3 := Nat.mul_le_mul_left 2 hAcard_le
    _ = 2 * (2 ^ f) ^ 3 := by rw [hpow]

theorem RootSetup.card_le_of_bender (h : RootSetup X Δ f)
    (hnc : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ ≠ ⊥)
    (hBen : CFSG.BenderSuzuki.IsBenderGroup (quotY X)) {T L : Subgroup K} (hT : T ∈ Δ)
    (hL : IsPGroup 2 L) (hLT : L ≤ cenOf T) (hLX : L ⊓ cenOf X = ⊥) :
    Nat.card L ≤ 2 * (2 ^ f) ^ 3 := by
  have hT'pg : IsPGroup 2 (quotSub X T) :=
    ((h.isPGroup hT).comap_subtype (K := X)).map (quotMap X)
  obtain ⟨Q, hTQ⟩ := hT'pg.exists_le_sylow
  have hroot : quotSub X T = rootCenter (Q : Subgroup (quotY X)) :=
    h.quotSub_eq_rootCenter hnc hBen hT Q hTQ
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.mp hBen
  cases hBT with
  | linear n hn e =>
      exact h.card_le_of_linear hT hLT hLX (BenderType.linear n hn e) Q hroot
  | suzuki a ha e =>
      obtain ⟨B, hB, hL2⟩ := h.partner T hT
      obtain ⟨x, hxT, y, hyB, hxy⟩ :=
        IsL2Gen.exists_orderOf_eq_three (h.isL2Gen_quotSub hT hB hL2)
      have h3 : 3 ∣ Nat.card (quotY X) := by
        rw [← hxy]
        exact orderOf_dvd_natCard (x * y)
      have hcardY : Nat.card (quotY X) = Nat.card (SzModel a) := Nat.card_congr e.toEquiv
      exact absurd (hcardY ▸ h3) (not_three_dvd_card_szModel ha)
  | unitary n hn e =>
      exact h.card_le_of_unitary (T := T) (L := L) (n := n) hT hL hLT hLX
        (by omega) (BenderType.unitary n hn e) Q hroot

theorem RootSetup.exists_commuting_of_large
    (h : RootSetup X Δ f) (hB : Timmesfeld.Bridge.OddTranspBender) {T L : Subgroup K}
    (hT : T ∈ Δ) (hL : IsPGroup 2 L) (hLT : L ≤ cenOf T) (hLX : L ⊓ cenOf X = ⊥)
    (hcard : 2 * (2 ^ f) ^ 3 < Nat.card L) : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ ⁅A, B⁆ = ⊥ := by
  by_contra hcon
  have hnc : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ ≠ ⊥ := by
    intro A hA B hB hAB hcomm
    exact hcon ⟨A, hA, B, hB, hAB, hcomm⟩
  have hBen : CFSG.BenderSuzuki.IsBenderGroup (quotY X) :=
    hB (quotY X) (rootElts (quotDelta X Δ)) h.setup_rootElts h.solvable_quot
      h.meetsSq_rootElts (h.disconnected_rootElts hnc)
  have hbound := h.card_le_of_bender hnc hBen hT hL hLT hLX
  exact (not_lt_of_ge hbound) hcard

end CFSG.RankThree.GF2n.Tim81
