module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofF
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXCover
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec19.Step1913
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68Tools
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofEnd
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.RankThree.PartTwo.Sec15.Item152StepsEnd

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Proof152FX

open Proof152Gen CFSG.SectionRank.Ccomm

variable {G : Type} [Group G] [Finite G]

theorem map_inf_eq_top_of_cent
    (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {Y M X : Subgroup G} (hctx : Ctx152 A (lB A) Y M X) {d : G} (hdA : d ∈ A)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {c, d} : Set G)) :
    ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quot_of_ctx152 hctx
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := pPrimeCoreOf 3 H with hO
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hcA : c ∈ A := hS13.mem_A
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hS13.commute ha hcA)
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H :=
    centralizer_singleton_le_normalizer_zpowers c
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_j2 h hJ
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 H
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 H)
  have hOc : O ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hcA hS13.orderOf_eq
      ⟨pPrimeCoreOf_le 3 H, (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3,
        (hAC.trans hCH).trans hHO⟩
  have hOL : O ≤ Subgroup.normalizer (L : Set G) := hOc.trans hCL
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hctx.norm_x
  have hXθ : X ≤ Subgroup.normalizer (θX : Set G) := Sec6.le_normalizer_theta X
  have hAθ : A ≤ Subgroup.normalizer (θX : Set G) :=
    hAX.trans (Sec6.normalizer_le_normalizer_theta X)
  have hsc : Late.sectionCentralizer A X θX = (Subgroup.closure {c, d} : Set G) := hcent
  have hcC : c ∈ Sec4.thetaQuotCentralizer X := by
    have hcsc : c ∈ Late.sectionCentralizer A X θX := by
      rw [hsc]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX hcA, fun l hl => ?_⟩
    have h1 := hcsc.2 l hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (hXθ (inv_mem hl)) _).mp h1
    have he : l⁻¹ * (c * l * c⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (c * l * c⁻¹) := by group
    rw [he] at h2
    exact h2
  set N := X ⊓ (L ⊔ O) with hN
  have hLON : L ⊔ O ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hOL
  have hcovc : ((X ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
    refine map_inf_centralizer_eq_top le_rfl (hAX hcA) hc3 hcC ?_
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hCN : X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (le_normalizer_sup hCL (hCH.trans hHO)))
  have hNn := map_subgroupOf_normal_of_le_normalizer hCN hcovc
  have hNne : (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) ≠ ⊥ := by
    intro hbot
    have hNθ : ∀ n ∈ N, n ∈ θX := by
      intro n hn
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨n, hn.1⟩ ∈
          (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
        ⟨⟨n, hn.1⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact ⟨⟨n, hn.1⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    have hAcent : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ θX := by
      intro a ha
      have hQ : ∀ Q ∈ collectionIn (scriptQ A (lB A)) X, ∀ q ∈ Q,
          (a * q * a⁻¹)⁻¹ * q ∈ θX := by
        rintro Q ⟨hQ, hQX⟩ q hq
        have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.2.2
        set W := Q ⊓ Subgroup.centralizer ({c} : Set G) with hW
        have hWinv : W ∈ invariantPiSubgroups H A (piCompl 3) :=
          ⟨inf_le_right.trans hCH,
            fun r hr => hQ.1.2.1 r (hr.trans (Subgroup.card_dvd_of_le inf_le_left)),
            Late.le_normalizer_inf hAQ (hAC.trans Subgroup.le_normalizer)⟩
        have hWX : W ≤ X := inf_le_left.trans hQX
        have hWA : ⁅W, A⁆ ≤ N := by
          refine le_inf (Subgroup.commutator_le.mpr fun w hw b hb => ?_)
            (commutator_le_sup_of_item142 h hJ (h142 G A c L h) hWinv)
          have h3 : ⁅w, b⁆ = w * (b * w⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
          rw [h3]
          exact mul_mem (hWX hw)
            ((Subgroup.mem_normalizer_iff.mp (hAX hb) _).mp (inv_mem (hWX hw)))
        have himg := map_inf_centralizer_eq hQX (hAQ hcA) hc3 hcC
        have hq' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨q, hQX hq⟩ ∈
            ((Q ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf X).map
              (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := by
          rw [himg]
          exact ⟨_, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
        obtain ⟨w, hwW, hwq⟩ := hq'
        have hwW' : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hwW
        have ht : (w : G)⁻¹ * q ∈ θX := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwq
          refine ⟨w⁻¹ * ⟨q, hQX hq⟩, hwq, ?_⟩
          simp
        have hwa : a * (w : G) * a⁻¹ * (w : G)⁻¹ ∈ θX := by
          have h1 := hNθ _ (hWA (Subgroup.commutator_mem_commutator hwW' ha))
          have h2 := inv_mem h1
          rw [commutatorElement_inv, commutatorElement_def] at h2
          exact h2
        have hwX : (w : G) ∈ X := w.2
        have h1 : a * ((w : G)⁻¹ * q)⁻¹ * a⁻¹ ∈ θX :=
          (Subgroup.mem_normalizer_iff.mp (hAθ ha) _).mp (inv_mem ht)
        have h2 : (w : G)⁻¹ * (a * w * a⁻¹ * (w : G)⁻¹)⁻¹ * (w : G)⁻¹⁻¹ ∈ θX :=
          (Subgroup.mem_normalizer_iff.mp (hXθ (inv_mem hwX)) _).mp (inv_mem hwa)
        have he : (a * q * a⁻¹)⁻¹ * q = (a * ((w : G)⁻¹ * q)⁻¹ * a⁻¹) *
            ((w : G)⁻¹ * (a * w * a⁻¹ * (w : G)⁻¹)⁻¹ * (w : G)⁻¹⁻¹) * ((w : G)⁻¹ * q) := by
          group
        rw [he]
        exact mul_mem (mul_mem h1 h2) ht
      let f : ↥X →* ↥X ⧸ aschbacherSolvableCore 3 ↥X :=
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp
          (X.normalizerMonoidHom ⟨a, hAX ha⟩).toMonoidHom
      have hc : ∀ x : ↥X, (((X.normalizerMonoidHom ⟨a, hAX ha⟩ x)⁻¹ * x : ↥X) : G) =
          (a * (x : G) * a⁻¹)⁻¹ * x := by
        intro x
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
      have hE : ∀ x : ↥X, (a * (x : G) * a⁻¹)⁻¹ * x ∈ θX →
          x ∈ f.eqLocus (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := by
        intro x hx
        change QuotientGroup.mk' _ (X.normalizerMonoidHom ⟨a, hAX ha⟩ x) = QuotientGroup.mk' _ x
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        refine (Subgroup.mem_map_iff_mem X.subtype_injective).mp ?_
        rw [Subgroup.coe_subtype, hc]
        exact hx
      have hE' : ∀ x : ↥X, x ∈ f.eqLocus (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) →
          (a * (x : G) * a⁻¹)⁻¹ * x ∈ θX := by
        intro x hx
        have hx' : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)
            (X.normalizerMonoidHom ⟨a, hAX ha⟩ x) =
            QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) x := hx
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hx'
        rw [← hc]
        exact ⟨_, hx', rfl⟩
      have hXE : X ≤ (f.eqLocus (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).map
          X.subtype := by
        refine hctx.delta_x.le.trans (sSup_le fun Q hQ' => ?_)
        intro q hq
        exact ⟨⟨q, hQ'.2 hq⟩, hE _ (hQ Q hQ' q hq), rfl⟩
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hXE hx
      have hu := hE' y hy
      have he : a * (y : G) * a⁻¹ * (y : G)⁻¹ =
          (y : G) * ((a * y * a⁻¹)⁻¹ * y)⁻¹ * (y : G)⁻¹ := by group
      rw [Subgroup.coe_subtype, he]
      have h := (Subgroup.mem_normalizer_iff.mp (hXθ y.2) _).mp (inv_mem hu)
      exact h
    have hdA := hdA
    have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
    have hAsub : A ≤ Subgroup.closure ({c, d} : Set G) := by
      intro a ha
      have h1 : a ∈ Late.sectionCentralizer A X θX := ⟨ha, hAcent a ha⟩
      rw [hsc] at h1
      exact h1
    have hcd : Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ Subgroup.zpowers d, x * y = y * x :=
      fun x hx y hy =>
        hS13.commute (Subgroup.zpowers_le.mpr hcA hx) (Subgroup.zpowers_le.mpr hdA hy)
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hc' : Nat.card (Subgroup.zpowers c) = 3 := hS13.card_zpowers
    have hd' : Nat.card (Subgroup.zpowers d) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hd3)
    have hpos : 0 < Nat.card (Subgroup.zpowers c ⊓ Subgroup.zpowers d : Subgroup G) :=
      Nat.card_pos
    have h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) ≤
        3 * Nat.card (Subgroup.zpowers d) := by
      rw [← hc', ← h1]
      exact Nat.le_mul_of_pos_right _ hpos
    have hle := Subgroup.card_le_of_le hAsub
    rw [hcd, hA.2] at hle
    omega
  have hNtop : (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
    hNn.eq_bot_or_eq_top.resolve_left hNne
  have hMn := map_subgroupOf_normal_of_le_normalizer (V := X ⊓ L)
    (Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans hLON)) hNtop
  have hMne : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) ≠
      ⊥ := by
    intro hbot
    obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥X ⧸ aschbacherSolvableCore 3 ↥X) 3 (by rw [hX60]; norm_num)
    have hxbN : xb ∈ (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
      hNtop ▸ Subgroup.mem_top xb
    obtain ⟨m, hmN, rfl⟩ := hxbN
    have hm0 : orderOf m ≠ 0 := (orderOf_pos m).ne'
    obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
    have hmr : ((m ^ r : ↥X) : G) ^ (3 ^ e) = 1 := by
      rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one, Subgroup.coe_one]
    have hmLO : ((m ^ r : ↥X) : G) ∈ L ⊔ O := by
      rw [Subgroup.coe_pow]
      exact pow_mem (Subgroup.mem_subgroupOf.mp hmN).2 r
    have hmrL : ((m ^ r : ↥X) : G) ∈ L :=
      Sec6.mem_of_mem_sup_of_pow_eq_one hOL hO3 hmLO hmr
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (m ^ r) ∈
        ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
      ⟨_, Subgroup.mem_subgroupOf.mpr ⟨(m ^ r).2, hmrL⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hxb] at h2
    exact hr3 h2
  exact hMn.eq_bot_or_eq_top.resolve_left hMne

theorem exists_sylow_of_isSylowOf {p : ℕ} [Fact p.Prime] {X R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype)) :
    ∃ Q : Sylow p ↥(Sec4.oTwoP p ↥X),
      ((Q : Subgroup ↥(Sec4.oTwoP p ↥X)).map (Sec4.oTwoP p ↥X).subtype).map X.subtype = R := by
  obtain ⟨Q', hQ'⟩ := hR
  let e : ↥(Sec4.oTwoP p ↥X) ≃* ↥((Sec4.oTwoP p ↥X).map X.subtype) :=
    (Sec4.oTwoP p ↥X).equivMapOfInjective X.subtype X.subtype_injective
  let Q : Sylow p ↥(Sec4.oTwoP p ↥X) :=
    Q'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨Q, ?_⟩
  have hcomp : (X.subtype.comp (Sec4.oTwoP p ↥X).subtype).comp e.symm.toMonoidHom =
      ((Sec4.oTwoP p ↥X).map X.subtype).subtype := by
    ext k
    exact congrArg Subtype.val (e.apply_symm_apply k)
  have hQc : (Q : Subgroup ↥(Sec4.oTwoP p ↥X)) =
      (Q' : Subgroup ↥((Sec4.oTwoP p ↥X).map X.subtype)).map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  rw [hQc, Subgroup.map_map, Subgroup.map_map, hcomp, hQ']

theorem exists_mul_of_mem_oTwoP {p : ℕ} [Fact p.Prime] {X R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype)) {o : G}
    (ho : o ∈ (Sec4.oTwoP p ↥X).map X.subtype) :
    ∃ r ∈ R, ∃ q ∈ CFSG.Open.pCoreOf 2 X, o = r * q := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_isSylowOf hR
  let f : ↥(Sec4.oTwoP p ↥X) →* ↥X ⧸ CFSG.pCore 2 ↥X :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Sec4.oTwoP p ↥X).subtype
  have hfr : IsPGroup p f.range := by
    refine (CFSG.pCore_isPGroup (p := p) (G := ↥X ⧸ CFSG.pCore 2 ↥X)).to_le ?_
    rintro _ ⟨x, rfl⟩
    exact x.2
  let Qf : Sylow p f.range := Q.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have hQf : (Qf : Subgroup f.range) = ⊤ := (Qf.is_maximal' (hfr.to_subgroup ⊤) le_top).symm
  obtain ⟨o', ho', rfl⟩ := ho
  have hmem : f.rangeRestrict ⟨o', ho'⟩ ∈ (Qf : Subgroup f.range) := hQf ▸ Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hmem
  obtain ⟨r, hr, hrf⟩ := hmem
  have hker : ((r : ↥(Sec4.oTwoP p ↥X)) : ↥X)⁻¹ * o' ∈ CFSG.pCore 2 ↥X := by
    have h1 := congrArg Subtype.val hrf
    change QuotientGroup.mk' _ ((r : ↥(Sec4.oTwoP p ↥X)) : ↥X) = QuotientGroup.mk' _ o' at h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact h1
  refine ⟨(((r : ↥(Sec4.oTwoP p ↥X)) : ↥X) : G), ?_,
    ((((r : ↥(Sec4.oTwoP p ↥X)) : ↥X)⁻¹ * o' : ↥X) : G), ?_, ?_⟩
  · rw [← hQ]
    exact ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  · rw [CFSG.Open.pCoreOf]
    exact ⟨_, hker, rfl⟩
  · simp

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) :=
  le_normalizer_sup (A := Subgroup.zpowers g) (Subgroup.zpowers_le.mpr hH)
    (Subgroup.zpowers_le.mpr hK) (Subgroup.mem_zpowers g)

theorem le_normalizer_sup_pCoreOf {p : ℕ} [Fact p.Prime] {X P : Subgroup G}
    (hchar : ∃ R : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p R ((Sec4.oTwoP p ↥X).map X.subtype) ∧ P ≤ R ∧
        (P.subgroupOf R).Characteristic) :
    X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR, hPR, hPc⟩ := hchar
  obtain ⟨Q, hQ⟩ := exists_sylow_of_isSylowOf hR
  have hOn : (Sec4.oTwoP p ↥X).Normal := Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _
  have hF := Sylow.normalizer_sup_eq_top Q
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hNRP : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := R)
      (P.subgroupOf R)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPR] at h
  have hRP : R ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPR).mp (Subgroup.normal_of_characteristic _)
  have hRX : R ≤ X := by
    obtain ⟨Q', hQ'⟩ := hR
    exact hQ' ▸ (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer
      ((Q : Subgroup ↥(Sec4.oTwoP p ↥X)).map (Sec4.oTwoP p ↥X).subtype : Set ↥X) ⊔
        Sec4.oTwoP p ↥X :=
    hF ▸ Subgroup.mem_top _
  obtain ⟨n, hn, o, ho, hno⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hnR : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hQ]
    exact Subgroup.le_normalizer_map X.subtype ⟨n, hn, rfl⟩
  obtain ⟨r, hr, q, hq, hoq⟩ := exists_mul_of_mem_oTwoP hR ⟨o, ho, rfl⟩
  have hxe : x = (n : G) * r * q := by
    have h1 : (n : G) * (o : G) = x := by simpa using congrArg Subtype.val hno
    have hoq' : (o : G) = r * q := hoq
    rw [← h1, hoq', mul_assoc]
  rw [hxe]
  refine mul_mem (mul_mem (mem_normalizer_sup (hNRP hnR) (hXQ n.2))
    (mem_normalizer_sup (hRP hr) (hXQ (hRX hr)))) ?_
  exact Subgroup.le_normalizer ((le_sup_right : CFSG.Open.pCoreOf 2 X ≤ _) hq)

theorem isPGroup_theta_of_item135 (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G}
    {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    IsPGroup 2 (aschbacherSolvableCore 3 ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := h135 G A c L h.toSec13Data h.hypS_or_hypT
  have hθ := Sec19.theta_eq_pCore_two_of_mult hmult hq (Or.inr (Or.inr (Or.inl hJ)))
  rw [hθ]
  exact CFSG.pCore_isPGroup

theorem not_sq_dvd_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 10080 := by
  intro h
  have hle : p ^ 2 ≤ 10080 := Nat.le_of_dvd (by norm_num) h
  have hp100 : p < 101 := by
    by_contra hc
    have : 101 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp hc) 2
    omega
  have hcop : Nat.Coprime 6 p := by
    have h6 : ¬ p ∣ 6 := by
      intro h6
      rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 3 by simpa using h6) with h' | h'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h6)
  have hcheck : ∀ q < 101, Nat.Coprime 6 q → 2 ≤ q → ¬ q ^ 2 ∣ 10080 := by decide +kernel
  exact hcheck p hp100 hcop hp.two_le h

theorem false_of_le_sup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {X L P : Subgroup G}
    (hθL : IsPGroup 2 (aschbacherSolvableCore 3 ↥L))
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hX60 : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) = 60)
    (hZcov : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hPX : P ≤ X) (hHθ : P ⊔ CFSG.Open.pCoreOf 2 X ≤ (aschbacherSolvableCore 3 ↥X).map X.subtype)
    (hP2 : p ^ 2 ∣ Nat.card P)
    (hPR : P ≤ (L ⊓ (P ⊔ CFSG.Open.pCoreOf 2 X)) ⊔ CFSG.Open.pCoreOf 2 X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  set H := P ⊔ Q with hH
  set R := L ⊓ H with hRdef
  set Z := X ⊓ L with hZdef
  set θX := aschbacherSolvableCore 3 ↥X with hθX
  set θL := aschbacherSolvableCore 3 ↥L with hθL'
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hHXle : H ≤ X := sup_le hPX hQX
  have hRZ : R ≤ Z := le_inf (inf_le_right.trans hHXle) inf_le_left
  have hZL : Z ≤ L := inf_le_right
  have hZX : Z ≤ X := inf_le_left
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) :=
    (hRZ.trans hZX).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have h1 : Nat.card ↥(R ⊔ Q) ∣ Nat.card R * Nat.card Q := card_sup_dvd_card_mul hRQ
  have h2 : Nat.card P ∣ Nat.card ↥(R ⊔ Q) := Subgroup.card_dvd_of_le hPR
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hcop2 : ∀ a b : ℕ, Nat.Coprime (p ^ a) (2 ^ b) := fun a b =>
    Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hRp : p ^ 2 ∣ Nat.card R := by
    have h3 : p ^ 2 ∣ Nat.card R * 2 ^ k := hk ▸ (hP2.trans (h2.trans h1))
    exact (hcop2 2 k).dvd_of_dvd_mul_right h3
  let ψ : ↥Z →* ↥L ⧸ θL := (QuotientGroup.mk' θL).comp (Subgroup.inclusion hZL)
  let φ : ↥Z →* ↥X ⧸ θX := (QuotientGroup.mk' θX).comp (Subgroup.inclusion hZX)
  have hφs : Function.Surjective φ := by
    intro q
    have hq : q ∈ ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' θX) := hZcov ▸ Subgroup.mem_top q
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hker2 : IsPGroup 2 ψ.ker := by
    intro z
    have hz : (Subgroup.inclusion hZL (z : ↥Z)) ∈ θL := by
      have h := z.2
      rw [MonoidHom.mem_ker] at h
      exact (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨m, hm⟩ := hθL ⟨_, hz⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg (fun t : θL => ((t : ↥L) : G)) hm
    simpa using h
  have hker : ψ.ker ≤ φ.ker := by
    have hn : (ψ.ker.map φ).Normal := (MonoidHom.normal_ker ψ).map φ hφs
    rcases hXs.eq_bot_or_eq_top_of_normal (ψ.ker.map φ) with hb | ht
    · intro z hz
      have : φ z ∈ ψ.ker.map φ := ⟨z, hz, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have h2' : IsPGroup 2 (ψ.ker.map φ) := hker2.map φ
      obtain ⟨m, hm⟩ := h2'.exists_card_eq
      rw [ht, Subgroup.card_top, hX60] at hm
      have hm6 : m < 6 := by
        by_contra hc
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hc)
        omega
      interval_cases m <;> norm_num at hm
  let φb : ↥ψ.range →* ↥X ⧸ θX :=
    (QuotientGroup.lift ψ.ker φ hker).comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
  have hφb : ∀ z : ↥Z, φb (ψ.rangeRestrict z) = φ z := by
    intro z
    have he : (QuotientGroup.quotientKerEquivRange ψ).symm (ψ.rangeRestrict z) =
        (z : ↥Z ⧸ ψ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift ψ.ker φ hker
      ((QuotientGroup.quotientKerEquivRange ψ).symm (ψ.rangeRestrict z)) = φ z
    rw [he, QuotientGroup.lift_mk]
  have hφbs : Function.Surjective φb := by
    intro q
    obtain ⟨z, rfl⟩ := hφs q
    exact ⟨ψ.rangeRestrict z, hφb z⟩
  set Rb := (R.subgroupOf Z).map ψ.rangeRestrict with hRb
  have hRbk : Rb ≤ φb.ker := by
    rintro _ ⟨r, hr, rfl⟩
    rw [MonoidHom.mem_ker, hφb]
    change QuotientGroup.mk' θX (Subgroup.inclusion hZX r) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyr⟩ := hHθ (Subgroup.mem_subgroupOf.mp hr).2
    have : y = Subgroup.inclusion hZX r := Subtype.ext hyr
    exact this ▸ hy
  have hcardψ : Nat.card ψ.range = Nat.card φb.ker * 60 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φb.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φb hφbs).toEquiv, hX60, mul_comm]
  have hψdvd : Nat.card ψ.range ∣ 604800 := by
    have h := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [KFacts.KS14.card_eq_of_j2 hJ] at h
  have hRbdvd : 60 * Nat.card Rb ∣ 604800 := by
    refine (dvd_trans ?_ hψdvd)
    rw [hcardψ, mul_comm 60]
    exact mul_dvd_mul_right (Subgroup.card_dvd_of_le hRbk) 60
  have hRbp : p ^ 2 ∣ Nat.card Rb := by
    let ψR : ↥(R.subgroupOf Z) →* ↥ψ.range := ψ.rangeRestrict.comp (R.subgroupOf Z).subtype
    have hrange : ψR.range = Rb := by
      rw [MonoidHom.range_comp ψ.rangeRestrict (R.subgroupOf Z).subtype, Subgroup.range_subtype]
    have hker2' : IsPGroup 2 ψR.ker := by
      intro x
      have hx : ((x : ↥(R.subgroupOf Z)) : ↥Z) ∈ ψ.ker := by
        have h := x.2
        rw [MonoidHom.mem_ker] at h ⊢
        have h' := congrArg Subtype.val h
        simpa [ψR] using h'
      obtain ⟨m, hm⟩ := hker2 ⟨_, hx⟩
      refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
      have h := congrArg (fun t : ψ.ker => (t : ↥Z)) hm
      simpa using h
    obtain ⟨j, hj⟩ := hker2'.exists_card_eq
    have hcardR : Nat.card ↥(R.subgroupOf Z) = Nat.card ψR.ker * Nat.card Rb := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψR.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψR).toEquiv, hrange, mul_comm]
    have hRR : Nat.card ↥(R.subgroupOf Z) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRZ).toEquiv
    rw [hRR, hj] at hcardR
    rw [hcardR] at hRp
    exact (hcop2 2 j).dvd_of_dvd_mul_left hRp
  have hfin : p ^ 2 ∣ 10080 := by
    have h := (mul_dvd_mul_left 60 hRbp).trans hRbdvd
    have h' : 60 * p ^ 2 ∣ 60 * 10080 := by simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  exact not_sq_dvd_of_ne hp hp2 hp3 hfin

theorem false_of_trivial_frattini_action {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X P Z : Subgroup G} (hP : IsPGroup p P) (hPX : P ≤ X)
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (h2 : 2 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X)) (hZX : Z ≤ X)
    (hZcov : (Z.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X)
    (hHX : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G))
    (htriv : ∀ z ∈ Z, ∀ u ∈ P, ∃ v ∈ (frattini ↥P).map P.subtype,
      ∃ q ∈ CFSG.Open.pCoreOf 2 X, z * u * z⁻¹ = v * u * q) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  set H := P ⊔ Q with hHdef
  set θX := aschbacherSolvableCore 3 ↥X with hθX
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPX.trans hXQ
  have hHmul : (H : Set G) = (P : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ
  have hPH : P ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  set O := CFSG.pCore 2 ↥H with hO
  have hQn : (Q.subgroupOf H).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := (Subgroup.mem_normalizer_iff.mp (hXQ ((sup_le hPX hQX) g.2)) _).mp hx
    simpa using h⟩
  have hQO : Q.subgroupOf H ≤ O := le_sSup ⟨hQn, hQ2.comap_subtype⟩
  have hOQ : ∀ h ∈ O, (h : G) ∈ Q := by
    intro h hh
    obtain ⟨u, hu, q, hq, huq⟩ : (h : G) ∈ (P : Set G) * (Q : Set G) := hHmul ▸ h.2
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨h, hh⟩
    have hm' : h ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    obtain ⟨n, hn⟩ := hP ⟨u, hu⟩
    have hn' : u ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    set π := QuotientGroup.mk' (Q.subgroupOf H) with hπ
    have hπh : π h = π ⟨u, hPH hu⟩ := by
      have he : h = ⟨u, hPH hu⟩ * ⟨q, hQH hq⟩ := Subtype.ext huq.symm
      have hq1 : π ⟨q, hQH hq⟩ = 1 := (QuotientGroup.eq_one_iff (⟨q, hQH hq⟩ : ↥H)).mpr
        (Subgroup.mem_subgroupOf.mpr (show q ∈ Q from hq))
      rw [he, map_mul, hq1, mul_one]
    have h1 : π ⟨u, hPH hu⟩ ^ 2 ^ m = 1 := by rw [← hπh, ← map_pow, hm', map_one]
    have h2' : π ⟨u, hPH hu⟩ ^ p ^ n = 1 := by
      rw [← map_pow]
      have : (⟨u, hPH hu⟩ : ↥H) ^ p ^ n = 1 := Subtype.ext (by simpa using hn')
      rw [this, map_one]
    have hcop : Nat.Coprime (p ^ n) (2 ^ m) :=
      Nat.Coprime.pow n m ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hord : orderOf (π ⟨u, hPH hu⟩) = 1 :=
      Nat.dvd_one.mp (hcop.gcd_eq_one ▸
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2') (orderOf_dvd_of_pow_eq_one h1))
    rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hord
    rw [← huq]
    exact Q.mul_mem hord hq
  set Y := ↥H ⧸ O with hY
  let g : ↥P →* Y := (QuotientGroup.mk' O).comp (Subgroup.inclusion hPH)
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O y
    obtain ⟨u, hu, q, hq, huq⟩ : (h : G) ∈ (P : Set G) * (Q : Set G) := hHmul ▸ h.2
    refine ⟨⟨u, hu⟩, ?_⟩
    have he : h = Subgroup.inclusion hPH ⟨u, hu⟩ * ⟨q, hQH hq⟩ := Subtype.ext huq.symm
    change QuotientGroup.mk' O (Subgroup.inclusion hPH ⟨u, hu⟩) = QuotientGroup.mk' O h
    have hq1 : QuotientGroup.mk' O ⟨q, hQH hq⟩ = 1 :=
      (QuotientGroup.eq_one_iff (⟨q, hQH hq⟩ : ↥H)).mpr
        (hQO (Subgroup.mem_subgroupOf.mpr (show q ∈ Q from hq)))
    rw [he, map_mul, hq1, mul_one]
  have hYp : IsPGroup p Y := hP.of_surjective g hgs
  have hΦ : frattini ↥P ≤ (frattini Y).comap g := frattini_le_comap_frattini_of_surjective hgs
  set NH := Subgroup.normalizer (H : Set G) with hNH
  let ζ : ↥NH →* MulAut Y := (autQuotient O).comp H.normalizerMonoidHom
  have hζ : ∀ (n : ↥NH) (x : ↥H), ζ n (x : Y) =
      ((⟨n * x * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩ : ↥H) : Y) :=
    fun _ _ => rfl
  have hZker : ∀ (z : G) (hz : z ∈ Z), ζ ⟨z, hHX (hZX hz)⟩ ∈ (autQuotient (frattini Y)).ker := by
    intro z hz
    rw [mem_ker_autQuotient]
    intro y
    obtain ⟨u, rfl⟩ := hgs y
    obtain ⟨v, hv, q, hq, he⟩ := htriv z hz u u.2
    obtain ⟨v', hv', rfl⟩ := hv
    have hgv : g v' ∈ frattini Y := hΦ hv'
    have hval : ζ ⟨z, hHX (hZX hz)⟩ (g u) = g v' * g u := by
      change ζ ⟨z, hHX (hZX hz)⟩ ((Subgroup.inclusion hPH u : ↥H) : Y) = _
      rw [hζ]
      have hx : (⟨z * (u : G) * z⁻¹, (Subgroup.mem_normalizer_iff.mp (hHX (hZX hz)) _).mp
          (hPH u.2)⟩ : ↥H) = Subgroup.inclusion hPH v' * Subgroup.inclusion hPH u *
            ⟨q, hQH hq⟩ := Subtype.ext he
      change QuotientGroup.mk' O (⟨z * (u : G) * z⁻¹, _⟩ : ↥H) =
        QuotientGroup.mk' O (Subgroup.inclusion hPH v') *
          QuotientGroup.mk' O (Subgroup.inclusion hPH u)
      have hq1 : QuotientGroup.mk' O ⟨q, hQH hq⟩ = 1 :=
        (QuotientGroup.eq_one_iff (⟨q, hQH hq⟩ : ↥H)).mpr
          (hQO (Subgroup.mem_subgroupOf.mpr (show q ∈ Q from hq)))
      rw [hx, map_mul, map_mul, hq1, mul_one]
    rw [hval, ← mul_assoc]
    have hn : (frattini Y).Normal := inferInstance
    have h := hn.conj_mem _ hgv (g u)⁻¹
    rw [inv_inv] at h
    simpa [mul_assoc] using h
  have hXp : IsPGroup p (↥X ⧸ θX) := by
    intro x
    obtain ⟨z, hz, rfl⟩ : x ∈ (Z.subgroupOf X).map (QuotientGroup.mk' θX) :=
      hZcov ▸ Subgroup.mem_top x
    have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨k, hk⟩ := isPGroup_ker_autQuotient_frattini hYp
      ⟨_, hZker (z : G) hzZ⟩
    have hk' : ζ (⟨(z : G), hHX (hZX hzZ)⟩ ^ p ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have hcomm : ∀ u ∈ P, ⁅(z : G) ^ p ^ k, u⁆ ∈ Q := by
      intro u hu
      have h1 := congrArg (fun α : MulAut Y => α ((Subgroup.inclusion hPH ⟨u, hu⟩ : ↥H) : Y)) hk'
      simp only [MulAut.one_apply] at h1
      rw [hζ] at h1
      rw [QuotientGroup.eq] at h1
      have h3 := hOQ _ h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
        Subgroup.coe_pow] at h3
      have h4 := Q.inv_mem ((Subgroup.mem_normalizer_iff.mp (hXQ (hPX hu)) _).mp h3)
      rw [commutatorElement_def]
      convert h4 using 1
      group
    have hzθ : ((z : G) ^ p ^ k) ∈ oTwoOddIn X :=
      mem_oTwoOddIn_of_commutator_mem hp2 hPX hP hC (pow_mem z.2 _) hcomm
    have hO2 := Proof152F.oTwoOddIn_le_theta hXs h2 hzθ
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyz⟩ := hO2
    have : y = z ^ p ^ k := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyz)
    exact this ▸ hy
  obtain ⟨m, hm⟩ := hXp.exists_card_eq
  rw [hm] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem not_le_centralizer_of
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y M X : Subgroup G} (hctx : Ctx152 A (lB A) Y M X)
    {c' : G} {L' : Subgroup G} (hb : Subgroup.zpowers c' ∈ omegaA A) (hLb : L' ∈ lA A c')
    (hJ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A)
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {c', d} : Set G))
    {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    ¬ P ≤ Subgroup.centralizer ({c'} : Set G) := by
  intro hPc
  have : Fact p.Prime := ⟨hP.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hP.prime
  have h' : Sec14Std G A c' L' :=
    { h with zpowers_mem_omegaA := hb, mem_lA := hLb }
  set θX := aschbacherSolvableCore 3 ↥X with hθX
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp
  have h2 : 2 ∣ Nat.card (↥X ⧸ θX) := by rw [hX60]; norm_num
  have hcA : c' ∈ A := (zpowers_mem_omegaA_iff.mp hb).1
  have hc3 : c' ^ 3 = 1 := h.isE27.1.2 c' hcA
  have hcC : c' ∈ Sec4.thetaQuotCentralizer X := by
    refine Proof152F.mem_thetaQuotCentralizer_of_mem hctx.norm_x ?_
    have hc : c' ∈ (Subgroup.closure {c', d} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    rw [← hcent] at hc
    exact hc
  have hPp : IsPGroup p P := by
    rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  have hP2 : p ^ 2 ∣ Nat.card P := by
    rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · rw [h]
    · rw [h]
      exact pow_dvd_pow p (by norm_num)
  have hV := Proof152F.card_frattini_quot_eq hP.type_p
  have hPX := hP.le_px
  have hCL := centralizer_le_normalizer_of_j2 h' hJ
  have hPL : P ≤ Subgroup.normalizer (L' : Set G) := hPc.trans hCL
  have hZcov := map_inf_eq_top_of_cent h142 h' hctx hdA hJ hcent
  have hθL := isPGroup_theta_of_item135 h135 hmult h' hJ
  set Q := CFSG.Open.pCoreOf 2 X with hQdef
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hHX := le_normalizer_sup_pCoreOf hP.char_p
  have hHmul : ((P ⊔ Q : Subgroup G) : Set G) = (P : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P Q (hPX.trans hXQ)
  have hQθ : Q ≤ θX.map X.subtype := by
    rw [hQdef, CFSG.Open.pCoreOf]
    exact Subgroup.map_mono (Proof152F.pCore_two_le_theta ↥X)
  have hHθ : P ⊔ Q ≤ θX.map X.subtype :=
    sup_le ((le_oTwoP_of_pData hP.char_p).trans
      (Subgroup.map_mono (Proof152F.oTwoP_le_theta hp3 _))) hQθ
  have hO2θ := Proof152F.oTwoOddIn_le_theta hXs h2
  have hC : ∀ (x : G) (hx : x ∈ X), x ∈ Subgroup.centralizer (P : Set G) →
      (⟨x, hx⟩ : ↥X) ∈ θX := by
    intro x hx hxc
    obtain ⟨y, hy, hyx⟩ := hO2θ (hP.cent_p ⟨hx, hxc⟩)
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  set W := X ⊓ Subgroup.normalizer (P : Set G) with hW
  have hWcov := Proof152F.map_inf_normalizer_eq_top hp3 hP.char_p
  have hcW : c' ∈ Subgroup.normalizer (W : Set G) := by
    have hcX : Subgroup.zpowers c' ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr (hctx.norm_x hcA)
    have hcP : Subgroup.zpowers c' ≤
        Subgroup.normalizer ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_normalizer P (hP.norm_p hcA))
    exact Late.le_normalizer_inf hcX hcP (Subgroup.mem_zpowers c')
  have hNcov := Proof152Gen.map_inf_centralizer_eq_top (inf_le_left : W ≤ X) hcW hc3 hcC hWcov
  set Nc := W ⊓ Subgroup.centralizer ({c'} : Set G) with hNc
  set R := L' ⊓ (P ⊔ Q) with hR
  set U := P ⊓ (R ⊔ Q) with hU
  have hNcX : Nc ≤ X := inf_le_left.trans inf_le_left
  have hNcP : Nc ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans inf_le_right
  have hNcU : Nc ≤ Subgroup.normalizer (U : Set G) :=
    Late.le_normalizer_inf hNcP (le_normalizer_sup (A := Nc)
      (Late.le_normalizer_inf (inf_le_right.trans hCL) (hNcX.trans hHX)) (hNcX.trans hXQ))
  set ℓ := (U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P)) with hℓ
  have hℓdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_subgroup_dvd_card ℓ
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hℓdvd
  interval_cases k
  ·
    have hbot : ℓ = ⊥ := Subgroup.eq_bot_of_card_eq ℓ (by rw [hk, pow_zero])
    rw [hℓ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    refine false_of_trivial_frattini_action hP.odd hPp hPX hXs h2 (inf_le_left : X ⊓ L' ≤ X)
      hZcov hP.cent_p hHX ?_
    intro z hz u hu
    have hzu : ⁅z, u⁆ ∈ R := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine L'.mul_mem hz.2 ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp (hPL hu) _).mp (L'.inv_mem hz.2)
        simpa [mul_assoc] using h1
      · have huH : u ∈ P ⊔ Q := Subgroup.mem_sup_left hu
        rw [commutatorElement_def]
        exact (P ⊔ Q).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHX hz.1) u).mp huH)
          ((P ⊔ Q).inv_mem huH)
    obtain ⟨v, hv, q, hq, hvq⟩ : ⁅z, u⁆ ∈ (P : Set G) * (Q : Set G) := hHmul ▸ hzu.2
    have hvq' : v * q = ⁅z, u⁆ := hvq
    have hvU : v ∈ U := by
      refine ⟨hv, ?_⟩
      have he : v = ⁅z, u⁆ * q⁻¹ := by rw [← hvq']; group
      rw [he]
      exact (R ⊔ Q).mul_mem (Subgroup.mem_sup_left hzu) (Subgroup.mem_sup_right (Q.inv_mem hq))
    have hvΦ : v ∈ (frattini ↥P).map P.subtype :=
      ⟨⟨v, hv⟩, hbot (Subgroup.mem_subgroupOf.mpr hvU), rfl⟩
    have hqu : u⁻¹ * q * u ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXQ (hPX (P.inv_mem hu))) q).mp hq
      simpa using h1
    refine ⟨v, hvΦ, u⁻¹ * q * u, hqu, ?_⟩
    calc z * u * z⁻¹ = ⁅z, u⁆ * u := by rw [commutatorElement_def]; group
      _ = v * q * u := by rw [← hvq']
      _ = v * u * (u⁻¹ * q * u) := by group
  ·
    exact Proof152Flag.false_of_invariant_line hP.odd hPp hV θX hXq.1 h2 hNcX hNcP hNcov hC hNcU
      (by rw [hk, pow_one])
  ·
    have htop : ℓ = ⊤ := Subgroup.eq_top_of_card_eq ℓ (by rw [hk, hV])
    have hsup : U.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini ↥P)) (U.subgroupOf P)
      rw [← hℓ, htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hUtop : U.subgroupOf P = ⊤ := frattini_nongenerating hsup
    have hPU : P ≤ R ⊔ Q := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥P) ∈ U.subgroupOf P := hUtop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h1).2
    exact false_of_le_sup hP.odd hp3 hθL hJ hXs hX60 hZcov hPX hHθ hP2 hPU

theorem not_le_centralizer
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {Y M X : Subgroup G} {c' : G} {L' : Subgroup G}
    {d : G} {p : ℕ} {P : Subgroup G} (hpt : Pt152 A (lB A) Y M X c' L')
    (hd : DData152 A X c' L' d) (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    ¬ P ≤ Subgroup.centralizer ({c'} : Set G) :=
  not_le_centralizer_of h142 h135 hmult h hpt.ctx hpt.omega hpt.mem_lA hpt.hj hd.mem_d hd.cent hP
    hp3

end Proof152FX

variable {G : Type} [Group G] [Finite G]

theorem step152ConfFC_of_item142
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) : Step152ConfFC A (lB A) :=
  fun _ _ _ _ _ _ _ _ _ _ _ hpt hd hP _ _ hθ _ _ _ =>
    Proof152FX.not_le_centralizer h142 h135 hmult h hpt hd hP (ne_three_of_le_theta hP hθ)

theorem step152ConfFCR_of_item142
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) : Step152ConfFCR :=
  fun _ _ _ _ _ _ hR => step152ConfFC_of_item142 h142 h135 hmult hR.toSec14Std

theorem step152ConfFR_of_item142
    (h142 : Item142AllS14) (h135 : Item135) (hmult : KFacts.KS18Mult) : Step152ConfFR :=
  step152ConfFR_of (step152ConfFCR_of_item142 h142 h135 hmult)

end CFSG.RankThree.PartTwo.Sec15
