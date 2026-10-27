module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Ctx
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofFX
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68Tools
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofEnd
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Ronan152SL25

open Proof152Gen Proof152FX Proof152F CFSG.SectionRank.Ccomm

variable {G : Type} [Group G] [Finite G]

theorem map_inf_eq_top_of_centJ
    (h142 : Item142AllS14) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {M X : Subgroup G} (hctx : Ctx152J A (lB A) M X) {d : G} (hdA : d ∈ A)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (Subgroup.closure {c, d} : Set G)) :
    ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
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

theorem inf_centralizer_le_frattini_or_le_ofJ
    {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {M X : Subgroup G} {c' : G} {p : ℕ} {P : Subgroup G} (hctx : Ctx152J A LB M X)
    (hcA : c' ∈ A) (hc3 : c' ^ 3 = 1) (hcC : c' ∈ Sec4.thetaQuotCentralizer X)
    (hP : PData152 A X p P) (hp3 : p ≠ 3) :
    P ⊓ Subgroup.centralizer ({c'} : Set G) ≤ (frattini ↥P).map P.subtype ∨
      P ≤ Subgroup.centralizer ({c'} : Set G) := by
  have : Fact p.Prime := ⟨hP.prime⟩
  have hp : p.Prime := hP.prime
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
  have hXq := isQuasisimple_theta_of_mem_thetaComponentsIn hctx.mem_comp
  have h2 : 2 ∣ Nat.card (↥X ⧸ θ) := by rw [hX60]; norm_num
  have hPp : IsPGroup p P := by
    rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card h
    · exact IsPGroup.of_card h
  have hV := card_frattini_quot_eq hP.type_p
  set W := X ⊓ Subgroup.normalizer (P : Set G) with hW
  have hWcov := map_inf_normalizer_eq_top hp3 hP.char_p
  have hcW : c' ∈ Subgroup.normalizer (W : Set G) := by
    have hcX : Subgroup.zpowers c' ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr (hctx.norm_x hcA)
    have hcP : Subgroup.zpowers c' ≤
        Subgroup.normalizer ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_normalizer P (hP.norm_p hcA))
    exact Late.le_normalizer_inf hcX hcP (Subgroup.mem_zpowers c')
  have hNcov := Proof152Gen.map_inf_centralizer_eq_top (inf_le_left : W ≤ X) hcW hc3 hcC hWcov
  set Nc := W ⊓ Subgroup.centralizer ({c'} : Set G) with hNc
  have hNcU : Nc ≤ Subgroup.normalizer ((P ⊓ Subgroup.centralizer ({c'} : Set G) :
      Subgroup G) : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans (Subgroup.le_normalizer))
  have hC : ∀ (x : G) (hx : x ∈ X), x ∈ Subgroup.centralizer (P : Set G) →
      (⟨x, hx⟩ : ↥X) ∈ θ := by
    intro x hx hxc
    obtain ⟨y, hy, hyx⟩ := oTwoOddIn_le_theta hXs h2 (hP.cent_p ⟨hx, hxc⟩)
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    exact this ▸ hy
  set U := P ⊓ Subgroup.centralizer ({c'} : Set G) with hU
  set ℓ := (U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P)) with hℓ
  have hℓdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_subgroup_dvd_card ℓ
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hℓdvd
  interval_cases k
  ·
    left
    have hbot : ℓ = ⊥ := Subgroup.eq_bot_of_card_eq ℓ (by rw [hk, pow_zero])
    rw [hℓ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    intro x hx
    exact ⟨⟨x, hx.1⟩, hbot (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  ·
    exfalso
    exact Proof152Flag.false_of_invariant_line hP.odd hPp hV θ hXq.1 h2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) hNcov hC hNcU
      (by rw [hk, pow_one])
  ·
    right
    have htop : ℓ = ⊤ := Subgroup.eq_top_of_card_eq ℓ (by rw [hk, hV])
    have hsup : U.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini ↥P)) (U.subgroupOf P)
      rw [← hℓ, htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hUtop : U.subgroupOf P = ⊤ := frattini_nongenerating hsup
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥P) ∈ U.subgroupOf P := hUtop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp h1).2

theorem not_le_centralizer_ofJ
    (h142 : Item142AllS14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {M X : Subgroup G} (hctx : Ctx152J A (lB A) M X)
    {c' : G} {L' : Subgroup G} (hb : Subgroup.zpowers c' ∈ omegaA A) (hLb : L' ∈ lA A c')
    (hJ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hθL : IsPGroup 2 (aschbacherSolvableCore 3 ↥L'))
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
  obtain ⟨hXs, hX60⟩ := isSimpleGroup_theta_quotJ hctx
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
  have hZcov := map_inf_eq_top_of_centJ h142 h' hctx hdA hJ hcent
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

end Ronan152SL25

end CFSG.RankThree.PartTwo.Sec15
