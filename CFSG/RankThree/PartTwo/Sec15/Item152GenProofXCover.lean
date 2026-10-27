module

public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofX
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof152Gen

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_sup_of_item142 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    {W : Subgroup G}
    (hW : W ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3)) :
    ⁅W, A⁆ ≤ L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set O := pPrimeCoreOf 3 H with hO
  set K := k142 A (lB A) c with hK
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := centralizer_singleton_le_normalizer_zpowers c
  have hAab : IsMulCommutative A := hD.isElemAbelian.1
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    (hAC.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  obtain ⟨Q, hQ, hWQ⟩ := exists_le_mem_maxInvariantPiSubgroups hW
  obtain ⟨hQmem, halt⟩ := h142 Q hQ
  have hQK : Q ≤ K := le_delta hQmem.1 (hQmem.2.trans hCH)
  refine (Subgroup.commutator_mono (hWQ.trans hQK) le_rfl).trans ?_
  rcases halt with ⟨-, -, hOK, hcard⟩ | ⟨hKeq, -⟩
  ·
    rw [← hH] at hOK hcard
    have hidx : (O.subgroupOf K).index = 2 := by
      have h1 := Subgroup.card_mul_index (O.subgroupOf K)
      have h2 : Nat.card ↥(O.subgroupOf K) = Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
      rw [h2, hcard] at h1
      have hpos : 0 < Nat.card O := Nat.card_pos
      have h3 : Nat.card O * (O.subgroupOf K).index = Nat.card O * 2 := by rw [h1, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hpos h3
    refine le_sup_of_le_right (Subgroup.commutator_le.mpr fun k hk a ha => ?_)
    have hk' : a * k⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK ha) _).mp (inv_mem hk)
    have hiff : (⟨a * k⁻¹ * a⁻¹, hk'⟩ : ↥K) ∈ O.subgroupOf K ↔ (⟨k, hk⟩ : ↥K) ∈ O.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      change a * k⁻¹ * a⁻¹ ∈ O ↔ k ∈ O
      rw [← (Subgroup.mem_normalizer_iff.mp (hAO ha) _), inv_mem_iff]
    have hmem : (⟨k, hk⟩ : ↥K) * ⟨a * k⁻¹ * a⁻¹, hk'⟩ ∈ O.subgroupOf K :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr hiff.symm
    rw [Subgroup.mem_subgroupOf] at hmem
    have he : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [he]
    exact hmem
  ·
    have hKeq' : K = L ⊔ O ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := hKeq
    rw [hKeq']
    set XA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hXA
    have hXAC : XA ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
    have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A)
    have hXAN : XA ≤ Subgroup.normalizer ((L ⊔ O : Subgroup G) : Set G) :=
      le_normalizer_sup ((hXAC.trans hCAc).trans (centralizer_le_normalizer_of_j2 h hJ))
        (((hXAC.trans hCAc).trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H))
    have hALO : A ≤ Subgroup.normalizer ((L ⊔ O : Subgroup G) : Set G) :=
      le_normalizer_sup hD.le_normalizer hAO
    rw [Subgroup.commutator_le]
    intro k hk a ha
    have hk' : k ∈ ((L ⊔ O ⊔ XA : Subgroup G) : Set G) := hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hXAN] at hk'
    obtain ⟨m, hm, x, hx, rfl⟩ := Set.mem_mul.mp hk'
    have hxa : x * a = a * x := (Subgroup.mem_centralizer_iff.mp (hXAC hx) a ha).symm
    have he : ⁅m * x, a⁆ = m * (a * m⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      calc m * x * a * (m * x)⁻¹ * a⁻¹ = m * (x * a) * x⁻¹ * m⁻¹ * a⁻¹ := by group
        _ = m * (a * x) * x⁻¹ * m⁻¹ * a⁻¹ := by rw [hxa]
        _ = m * (a * m⁻¹ * a⁻¹) := by group
    rw [he]
    exact mul_mem hm ((Subgroup.mem_normalizer_iff.mp (hALO ha) _).mp (inv_mem hm))

omit [Finite G] in
theorem map_subgroupOf_normal_of_le_normalizer {X V R : Subgroup G}
    (hRV : R ≤ Subgroup.normalizer (V : Set G))
    (hR : (R.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    ((V.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X))).Normal := by
  constructor
  rintro _ ⟨v, hv, rfl⟩ g
  have hg : g ∈ (R.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
    hR ▸ Subgroup.mem_top g
  obtain ⟨r, hr, rfl⟩ := hg
  refine ⟨r * v * r⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_inv]⟩
  have h := (Subgroup.mem_normalizer_iff.mp (hRV (Subgroup.mem_subgroupOf.mp hr)) v).mp
    (Subgroup.mem_subgroupOf.mp hv)
  simpa using h

end Proof152Gen

open Proof152Gen

theorem step152GenXCover_of
    (h142 : Item142AllS14) : Step152GenXCover := by
  intro G _ _ A c L h Y M X hctx d p P T K S hD
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
    centralizer_le_normalizer_of_j2 h hD.hj
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
  have hsc : Late.sectionCentralizer A X θX = (Subgroup.closure {c, d} : Set G) := hD.cent
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
            (commutator_le_sup_of_item142 h hD.hj (h142 G A c L h) hWinv)
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
    have hdA := hD.mem_d
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
  have hMtop : ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) =
      ⊤ := hMn.eq_bot_or_eq_top.resolve_left hMne
  intro x hx
  have hq : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩ ∈
      ((X ⊓ L).subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
    hMtop ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have he : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [he]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) ⟨_, hyx, rfl⟩

end CFSG.RankThree.PartTwo.Sec15
