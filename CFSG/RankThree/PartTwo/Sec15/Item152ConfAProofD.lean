module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTools
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXCover
import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
import CFSG.RankThree.PartTwo.Sec14.Concl142HJTools
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item68Tools
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof152ConfA

variable {G : Type} [Group G] [Finite G]

theorem le_inf_sup_theta_of_item142
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h142 : Item142 A (lB A) c L h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A)
    {Y M X : Subgroup G} (hctx : Ctx152 A (lB A) Y M X)
    (hcC : c ∈ Sec4.thetaQuotCentralizer X)
    (hnc : ∃ a ∈ A, a ∉ Sec4.thetaQuotCentralizer X) :
    X ≤ (X ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  obtain ⟨hXs, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
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
  set N := X ⊓ (L ⊔ O) with hN
  have hLON : L ⊔ O ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hOL
  have hcovc : ((X ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ := by
    refine Proof152Gen.map_inf_centralizer_eq_top le_rfl (hAX hcA) hc3 hcC ?_
    rw [Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hCN : X ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    Late.le_normalizer_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans (le_normalizer_sup hCL (hCH.trans hHO)))
  have hNn := Proof152Gen.map_subgroupOf_normal_of_le_normalizer hCN hcovc
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
            (Proof152Gen.commutator_le_sup_of_item142 h hJ h142 hWinv)
          have h3 : ⁅w, b⁆ = w * (b * w⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
          rw [h3]
          exact mul_mem (hWX hw)
            ((Subgroup.mem_normalizer_iff.mp (hAX hb) _).mp (inv_mem (hWX hw)))
        have himg := Proof152Gen.map_inf_centralizer_eq hQX (hAQ hcA) hc3 hcC
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
    obtain ⟨a, ha, hna⟩ := hnc
    refine hna (Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hAX ha, fun l hl => ?_⟩)
    have h1 := hAcent a ha l hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (hXθ (inv_mem hl)) _).mp h1
    rwa [show l⁻¹ * (a * l * a⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (a * l * a⁻¹) by group] at h2
  have hNtop : (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤ :=
    hNn.eq_bot_or_eq_top.resolve_left hNne
  have hMn := Proof152Gen.map_subgroupOf_normal_of_le_normalizer (V := X ⊓ L)
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

theorem isThreeCentralIn_of_cover
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {LB : Subgroup G → Subgroup G} {Y M X : Subgroup G} (hctx : Ctx152 A LB Y M X)
    (hcov : X ≤ (X ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    {d : G} (hdA : d ∈ A) (hdL : d ∈ L) (hdC : d ∈ Sec4.thetaQuotCentralizer X) :
    IsThreeCentralIn L d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hS13 := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  obtain ⟨-, hX60⟩ := Proof152Gen.isSimpleGroup_theta_quot_of_ctx152 hctx
  have hWtop := Proof152Gen.map_subgroupOf_eq_top_of_le_sup (inf_le_left : X ⊓ L ≤ X) hcov
  have hdW : d ∈ Subgroup.normalizer ((X ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hctx.norm_x hS13.le_normalizer hdA
  have hW' := Proof152Gen.map_inf_centralizer_eq_top inf_le_left hdW hd3 hdC hWtop
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥X ⧸ aschbacherSolvableCore 3 ↥X) 5 (by rw [hX60]; norm_num)
  have hqmem : q ∈ (((X ⊓ L) ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf X).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) := hW' ▸ Subgroup.mem_top q
  obtain ⟨w, hwW, hwq⟩ := hqmem
  have hwW' : (w : G) ∈ (X ⊓ L) ⊓ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_subgroupOf.mp hwW
  have hwL : (w : G) ∈ L := hwW'.1.2
  have h5w : 5 ∣ orderOf w := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) w
    rwa [hwq, hq] at h1
  set θL := aschbacherSolvableCore 3 ↥L with hθL
  set ρ := QuotientGroup.mk' θL with hρ
  set z : ↥L ⧸ θL := ρ ⟨d, hdL⟩ with hz
  set v : ↥L ⧸ θL := ρ ⟨w, hwL⟩ with hv
  have hθL2 : IsPGroup 2 θL := Proof152Gen.isPGroup_theta_of_j2 h hJ
  have h5v : 5 ∣ orderOf v := by
    have hvn : v ^ orderOf v = 1 := pow_orderOf_eq_one v
    have hwn : (⟨w, hwL⟩ : ↥L) ^ orderOf v ∈ θL := by
      rw [← QuotientGroup.eq_one_iff]
      change ρ ((⟨w, hwL⟩ : ↥L) ^ orderOf v) = 1
      rw [map_pow]
      exact hvn
    obtain ⟨k, hk⟩ := hθL2 ⟨_, hwn⟩
    have hk' : (w : G) ^ (orderOf v * 2 ^ k) = 1 := by
      have := congrArg (fun t : θL => ((t : ↥L) : G)) hk
      simpa [pow_mul] using this
    have h1 : orderOf w ∣ orderOf v * 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk'
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp (h5w.trans h1) with h2 | h2
    · exact h2
    · exfalso
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h2)
      omega
  have hvz : v ∈ Subgroup.centralizer ({z} : Set (↥L ⧸ θL)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hv, hz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hwW'.2)
  have h5C : 5 ∣ Nat.card (Subgroup.centralizer ({z} : Set (↥L ⧸ θL))) :=
    h5v.trans (Subgroup.orderOf_dvd_natCard _ hvz)
  have hAL3 : IsPGroup 3 (A.subgroupOf L) := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨S1, hS1⟩ := hAL3.exists_le_sylow
  set P := S1.mapSurjective (QuotientGroup.mk'_surjective θL) with hP
  have hB9 : Nat.card ((A.subgroupOf L).map ρ) = 9 := by
    rw [hρ, card_map_mk_subgroupOf hS13.isElemAbelian]
    exact (j2_point_facts hS13 hJ).2.1
  have hBP : (A.subgroupOf L).map ρ ≤ (P : Subgroup (↥L ⧸ θL)) := by
    rw [hP, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hS1
  have hzB : z ∈ (A.subgroupOf L).map ρ := ⟨⟨d, hdL⟩, Subgroup.mem_subgroupOf.mpr hdA, rfl⟩
  have hdS1 : (⟨d, hdL⟩ : ↥L) ∈ (S1 : Subgroup ↥L) := hS1 (Subgroup.mem_subgroupOf.mpr hdA)
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, -, -, h4, -⟩ := h415 (↥L ⧸ θL) hJ P _ rfl _ rfl
  have hzZ : z ∈ (P : Subgroup (↥L ⧸ θL)) ⊓
      Subgroup.centralizer ((P : Subgroup (↥L ⧸ θL)) : Set (↥L ⧸ θL)) := by
    by_contra hzZ
    obtain ⟨-, ⟨eN⟩, -⟩ := h4 ((A.subgroupOf L).map ρ) ⟨hBP, hB9⟩ z hzB hzZ
    have h72 : Nat.card (Subgroup.normalizer (Subgroup.zpowers z : Set (↥L ⧸ θL))) = 72 := by
      rw [Nat.card_congr eN.toEquiv, Nat.card_prod, natCard_perm_fin_three,
        natCard_alternatingGroup_fin_four]
    have h1 := h5C.trans (Subgroup.card_dvd_of_le (centralizer_singleton_le_normalizer_zpowers z))
    rw [h72] at h1
    norm_num at h1
  exact ⟨hdL, S1, hdS1, le_centralizer_of_mk_mem_center S1 hdS1 hzZ.2⟩

theorem step152ConfD_of
    (h142 : Item142R) {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L) :
    Step152ConfD A (lB A) := by
  intro Y M X c' L' hpt
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR' : Sec15R G A c' L' := { hR with zpowers_mem_omegaA := hpt.omega, mem_lA := hpt.mem_lA }
  have hS := hR'.toSec14Std
  have hS13 := hS.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS13.mem_partTwoE
  have hAF := hS13.mem_partTwoF
  have hctx := hpt.ctx
  have hc'A := hS13.mem_A
  have hc'3 := hS13.orderOf_eq
  have hcC := mem_thetaQuotCentralizer_of_dec hctx hAF hA hc'A hc'3 hpt.dec
  have h9 := card_inf_thetaQuotCentralizer hctx hAF hA
  obtain ⟨hc'L, hAL9, -⟩ := j2_point_facts hS13 hpt.hj
  set C := A ⊓ Sec4.thetaQuotCentralizer X with hC
  have hcomm : ∀ x ∈ C, ∀ y ∈ A ⊓ L', x * y = y * x := fun x hx y hy =>
    hS13.commute hx.1 hy.1
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C (A ⊓ L') hcomm
  have hsup : Nat.card (C ⊔ (A ⊓ L') : Subgroup G) ≤ 27 := by
    rw [← hA.2]
    exact Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left)
  rw [h9, hAL9] at h1
  have hinf : 1 < Nat.card (C ⊓ (A ⊓ L') : Subgroup G) := by
    by_contra hle
    push Not at hle
    have : Nat.card (C ⊔ (A ⊓ L') : Subgroup G) * Nat.card (C ⊓ (A ⊓ L') : Subgroup G) ≤
        27 * 1 := Nat.mul_le_mul hsup hle
    omega
  have : Nontrivial (C ⊓ (A ⊓ L') : Subgroup G) := Finite.one_lt_card_iff_nontrivial.mp hinf
  obtain ⟨⟨d, hd⟩, hd1⟩ := exists_ne (1 : (C ⊓ (A ⊓ L') : Subgroup G))
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdA : d ∈ A := hd.1.1
  have hdC : d ∈ Sec4.thetaQuotCentralizer X := hd.1.2
  have hdL : d ∈ L' := hd.2.2
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1'
  have hcov := le_inf_sup_theta_of_item142 hS hpt.hj (h142 G A c' L' hR') hctx hcC
    (exists_not_mem_thetaQuotCentralizer hctx hAF hA)
  refine ⟨d, ⟨hdA, hd1', isThreeCentralIn_of_cover hS hpt.hj hctx hcov hdA hdL hdC, ?_⟩⟩
  rw [sectionCentralizer_eq_inf hctx.norm_x]
  congr 1
  have hcd : Subgroup.closure ({c', d} : Set G) = Subgroup.zpowers c' ⊔ Subgroup.zpowers d := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  rw [hcd]
  have hle : Subgroup.zpowers c' ⊔ Subgroup.zpowers d ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hc'A, hcC⟩) (Subgroup.zpowers_le.mpr ⟨hdA, hdC⟩)
  have hdisj : Subgroup.zpowers d ⊓ Subgroup.zpowers c' = ⊥ := by
    refine Sec12.inf_zpowers_eq_bot_of_not_mem hc'3 fun hc'd => hc'L ?_
    exact (Subgroup.zpowers_le.mpr hdL) hc'd
  have hcommcd : ∀ x ∈ Subgroup.zpowers c', ∀ y ∈ Subgroup.zpowers d, x * y = y * x :=
    fun x hx y hy => hS13.commute (Subgroup.zpowers_le.mpr hc'A hx)
      (Subgroup.zpowers_le.mpr hdA hy)
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommcd
  rw [inf_comm, hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hc'3,
    hdo] at h2
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h9, h2]

end Proof152ConfA

theorem step152ConfDR_of
    (h142 : Item142R) : Step152ConfDR :=
  fun _ _ _ _ _ _ hR => Proof152ConfA.step152ConfD_of h142 hR

end CFSG.RankThree.PartTwo.Sec15
