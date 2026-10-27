module

public import CFSG.RankThree.PartTwo.J2Residue.ConfigFacts
import CFSG.ClassicalGroups.PCoreSection
import CFSG.RankThree.GroupTheory.SteinbergCDRankOneAutPrimes
import CFSG.Holt.H78.Sec4LemmaD
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.ClassicalInvolution.AschTight.CSM
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma pRank_two_le_one_of_unique_involution {U : Subgroup G} {z : G}
    (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (huniq : ∀ x ∈ U, x * x = 1 → x = 1 ∨ x = z) :
    CFSG.Open.pRank 2 U ≤ 1 := by
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E hEU hE
  have hEz : E ≤ Subgroup.zpowers z := by
    intro x hx
    have hx2 : x * x = 1 := by
      have := hE.2 x hx
      rwa [pow_two] at this
    rcases huniq x (hEU hx) hx2 with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  have hcardE : Nat.card ↥E ≤ Nat.card ↥(Subgroup.zpowers z) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hEz)
  have hz2' : z ^ 2 = 1 := by rwa [pow_two]
  have hzord : orderOf z = 2 := orderOf_eq_prime hz2' hz1
  rw [Nat.card_zpowers, hzord] at hcardE
  simpa using hcardE

private lemma commute_pCore_of_orderOf_five {LB : Subgroup G} (f : ↥LB) (hf : orderOf f = 5)
    (hrank : CFSG.Open.pRank 2 (⊤ : Subgroup ↥(CFSG.pCore 2 ↥LB)) ≤ 1) :
    ∀ x : ↥(CFSG.pCore 2 ↥LB), f * x = x * f := by
  let A : Subgroup ↥LB := Subgroup.zpowers f
  let φ : ↥A →* MulAut ↥(CFSG.pCore 2 ↥LB) :=
    (MulAut.conjNormal (H := CFSG.pCore 2 ↥LB)).comp A.subtype
  let act : MulDistribMulAction ↥A ↥(CFSG.pCore 2 ↥LB) :=
    MulDistribMulAction.compHom ↥(CFSG.pCore 2 ↥LB) φ
  have hsmul : ∀ (a : ↥A) (x : ↥(CFSG.pCore 2 ↥LB)),
      a • x = (MulAut.conjNormal (H := CFSG.pCore 2 ↥LB)) (a : ↥LB) x := fun a x => rfl
  have hA5 : IsPGroup 5 ↥A := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hf, pow_one]
  have hU'2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥LB) := (CFSG.pCore_isPGroup (p := 2) (G := ↥LB))
  have hact : ∀ (a : ↥A) (x : ↥(CFSG.pCore 2 ↥LB)), a • x = x := by
    intro a x
    by_contra hne
    have h2 := CFSG.RankThree.GroupTheory.two_le_pRank_of_nontrivial_action
      Nat.prime_five (by norm_num) (A := ↥A) (R := ↥(CFSG.pCore 2 ↥LB)) hA5 hU'2 ⟨a, x, hne⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    omega
  intro x
  have h := hact ⟨f, Subgroup.mem_zpowers f⟩ x
  have h' := congrArg (fun y : ↥(CFSG.pCore 2 ↥LB) => (y : ↥LB)) h
  simp only [hsmul, MulAut.conjNormal_apply, Subgroup.coe_subtype] at h'
  calc f * x = (f * x * f⁻¹) * f := by group
    _ = x * f := by rw [h']

private lemma five_dvd_card_lB {LB : Subgroup G}
    (hZcard : Nat.card ↥(Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)) = 3)
    (eA : (↥LB ⧸ CFSG.pCore 2 ↥LB) ⧸ Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) ≃*
      alternatingGroup (Fin 6)) :
    5 ∣ Nat.card ↥LB := by
  classical
  have hcardX : Nat.card (↥LB ⧸ CFSG.pCore 2 ↥LB) = 1080 := by
    have h1 : Nat.card ↥(Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)) *
        (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)).index =
        Nat.card (↥LB ⧸ CFSG.pCore 2 ↥LB) := Subgroup.card_mul_index _
    rw [Subgroup.index_eq_card] at h1
    have h2 : Nat.card ((↥LB ⧸ CFSG.pCore 2 ↥LB) ⧸
        Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)) = 360 := by
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
      simp only [Nat.card_fin]
      norm_num
    rw [h2, hZcard] at h1
    omega
  have h1 : Nat.card ↥(CFSG.pCore 2 ↥LB) * (CFSG.pCore 2 ↥LB).index = Nat.card ↥LB :=
    Subgroup.card_mul_index _
  rw [Subgroup.index_eq_card, hcardX] at h1
  rw [← h1]
  exact dvd_mul_of_dvd_right (by norm_num : 5 ∣ 1080) _

private lemma card_pCore_le_two {LB : Subgroup G} {d : G} (hdLB : d ∈ LB) (hd3 : orderOf d = 3)
    (hdc : ∀ y : ↥LB, (⟨d, hdLB⟩ : ↥LB) * y = y * ⟨d, hdLB⟩)
    (hperf : Group.IsPerfect LB)
    (htrip : CFSG.RankThree.PartTwo.Sec4.IsTripleCover
      (↥LB ⧸ CFSG.pCore 2 ↥LB) (alternatingGroup (Fin 6)))
    (hU'Z : CFSG.pCore 2 ↥LB ≤ Subgroup.center ↥LB) :
    Nat.card ↥(CFSG.pCore 2 ↥LB) ≤ 2 := by
  classical
  obtain ⟨hZcard, ⟨eA⟩⟩ := htrip
  have hd'ord : orderOf (⟨d, hdLB⟩ : ↥LB) = 3 := by
    rw [← Subgroup.orderOf_coe (⟨d, hdLB⟩ : ↥LB)]
    exact hd3
  have hd'3 : (⟨d, hdLB⟩ : ↥LB) ^ 3 = 1 := by
    rw [← hd'ord]
    exact pow_orderOf_eq_one _
  have hd'c : (⟨d, hdLB⟩ : ↥LB) ∈ Subgroup.center ↥LB := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hdc y).symm
  let q1 : ↥LB →* ↥LB ⧸ CFSG.pCore 2 ↥LB := QuotientGroup.mk' (CFSG.pCore 2 ↥LB)
  let q2 : (↥LB ⧸ CFSG.pCore 2 ↥LB) →*
      (↥LB ⧸ CFSG.pCore 2 ↥LB) ⧸ Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) :=
    QuotientGroup.mk' (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB))
  let ψ : ↥LB →* alternatingGroup (Fin 6) := eA.toMonoidHom.comp (q2.comp q1)
  have hq1 : Function.Surjective q1 := QuotientGroup.mk'_surjective _
  have hq2 : Function.Surjective q2 := QuotientGroup.mk'_surjective _
  have hψ : Function.Surjective ψ := eA.surjective.comp (hq2.comp hq1)
  have hqd'c : q1 ⟨d, hdLB⟩ ∈ Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := hq1 x
    calc q1 y * q1 ⟨d, hdLB⟩ = q1 (y * ⟨d, hdLB⟩) := by rw [map_mul]
      _ = q1 (⟨d, hdLB⟩ * y) := by rw [hdc y]
      _ = q1 ⟨d, hdLB⟩ * q1 y := by rw [map_mul]
  have hq3 : q1 ⟨d, hdLB⟩ ^ 3 = 1 := by
    rw [← map_pow, hd'3, map_one]
  have hq1ne : q1 ⟨d, hdLB⟩ ≠ 1 := by
    intro h
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥LB)) ⟨d, hdLB⟩ = 1 at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥LB))) ⟨⟨d, hdLB⟩, h⟩
    rw [← Subgroup.orderOf_coe (⟨⟨d, hdLB⟩, h⟩ : ↥(CFSG.pCore 2 ↥LB))] at hn
    rw [hd'ord] at hn
    have h3dvd : 3 ∣ 2 ^ n := hn ▸ dvd_refl 3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    norm_num at h32
  have hqord : orderOf (q1 ⟨d, hdLB⟩) = 3 := orderOf_eq_prime hq3 hq1ne
  have hZeq : Subgroup.zpowers (q1 ⟨d, hdLB⟩) =
      Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hqd'c)
    rw [Nat.card_zpowers, hqord, hZcard]
  haveI hDn : (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hd'c)
  have hle : Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB) ≤ ψ.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    have hq2d : q2 (q1 ⟨d, hdLB⟩) = 1 := by
      change (QuotientGroup.mk' (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)))
        (q1 ⟨d, hdLB⟩) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hqd'c
    show eA (q2 (q1 ⟨d, hdLB⟩)) = 1
    rw [hq2d, map_one]
  let qD : ↥LB →* ↥LB ⧸ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB) :=
    QuotientGroup.mk' (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB))
  let M := ↥LB ⧸ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)
  let η : M →* alternatingGroup (Fin 6) :=
    QuotientGroup.lift (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)) ψ hle
  have hη : Function.Surjective η :=
    QuotientGroup.lift_surjective_of_surjective _ ψ hψ hle
  have hqD : Function.Surjective qD := QuotientGroup.mk'_surjective _
  haveI : Group.IsPerfect LB := hperf
  haveI : Group.IsPerfect M := by
    show Group.IsPerfect (↥LB ⧸ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB))
    infer_instance
  have hker_ge : (CFSG.pCore 2 ↥LB).map qD ≤ η.ker := by
    intro m hm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
    rw [MonoidHom.mem_ker]
    have hq1u : q1 u = 1 := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥LB)) u = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hu
    calc η (qD u) = ψ u := by
          change (QuotientGroup.lift (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)) ψ hle)
            (qD u) = ψ u
          rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
      _ = eA (q2 (q1 u)) := rfl
      _ = 1 := by rw [hq1u, map_one, map_one]
  have hker_le : η.ker ≤ (CFSG.pCore 2 ↥LB).map qD := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm
    obtain ⟨x, rfl⟩ := hqD m
    have hψx : ψ x = 1 := by
      have h := hm
      change (QuotientGroup.lift (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)) ψ hle)
        (qD x) = 1 at h
      rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at h
      exact h
    have hq1x : q1 x ∈ Subgroup.zpowers (q1 ⟨d, hdLB⟩) := by
      have hq2x : q2 (q1 x) = 1 := by
        have hψx' : eA (q2 (q1 x)) = 1 := hψx
        exact eA.injective (by rw [hψx', map_one])
      change (QuotientGroup.mk' (Subgroup.center (↥LB ⧸ CFSG.pCore 2 ↥LB)))
        (q1 x) = 1 at hq2x
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq2x
      rw [hZeq]
      exact hq2x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hq1x
    have hu : ((⟨d, hdLB⟩ : ↥LB) ^ k)⁻¹ * x ∈ CFSG.pCore 2 ↥LB := by
      rw [← QuotientGroup.eq_one_iff]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥LB))
        (((⟨d, hdLB⟩ : ↥LB) ^ k)⁻¹ * x) = 1
      rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel]
    refine Subgroup.mem_map.mpr ⟨((⟨d, hdLB⟩ : ↥LB) ^ k)⁻¹ * x, hu, ?_⟩
    change qD (((⟨d, hdLB⟩ : ↥LB) ^ k)⁻¹ * x) = qD x
    have hqDd : qD (⟨d, hdLB⟩ : ↥LB) = 1 := by
      change (QuotientGroup.mk' (Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB)))
        ⟨d, hdLB⟩ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_zpowers _
    rw [map_mul, map_inv, map_zpow, hqDd, one_zpow, inv_one, one_mul]
  have hker_eq : η.ker = (CFSG.pCore 2 ↥LB).map qD := le_antisymm hker_le hker_ge
  have hx3_of_mem_zpowers : ∀ x ∈ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB), x ^ 3 = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk, ← zpow_natCast ((⟨d, hdLB⟩ : ↥LB) ^ k) 3, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hd'3, one_zpow]
  have hdisj : CFSG.pCore 2 ↥LB ⊓ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxD⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥LB))) ⟨x, hxU⟩
    have hn' : orderOf x = 2 ^ n := by simpa using hn
    have hx3dvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hx3_of_mem_zpowers x hxD)
    have h2n_dvd : 2 ^ n ∣ 3 := hn' ▸ hx3dvd
    have hle3 : 2 ^ n ≤ 3 := Nat.le_of_dvd (by norm_num) h2n_dvd
    have hn1 : n ≤ 1 := by
      by_contra h
      push Not at h
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h4
      omega
    interval_cases n
    · rw [pow_zero] at hn'
      exact orderOf_eq_one_iff.mp hn'
    · rw [pow_one] at hn'
      have h23 : 2 ∣ 3 := hn' ▸ hx3dvd
      norm_num at h23
  have hinj : Function.Injective (fun u : ↥(CFSG.pCore 2 ↥LB) => qD (u : ↥LB)) := by
    intro u v huv
    have huv' : qD (u : ↥LB) = qD (v : ↥LB) := huv
    have h0 : qD ((u : ↥LB) * (v : ↥LB)⁻¹) = 1 := by
      rw [map_mul, map_inv, huv', mul_inv_cancel]
    have h1 : (u : ↥LB) * (v : ↥LB)⁻¹ ∈ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB) :=
      (QuotientGroup.eq_one_iff _).mp h0
    have h2 : (u : ↥LB) * (v : ↥LB)⁻¹ ∈ CFSG.pCore 2 ↥LB :=
      Subgroup.mul_mem _ u.2 (Subgroup.inv_mem _ v.2)
    have h3 : (u : ↥LB) * (v : ↥LB)⁻¹ = 1 := by
      have h4 : (u : ↥LB) * (v : ↥LB)⁻¹ ∈
          CFSG.pCore 2 ↥LB ⊓ Subgroup.zpowers (⟨d, hdLB⟩ : ↥LB) :=
        Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hdisj] at h4
      simpa using h4
    apply Subtype.ext
    calc (u : ↥LB) = (u : ↥LB) * (v : ↥LB)⁻¹ * (v : ↥LB) := by group
      _ = (v : ↥LB) := by rw [h3, one_mul]
  have hmap : ∀ u : ↥(CFSG.pCore 2 ↥LB), qD (u : ↥LB) ∈ η.ker := by
    intro u
    rw [hker_eq]
    exact Subgroup.mem_map_of_mem qD u.2
  have hcard_le : Nat.card ↥(CFSG.pCore 2 ↥LB) ≤ Nat.card ↥η.ker :=
    Nat.card_le_card_of_injective (fun u => (⟨qD (u : ↥LB), hmap u⟩ : ↥η.ker))
      (fun u v huv => hinj (congrArg Subtype.val huv))
  have hK : η.ker ≤ Subgroup.center M := by
    rw [hker_eq]
    exact (Subgroup.map_mono hU'Z).trans
      (Subgroup.map_center_le_center (f := qD) hqD)
  have hK2 : IsPGroup 2 ↥η.ker := by
    rw [hker_eq]
    exact IsPGroup.map (ϕ := qD) (CFSG.pCore_isPGroup (p := 2) (G := ↥LB))
  have hhol := CFSG.Holt.H78.card_ker_le_two_of_alternatingGroup
    (Ψ := Fin 6) (by norm_num) η hη hK hK2
  omega

private lemma commute_of_pCoreOf {L LB : Subgroup G} {d : G} (hJ : J2Config L d LB)
    (hU'Z : CFSG.pCore 2 ↥LB ≤ Subgroup.center ↥LB) :
    ∀ w ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G),
      ∀ l ∈ LB, l * w = w * l := by
  have hUZ : CFSG.Open.pCoreOf 2 LB ≤
      Subgroup.map LB.subtype (Subgroup.center ↥LB) := Subgroup.map_mono hU'Z
  intro w hw l hl
  have hwN : w ∈ Subgroup.normalizer (LB : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hc : ⁅w, x⁆ ∈ CFSG.Open.pCoreOf 2 LB :=
        hJ.commutator_le (Subgroup.commutator_mem_commutator hw hx)
      have hceq : w * x * w⁻¹ = ⁅w, x⁆ * x := by rw [commutatorElement_def]; group
      rw [hceq]
      exact LB.mul_mem (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 LB hc) hx
    · intro hx
      have hc : ⁅w⁻¹, w * x * w⁻¹⁆ ∈ CFSG.Open.pCoreOf 2 LB :=
        hJ.commutator_le (Subgroup.commutator_mem_commutator
          (Subgroup.inv_mem _ hw) hx)
      have hxeq : x = ⁅w⁻¹, w * x * w⁻¹⁆ * (w * x * w⁻¹) := by
        rw [commutatorElement_def]; group
      rw [hxeq]
      exact LB.mul_mem (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 LB hc) hx
  have h := CFSG.ClassicalInvolution.Disconnected.AschTight.commute_of_commutator_mem_center
    (K := LB) hJ.isPerfect_lB (t := w) hwN ?_
  · exact h l hl
  · intro k hk
    have hcomm : ⁅k, w⁆ ∈ ⁅LB, CFSG.Open.pCoreOf 2 L ⊓
        Subgroup.centralizer ({d} : Set G)⁆ :=
      Subgroup.commutator_mem_commutator hk hw
    have hle : ⁅LB, CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)⁆ ≤
        CFSG.Open.pCoreOf 2 LB := by
      rw [Subgroup.commutator_comm]
      exact hJ.commutator_le
    exact hUZ (hle hcomm)

private lemma exists_sq_eq_of_four_le_card {W : Subgroup G} {z : G}
    (hW4 : 4 ≤ Nat.card ↥W) (hW2 : IsPGroup 2 ↥W)
    (huniq : ∀ x ∈ W, x * x = 1 → x = 1 ∨ x = z) :
    ∃ u ∈ W, u * u = z := by
  classical
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    interval_cases m <;> rw [hm] at hW4 <;> norm_num at hW4
  obtain ⟨V, hVcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥W) 2 (n := 2) (by
    rw [hm]
    exact pow_dvd_pow 2 hm2)
  have hVcard4 : Nat.card ↥V = 4 := by
    rw [hVcard]
    norm_num
  have hex : ∃ x : ↥V, (((x : ↥V) : ↥W) : G) ≠ 1 ∧ (((x : ↥V) : ↥W) : G) ≠ z := by
    by_contra h
    push Not at h
    have hinj : Function.Injective
        (fun x : ↥V => if (((x : ↥V) : ↥W) : G) = z then true else false) := by
      intro x y hxy
      by_cases hx : (((x : ↥V) : ↥W) : G) = z
      · have hy : (((y : ↥V) : ↥W) : G) = z := by
          by_contra hy
          simp [hx, hy] at hxy
        exact Subtype.ext (Subtype.ext (hx.trans hy.symm))
      · have hy : (((y : ↥V) : ↥W) : G) ≠ z := by
          intro hy
          simp [hx, hy] at hxy
        have hx1 : (((x : ↥V) : ↥W) : G) = 1 := by
          by_contra hne
          exact absurd (h x hne) hx
        have hy1 : (((y : ↥V) : ↥W) : G) = 1 := by
          by_contra hne
          exact absurd (h y hne) hy
        exact Subtype.ext (Subtype.ext (hx1.trans hy1.symm))
    have hle := Nat.card_le_card_of_injective
      (fun x : ↥V => if (((x : ↥V) : ↥W) : G) = z then true else false) hinj
    have hb : Nat.card Bool = 2 := by simp
    rw [hb] at hle
    omega
  obtain ⟨x, hx1, hxz⟩ := hex
  have hx0W : (((x : ↥V) : ↥W) : G) ∈ W := ((x : ↥V) : ↥W).2
  have hxord : orderOf x = 4 := by
    have hne1 : orderOf x ≠ 1 := by
      intro h
      apply hx1
      have hxeq : x = 1 := orderOf_eq_one_iff.mp h
      simp [hxeq]
    have hx2 : x * x ≠ 1 := by
      intro h
      have hG : (((x : ↥V) : ↥W) : G) * (((x : ↥V) : ↥W) : G) = 1 := by
        have h' := congrArg (fun y : ↥V => (((y : ↥W)) : G)) h
        simpa using h'
      rcases huniq (((x : ↥V) : ↥W) : G) hx0W hG with h1 | hz
      · exact hx1 h1
      · exact hxz hz
    have hne2 : orderOf x ≠ 2 := by
      intro h
      apply hx2
      have h2 : x ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
      rwa [pow_two] at h2
    have hdvd : orderOf x ∣ 4 := by
      have h := orderOf_dvd_natCard x
      rwa [hVcard4] at h
    have hle4 : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases orderOf x <;> simp_all
  have hsq : (((x : ↥V) : ↥W) : G) * (((x : ↥V) : ↥W) : G) = z := by
    have hmem : ((((x : ↥V) : ↥W) : G) ^ 2) ∈ W := W.pow_mem hx0W 2
    have hinv : (((((x : ↥V) : ↥W) : G)) ^ 2) * (((((x : ↥V) : ↥W) : G)) ^ 2) = 1 := by
      rw [← pow_add]
      rw [show (2:ℕ) + 2 = 4 by norm_num]
      have h4 : x ^ 4 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      have h' := congrArg (fun y : ↥V => (((y : ↥W)) : G)) h4
      simpa using h'
    rcases huniq _ hmem hinv with h1 | hz
    · exfalso
      have hx2eq : x ^ 2 = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        simpa using h1
      have h4 : (4:ℕ) ∣ 2 := by
        rw [← hxord]
        exact orderOf_dvd_iff_pow_eq_one.mpr hx2eq
      norm_num at h4
    · rw [pow_two] at hz
      exact hz
  exact ⟨(((x : ↥V) : ↥W) : G), hx0W, hsq⟩

theorem exists_involution {L LB : Subgroup G} {d : G} (hJ : J2Config L d LB)
    (hW4 : 4 ≤ Nat.card ↥(CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)))
    {z : G} (hz : z ∈ Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB)) (hz1 : z ≠ 1) :
    ∃ x ∈ LB ⊔ (CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)),
      x * x = 1 ∧ x ≠ 1 ∧ x ≠ z ∧ x * z = z * x := by
  classical
  obtain ⟨hzU, hzcent, hz2⟩ := (mem_omegaZOf_iff (CFSG.Open.pCoreOf 2 LB)).mp hz
  by_cases hstep1 : ∃ x ∈ CFSG.Open.pCoreOf 2 LB,
      x * x = 1 ∧ x ≠ 1 ∧ x ≠ z
  · obtain ⟨x, hxU, hx2, hx1, hxz⟩ := hstep1
    exact ⟨x, Subgroup.mem_sup_left (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 LB hxU),
      hx2, hx1, hxz, (hzcent x hxU).symm⟩
  push Not at hstep1
  have huniqU : ∀ x ∈ CFSG.Open.pCoreOf 2 LB, x * x = 1 → x = 1 ∨ x = z := by
    intro x hx hx2
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hstep1 x hx hx2 h1)
  have hrank : CFSG.Open.pRank 2 (CFSG.Open.pCoreOf 2 LB) ≤ 1 :=
    pRank_two_le_one_of_unique_involution hz1 hz2 huniqU
  obtain ⟨hZcard, ⟨eA⟩⟩ := hJ.tripleCover
  have h5LB : 5 ∣ Nat.card ↥LB := five_dvd_card_lB hZcard eA
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨f, hford⟩ := exists_prime_orderOf_dvd_card' (G := ↥LB) 5 h5LB
  have hfcent : ∀ u ∈ CFSG.Open.pCoreOf 2 LB, (f : G) * u = u * (f : G) := by
    have hU'rank : CFSG.Open.pRank 2 (⊤ : Subgroup ↥(CFSG.pCore 2 ↥LB)) ≤ 1 := by
      have hle : CFSG.Open.pRank 2 (CFSG.pCore 2 ↥LB) ≤
          CFSG.Open.pRank 2 (CFSG.Open.pCoreOf 2 LB) :=
        CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) LB.subtype
          LB.subtype_injective _
      exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm.trans_le (hle.trans hrank)
    have hfcentU' := commute_pCore_of_orderOf_five f hford hU'rank
    intro u hu
    have hu' : u ∈ Subgroup.map LB.subtype (CFSG.pCore 2 ↥LB) := hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu'
    exact congrArg (fun y : ↥LB => (y : G)) (hfcentU' ⟨x, hx⟩)
  let N : Subgroup G := LB ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 LB : Set G)
  have hNle : N ≤ LB := inf_le_left
  have hfN : (f : G) ∈ N := by
    refine Subgroup.mem_inf.mpr ⟨f.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun u hu => (hfcent u hu).symm
  have h5N : 5 ∣ Nat.card ↥N := by
    have hle : Subgroup.zpowers (f : G) ≤ N := Subgroup.zpowers_le.mpr hfN
    have hcard : Nat.card ↥(Subgroup.zpowers (f : G)) = 5 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe]
      exact hford
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  have hnormN : LB ≤ Subgroup.normalizer (N : Set G) := by
    have hU_norm : LB ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 LB : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf ha hx
      · intro hx
        have h2 : a⁻¹ * (a * x * a⁻¹) * a ∈ CFSG.Open.pCoreOf 2 LB := by
          simpa using CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (LB.inv_mem ha) hx
        have hxA : x = a⁻¹ * (a * x * a⁻¹) * a := by group
        rw [hxA]
        exact h2
    have hC_norm : LB ≤ Subgroup.normalizer
        ((Subgroup.centralizer (CFSG.Open.pCoreOf 2 LB : Set G)) : Set G) :=
      le_trans hU_norm
        (CFSG.ClassicalInvolution.Disconnected.AschTight.normalizer_le_normalizer_centralizer_self
          (K := CFSG.Open.pCoreOf 2 LB))
    intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hh, hC_norm hh⟩)
  have hNeq : N = LB := hJ.eq_lB_of_dvd hNle hnormN (Or.inr h5N)
  have hLBleC : LB ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 LB : Set G) := by
    intro l hl
    have hmem : l ∈ N := by rw [hNeq]; exact hl
    exact (Subgroup.mem_inf.mp hmem).2
  have hUZ : CFSG.Open.pCoreOf 2 LB ≤
      Subgroup.map LB.subtype (Subgroup.center ↥LB) := by
    intro u hu
    have hc : (⟨u, CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 LB hu⟩ : ↥LB) ∈
        Subgroup.center ↥LB := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl : (l : G) ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 LB : Set G) :=
        hLBleC l.2
      exact (Subgroup.mem_centralizer_iff.mp hl u hu).symm
    exact Subgroup.mem_map_of_mem LB.subtype hc
  have hU'Z : CFSG.pCore 2 ↥LB ≤ Subgroup.center ↥LB := by
    intro x hx
    have hxU : (x : G) ∈ CFSG.Open.pCoreOf 2 LB := by
      show LB.subtype x ∈ Subgroup.map LB.subtype (CFSG.pCore 2 ↥LB)
      exact Subgroup.mem_map_of_mem LB.subtype hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hUZ hxU)
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  have hcardU : Nat.card ↥(CFSG.Open.pCoreOf 2 LB) ≤ 2 := by
    have := card_pCore_le_two hJ.mem_lB hJ.orderOf_d
      (fun y => by
        have hyc : (y : G) ∈ Subgroup.centralizer ({d} : Set G) :=
          (Subgroup.mem_inf.mp (hJ.lB_le y.2)).2
        rw [Subgroup.mem_centralizer_singleton_iff] at hyc
        apply Subtype.ext
        exact hyc.symm)
      hJ.isPerfect_lB hJ.tripleCover hU'Z
    rwa [← Subgroup.card_map_of_injective (f := LB.subtype) LB.subtype_injective] at this
  have hUeq : CFSG.Open.pCoreOf 2 LB = Subgroup.zpowers z := by
    have hzle : Subgroup.zpowers z ≤ CFSG.Open.pCoreOf 2 LB := Subgroup.zpowers_le.mpr hzU
    have hzcard : Nat.card ↥(Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rwa [pow_two]) hz1
    exact (Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard]; exact hcardU)).symm
  have hWcent : ∀ w ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G),
      ∀ l ∈ LB, l * w = w * l := commute_of_pCoreOf hJ hU'Z
  have hzLB : z ∈ LB := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 LB hzU
  have hzcomm : ∀ l ∈ LB, l * z = z * l := by
    intro l hl
    have hmem : z ∈ Subgroup.map LB.subtype (Subgroup.center ↥LB) := hUZ hzU
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hmem
    have h := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
    have h' := congrArg (fun y : ↥LB => (y : G)) h
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
    rw [show (c : G) = z from hcz] at h'
    exact h'
  have hzW : z ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hJ.pCoreOf_le hzU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzcomm d hJ.mem_lB).symm
  by_cases hstep5 : ∃ x ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G),
      x * x = 1 ∧ x ≠ 1 ∧ x ≠ z
  · obtain ⟨x, hxW, hx2, hx1, hxz⟩ := hstep5
    exact ⟨x, Subgroup.mem_sup_right hxW, hx2, hx1, hxz, (hWcent x hxW z hzLB).symm⟩
  push Not at hstep5
  have huniqW : ∀ x ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G),
      x * x = 1 → x = 1 ∨ x = z := by
    intro x hx hx2
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hstep5 x hx hx2 h1)
  have hW2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L).to_le inf_le_left
  obtain ⟨u, huW, hu2⟩ := exists_sq_eq_of_four_le_card hW4 hW2 huniqW
  obtain ⟨t, htLB, htU, ht2⟩ := hJ.exists_mul_self_mem
  have ht2' : t * t ∈ Subgroup.zpowers z := by
    rw [← hUeq]
    exact ht2
  have hz2'' : z ^ 2 = 1 := by rwa [pow_two]
  have hz2z : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hz2''
  have ht_cases : t * t = 1 ∨ t * t = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht2'
    rw [← hk, zpow_eq_zpow_emod (x := z) k (n := 2) hz2z]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  have htU' : t ∉ CFSG.Open.pCoreOf 2 LB := htU
  rcases ht_cases with ht1 | htz
  · refine ⟨t, Subgroup.mem_sup_left htLB, ht1, ?_, ?_, hzcomm t htLB⟩
    · intro h
      exact htU' (h ▸ Subgroup.one_mem _)
    · intro h
      exact htU' (h ▸ hzU)
  · refine ⟨t * u, Subgroup.mul_mem _ (Subgroup.mem_sup_left htLB)
      (Subgroup.mem_sup_right huW), ?_, ?_, ?_, ?_⟩
    · have htu : u * t = t * u := (hWcent u huW t htLB).symm
      calc t * u * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [htu]
        _ = (t * t) * (u * u) := by group
        _ = z * z := by rw [htz, hu2]
        _ = 1 := hz2
    · intro h
      apply htU'
      have htW : t ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) := by
        have ht_eq : t = u⁻¹ := by
          calc t = (t * u) * u⁻¹ := by group
            _ = u⁻¹ := by rw [h, one_mul]
        rw [ht_eq]
        exact Subgroup.inv_mem _ huW
      have htO : t ∈ CFSG.Open.pCoreOf 2 L := (Subgroup.mem_inf.mp htW).1
      have htinf : t ∈ LB ⊓ CFSG.Open.pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨htLB, htO⟩
      rwa [hJ.lB_inf_pCoreOf] at htinf
    · intro h
      apply htU'
      have htW : t ∈ CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({d} : Set G) := by
        have ht_eq : t = z * u⁻¹ := by
          calc t = (t * u) * u⁻¹ := by group
            _ = z * u⁻¹ := by rw [h]
        rw [ht_eq]
        exact Subgroup.mul_mem _ hzW (Subgroup.inv_mem _ huW)
      have htO : t ∈ CFSG.Open.pCoreOf 2 L := (Subgroup.mem_inf.mp htW).1
      have htinf : t ∈ LB ⊓ CFSG.Open.pCoreOf 2 L := Subgroup.mem_inf.mpr ⟨htLB, htO⟩
      rwa [hJ.lB_inf_pCoreOf] at htinf
    · have huz : u * z = z * u := (hWcent u huW z hzLB).symm
      have htz' : t * z = z * t := hzcomm t htLB
      calc t * u * z = t * (u * z) := by group
        _ = t * (z * u) := by rw [huz]
        _ = z * (t * u) := by
              have : t * (z * u) = (t * z) * u := by group
              rw [this, htz']
              group
