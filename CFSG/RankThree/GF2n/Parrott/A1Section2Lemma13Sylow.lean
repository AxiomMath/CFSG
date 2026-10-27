module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Free
public import CFSG.RankThree.GF2n.Parrott.A1ModelFacts
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem isSylowOf_of_card_le_two_mul {K L B : Subgroup G} (hKL : K ≤ L) (hK : IsPGroup 2 K)
    (hBK : B ≤ K) {x : G} (hxK : x ∈ K) (hxB : x ∉ B)
    (hS : ∀ S : Subgroup G, S ≤ L → IsPGroup 2 S → Nat.card S ≤ 2 * Nat.card B) :
    IsSylowOf 2 K L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : 2 * Nat.card B ≤ Nat.card K := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hBK
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hxB
      rw [Subgroup.eq_of_le_of_card_ge hBK (by rw [hm, mul_one])]
      exact hxK
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    rw [hm, mul_comm 2]
    exact Nat.mul_le_mul_left _ (by omega)
  have hKsub : IsPGroup 2 (K.subgroupOf L) := hK.comap_subtype
  obtain ⟨Q, hKQ⟩ := hKsub.exists_le_sylow
  have hKS : K ≤ (Q : Subgroup L).map L.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKL]
    exact Subgroup.map_mono hKQ
  have hcard := hS _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map L.subtype)
  exact ⟨Q, (Subgroup.eq_of_le_of_card_ge hKS (hcard.trans hK2)).symm⟩

section Bound

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem card_le_two_mul_card_inf_J {S : Subgroup G} (hSH : S ≤ H z)
    (hSs : S ≤ Subgroup.centralizer
      ({((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹} : Set G))
    (hS2 : IsPGroup 2 S) :
    Nat.card S ≤ 2 * Nat.card (S ⊓ J z : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥S →* ↥QP45.originalSubgroup := (qHP D).comp (Subgroup.inclusion hSH)
  have hker : φ.ker.map S.subtype = S ⊓ J z := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have hk : Subgroup.inclusion hSH y ∈ (qHP D).ker := hy
      rw [ker_qHP] at hk
      exact Subgroup.mem_subgroupOf.mp hk
    · rintro ⟨hgS, hgJ⟩
      refine ⟨⟨g, hgS⟩, ?_, rfl⟩
      have hk : Subgroup.inclusion hSH ⟨g, hgS⟩ ∈ (qHP D).ker := by
        rw [ker_qHP]
        exact Subgroup.mem_subgroupOf.mpr hgJ
      exact hk
  have hkercard : Nat.card φ.ker = Nat.card (S ⊓ J z : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective S.subtype_injective]
  have hle : φ.range ≤ Subgroup.centralizer
      ({(⟨sigma1, sigma1_mem_Q⟩ : ↥QP45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_Q⟩ : ↥QP45.originalSubgroup)⁻¹} : Set ↥QP45.originalSubgroup) := by
    intro g hg
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyH : Subgroup.inclusion hSH y * (s1HP D * (s2HP D)⁻¹) =
        (s1HP D * (s2HP D)⁻¹) * Subgroup.inclusion hSH y :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hSs y.2))
    have h := congrArg (qHP D) hyH
    simp only [map_mul, map_inv, qHP_s1HP, qHP_s2HP] at h
    exact h
  have hdvd : Nat.card φ.range ∣ 54 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [qp45_card_centralizer_s1s2inv] at h
  have hp : IsPGroup 2 φ.range := hS2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hn1 : n ≤ 1 := by
    by_contra hcon
    have h4 : (4 : ℕ) ∣ 54 := by
      have h4n : (4 : ℕ) ∣ 2 ^ n := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
      exact h4n.trans (by rw [← hn]; exact hdvd)
    omega
  have hrange : Nat.card φ.range ≤ 2 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 2 := by norm_num
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hkercard] at h
  calc Nat.card S = Nat.card (S ⊓ J z : Subgroup G) * Nat.card φ.range := h.symm
    _ ≤ Nat.card (S ⊓ J z : Subgroup G) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (S ⊓ J z : Subgroup G) := mul_comm _ _

end Bound

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem card_le_two_mul_card_inf_centralizer {B : Subgroup G} (hBH : B ≤ H z) {w : G}
    (hwH : w ∈ H z) (hBw : ∀ b ∈ B, b * w * b⁻¹ * w⁻¹ ∈ zpowers z) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
  let f : ↥B →* G := MonoidHom.mk' (fun b => (b : G) * w * (b : G)⁻¹ * w⁻¹) (fun a b => by
    set d := (b : G) * w * (b : G)⁻¹ * w⁻¹ with hd
    have hdz : d ∈ zpowers z := hBw b b.2
    have had : (a : G) * d = d * a := hy.commute_of_mem_zpowers_of_mem_H (hBH a.2) hdz
    have hxH : (a : G) * w * (a : G)⁻¹ * w⁻¹ ∈ H z :=
      (H z).mul_mem ((H z).mul_mem ((H z).mul_mem (hBH a.2) hwH)
        ((H z).inv_mem (hBH a.2))) ((H z).inv_mem hwH)
    have hdx := hy.commute_of_mem_zpowers_of_mem_H hxH hdz
    have hbw : (b : G) * w * (b : G)⁻¹ = d * w := by rw [hd]; group
    change (a : G) * b * w * ((a : G) * b)⁻¹ * w⁻¹ =
      ((a : G) * w * (a : G)⁻¹ * w⁻¹) * ((b : G) * w * (b : G)⁻¹ * w⁻¹)
    calc (a : G) * b * w * ((a : G) * b)⁻¹ * w⁻¹
        = (a : G) * ((b : G) * w * (b : G)⁻¹) * (a : G)⁻¹ * w⁻¹ := by group
      _ = (a : G) * (d * w) * (a : G)⁻¹ * w⁻¹ := by rw [hbw]
      _ = ((a : G) * d) * w * (a : G)⁻¹ * w⁻¹ := by group
      _ = (d * a) * w * (a : G)⁻¹ * w⁻¹ := by rw [had]
      _ = d * ((a : G) * w * (a : G)⁻¹ * w⁻¹) := by group
      _ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) * d := hdx.symm
      _ = ((a : G) * w * (a : G)⁻¹ * w⁻¹) * ((b : G) * w * (b : G)⁻¹ * w⁻¹) := by rw [hd])
  have hker : f.ker.map B.subtype = B ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.2, ?_⟩
      have h1 : (b : G) * w * (b : G)⁻¹ * w⁻¹ = 1 := hb
      calc (b : G) * w = (b : G) * w * (b : G)⁻¹ * w⁻¹ * (w * b) := by group
        _ = w * b := by rw [h1, one_mul]
    · rintro ⟨hgB, hgw⟩
      refine ⟨⟨g, hgB⟩, ?_, rfl⟩
      change g * w * g⁻¹ * w⁻¹ = 1
      rw [hgw]
      group
  have hkercard : Nat.card f.ker =
      Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective B.subtype_injective]
  have hrange : Nat.card f.range ≤ 2 := by
    have hle : f.range ≤ zpowers z := by
      intro g hg
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hg
      exact hBw b b.2
    have := Subgroup.card_le_of_le hle
    rwa [hy.card_zpowers_z] at this
  have h := Subgroup.card_ker_mul_card_range f
  rw [hkercard] at h
  calc Nat.card B = Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) *
        Nat.card f.range := h.symm
    _ ≤ Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) * 2 :=
        Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) := mul_comm _ _

theorem card_le_two_mul_card_inf_centralizer_of_le_J {B : Subgroup G} (hBJ : B ≤ J z) {w : G}
    (hw : w ∈ J z) :
    Nat.card B ≤ 2 * Nat.card (B ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) :=
  hy.card_le_two_mul_card_inf_centralizer (hBJ.trans J_le_H) (J_le_H hw)
    fun _ hb => hy.comm_mem (hBJ hb) hw

theorem exists_not_commute_of_le_J {M : Subgroup G} (hMJ : M ≤ J z) (hM : 32 ≤ Nat.card M)
    (hZ : ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → a ∈ zpowers z) {c : G} (hc : c ∈ J z) :
    ∃ a ∈ M, ∃ b ∈ M, a * c = c * a ∧ b * c = c * b ∧ a * b ≠ b * a := by
  set A := M ⊓ Subgroup.centralizer ({c} : Set G) with hA
  by_contra hcon
  push Not at hcon
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    hcon a ha.1 b hb.1 (Subgroup.mem_centralizer_singleton_iff.mp ha.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  have hAJ : A ≤ J z := inf_le_left.trans hMJ
  have hMA : Nat.card M ≤ 2 * Nat.card A := hy.card_le_two_mul_card_inf_centralizer_of_le_J hMJ hc
  have hAM : ∃ w ∈ M, w ∉ A := by
    by_contra hall
    push Not at hall
    have hle : M ≤ zpowers z := fun a ha =>
      hZ a ha (fun d hd => hAab a (hall a ha) d (hall d hd))
    have := Subgroup.card_le_of_le hle
    rw [hy.card_zpowers_z] at this
    omega
  obtain ⟨w, hwM, hwA⟩ := hAM
  set Aw := A ⊓ Subgroup.centralizer ({w} : Set G) with hAw
  have hAw2 : Nat.card A ≤ 2 * Nat.card Aw :=
    hy.card_le_two_mul_card_inf_centralizer_of_le_J hAJ (hMJ hwM)
  have hsup : A ⊔ zpowers w = M := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.mpr hwM))
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : A ≤ A ⊔ zpowers w)
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hwA
      rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ zpowers w) (by rw [hm, mul_one])]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    have hm0 : m ≠ 0 := by
      rintro rfl
      have hpos : 0 < Nat.card (A ⊔ zpowers w : Subgroup G) := Nat.card_pos
      omega
    rw [hm]
    have : 2 ≤ m := by omega
    nlinarith
  have hAwz : Aw ≤ zpowers z := by
    intro a ha
    apply hZ a ha.1.1
    intro d hd
    have hle : A ⊔ zpowers w ≤ Subgroup.centralizer ({a} : Set G) := by
      apply sup_le
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hAab a ha.1 b hb).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp ha.2).symm
    have hd' := hle (by rw [hsup]; exact hd)
    rw [Subgroup.mem_centralizer_singleton_iff] at hd'
    exact hd'.symm
  have := Subgroup.card_le_of_le hAwz
  rw [hy.card_zpowers_z] at this
  omega

omit [Finite G] hy in
theorem commute_s_of_t1 {t₁ : G} (hts1 : t₁ * s1 = s1 * t₁) (hts2 : t₁ * s2 = s2 * t₁) :
    t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁ := by
  have hts2' : t₁ * s2⁻¹ = s2⁻¹ * t₁ := by
    calc t₁ * s2⁻¹ = s2⁻¹ * (s2 * t₁) * s2⁻¹ := by group
      _ = s2⁻¹ * (t₁ * s2) * s2⁻¹ := by rw [hts2]
      _ = s2⁻¹ * t₁ := by group
  calc t₁ * (s1 * s2⁻¹) = (t₁ * s1) * s2⁻¹ := by group
    _ = (s1 * t₁) * s2⁻¹ := by rw [hts1]
    _ = s1 * (t₁ * s2⁻¹) := by group
    _ = s1 * (s2⁻¹ * t₁) := by rw [hts2']
    _ = (s1 * s2⁻¹) * t₁ := by group

omit [Finite G] hy in
theorem zpowers_commute_CJs {t₁ : G} (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁) :
    ∀ τ ∈ zpowers t₁, ∀ c ∈ CJ z (s1 * s2⁻¹), τ * c = c * τ := by
  intro τ hτ c hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  exact (Commute.zpow_left (show Commute t₁ c from htC c hc) k).eq

omit hy in
theorem T2_le {t₁ : G} (ht₁H : t₁ ∈ H z) (hts : t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁) :
    CJ z (s1 * s2⁻¹) ⊔ zpowers t₁ ≤
      Subgroup.centralizer ({s1 * s2⁻¹} : Set G) ⊓ H z := by
  apply sup_le
  · intro c hc
    exact ⟨(mem_CJ.mp hc).1, J_le_H ((CJ_le_J _) hc)⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hts, ht₁H⟩

theorem isPGroup_T2 {t₁ : G} (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁)
    (ht2 : t₁ * t₁ ∈ zpowers z) : IsPGroup 2 (CJ z (s1 * s2⁻¹) ⊔ zpowers t₁ : Subgroup G) := by
  have hC2 : IsPGroup 2 (CJ z (s1 * s2⁻¹)) := hy.hA1.extraspecial.1.to_le (CJ_le_J _)
  have h4 : t₁ ^ 4 = 1 := by
    rcases hy.mem_zpowers_z_iff.mp ht2 with h1 | h1
    · calc t₁ ^ 4 = (t₁ * t₁) * (t₁ * t₁) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [h1, one_mul]
    · calc t₁ ^ 4 = (t₁ * t₁) * (t₁ * t₁) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [h1, hy.z_sq]
  have hτ2 : IsPGroup 2 (zpowers t₁) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨2, Subtype.ext ?_⟩
    change (t₁ ^ k) ^ 2 ^ 2 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num [h4]
  exact hC2.to_sup_of_normal_left' hτ2
    (le_normalizer_of_commute fun τ hτ c hc => Hyp.zpowers_commute_CJs htC τ hτ c hc)

theorem comm_mem_T2 {t₁ : G} (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁) {a b : G}
    (ha : a ∈ CJ z (s1 * s2⁻¹) ⊔ zpowers t₁) (hb : b ∈ CJ z (s1 * s2⁻¹) ⊔ zpowers t₁) :
    a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have hτc := Hyp.zpowers_commute_CJs htC
  have hn : zpowers t₁ ≤ Subgroup.normalizer (CJ z (s1 * s2⁻¹) : Set G) :=
    le_normalizer_of_commute fun τ hτ c hc => hτc τ hτ c hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at ha hb
  obtain ⟨c1, hc1, τ1, hτ1, rfl⟩ := ha
  obtain ⟨c2, hc2, τ2, hτ2, rfl⟩ := hb
  have h12 : τ1 * c2 = c2 * τ1 := hτc τ1 hτ1 c2 hc2
  have h21 : τ2 * c1⁻¹ = c1⁻¹ * τ2 := hτc τ2 hτ2 c1⁻¹ ((CJ z (s1 * s2⁻¹)).inv_mem hc1)
  have hττ : τ1 * τ2 = τ2 * τ1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ1
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ2
    exact (Commute.zpow_zpow_self t₁ k l).eq
  have e : c1 * τ1 * (c2 * τ2) * (c1 * τ1)⁻¹ * (c2 * τ2)⁻¹ = c1 * c2 * c1⁻¹ * c2⁻¹ := by
    calc c1 * τ1 * (c2 * τ2) * (c1 * τ1)⁻¹ * (c2 * τ2)⁻¹
        = c1 * (τ1 * c2) * τ2 * τ1⁻¹ * c1⁻¹ * τ2⁻¹ * c2⁻¹ := by group
      _ = c1 * (c2 * τ1) * τ2 * τ1⁻¹ * c1⁻¹ * τ2⁻¹ * c2⁻¹ := by rw [h12]
      _ = c1 * c2 * (τ1 * τ2) * τ1⁻¹ * c1⁻¹ * τ2⁻¹ * c2⁻¹ := by group
      _ = c1 * c2 * (τ2 * τ1) * τ1⁻¹ * c1⁻¹ * τ2⁻¹ * c2⁻¹ := by rw [hττ]
      _ = c1 * c2 * (τ2 * c1⁻¹) * τ2⁻¹ * c2⁻¹ := by group
      _ = c1 * c2 * (c1⁻¹ * τ2) * τ2⁻¹ * c2⁻¹ := by rw [h21]
      _ = c1 * c2 * c1⁻¹ * c2⁻¹ := by group
  rw [e]
  exact hy.comm_mem ((CJ_le_J _) hc1) ((CJ_le_J _) hc2)

theorem mem_H_of_mem_normalizer {K : Subgroup G} (hzK : z ∈ ⁅K, K⁆) (hKz : ⁅K, K⁆ ≤ zpowers z)
    {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ H z := by
  have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hmap : (⁅K, K⁆).map (MulAut.conj g).toMonoidHom = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, hKmap]
  have hmem : g * z * g⁻¹ ∈ ⁅K, K⁆ := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzK
    rw [hmap] at h
    simpa [MulAut.conj_apply] using h
  rcases hy.mem_zpowers_z_iff.mp (hKz hmem) with h1 | h1
  · exfalso
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have h2 := hy.orderOf_z
    rw [hz1, orderOf_one] at h2
    omega
  · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h1]

end Hyp

section Inputs

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem not_mem_J_of_mem_tJ {t₁ : G} (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z) :
    t₁ ∉ J z := by
  intro ht₁
  have httJ : ((tHP D : ↥(H z)) : G) ∈ J z := by
    have e : ((tHP D : ↥(H z)) : G) = t₁ * (((tHP D : ↥(H z)) : G)⁻¹ * t₁)⁻¹ := by group
    rw [e]
    exact (J z).mul_mem ht₁ ((J z).inv_mem ht₁J)
  have hk : tHP D ∈ (qHP D).ker := by
    rw [ker_qHP]
    exact Subgroup.mem_subgroupOf.mpr httJ
  have hq : qHP D (tHP D) = 1 := hk
  rw [qHP_tHP] at hq
  exact t_ne_one (congrArg Subtype.val hq)

variable (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G))
include hy

theorem reduce_t1 {t₁ : G} (ht₁H : t₁ ∈ H z) (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z)
    (hts1 : t₁ * ((s1HP D : ↥(H z)) : G) = ((s1HP D : ↥(H z)) : G) * t₁)
    (hts : t₁ * (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) =
      (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) * t₁)
    (htC : ∀ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹),
      t₁ * c = c * t₁) (ht2 : t₁ * t₁ ∈ zpowers z) :
    ∀ ⦃x : G⦄, (∃ j ∈ J z, x = t₁ * j) → orderOf x = 2 →
      ∃ h ∈ H z, ∃ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹),
        h * x * h⁻¹ = t₁ * c := by
  intro x hx hx2
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h
  obtain ⟨r, hr, c, hc, hrc⟩ := hy.exists_conj_mem_of_free ht₁H htC
    (mem_commutator_conj_iff ht₁H hts) ht2
    (hy.free_of_t1 D rfl ht₁H ht₁J hts1 hts htC ht2) hx hxx
  exact ⟨r, J_le_H (hy.R_le_J hr), c, hc, hrc⟩

theorem facts_T2 {t₁ : G} (ht₁H : t₁ ∈ H z) (ht₁nJ : t₁ ∉ J z)
    (hts : t₁ * (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) =
      (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) * t₁)
    (htC : ∀ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹),
      t₁ * c = c * t₁) (ht2 : t₁ * t₁ ∈ zpowers z) :
    ∀ ⦃x : G⦄, (∃ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹),
        x = t₁ * c) → orderOf x = 2 →
      IsSylowOf 2 (Subgroup.centralizer ({x} : Set G) ⊓
          (CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) ⊔ zpowers t₁))
          (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer
            ({((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹} : Set G)) ∧
        z ∈ ⁅Subgroup.centralizer ({x} : Set G) ⊓
            (CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) ⊔ zpowers t₁),
          Subgroup.centralizer ({x} : Set G) ⊓
            (CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) ⊔ zpowers t₁)⁆ ∧
        ⁅Subgroup.centralizer ({x} : Set G) ⊓
            (CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) ⊔ zpowers t₁),
          Subgroup.centralizer ({x} : Set G) ⊓
            (CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹) ⊔ zpowers t₁)⁆ ≤
          zpowers z := by
  set s : G := ((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹ with hs
  set C := CJ z s with hC
  set T2 := C ⊔ zpowers t₁ with hT2
  rintro x ⟨c, hc, rfl⟩ _
  set K := Subgroup.centralizer ({t₁ * c} : Set G) ⊓ T2 with hK
  have hcJ : c ∈ J z := (CJ_le_J _) hc
  have hxJ : t₁ * c ∉ J z := by
    intro h
    apply ht₁nJ
    have e : t₁ = t₁ * c * c⁻¹ := by group
    rw [e]
    exact (J z).mul_mem h ((J z).inv_mem hcJ)
  have hCT : C ≤ T2 := le_sup_left
  have ht₁T : t₁ ∈ T2 := Subgroup.mem_sup_right (Subgroup.mem_zpowers t₁)
  have hCK : ∀ a ∈ C, a * c = c * a → a ∈ K := by
    intro a ha hac
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hCT ha⟩
    calc a * (t₁ * c) = (a * t₁) * c := by group
      _ = (t₁ * a) * c := by rw [htC a ha]
      _ = t₁ * (a * c) := by group
      _ = t₁ * (c * a) := by rw [hac]
      _ = t₁ * c * a := by group
  have hKz : ⁅K, K⁆ ≤ zpowers z := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hy.comm_mem_T2 htC ha.2 hb.2
  have hzK : z ∈ ⁅K, K⁆ := by
    obtain ⟨a, haC, b, hbC, hac, hbc, hab⟩ := hy.exists_not_commute_of_le_J (CJ_le_J _)
      (by rw [hy.card_Cs]) (fun a ha hcomm => hy.mem_zpowers_of_mem_CJs_of_commute ha hcomm) hcJ
    have hmem : ⁅a, b⁆ ∈ ⁅K, K⁆ :=
      Subgroup.commutator_mem_commutator (hCK a haC hac) (hCK b hbC hbc)
    rcases hy.mem_zpowers_z_iff.mp (hKz hmem) with h1 | h1
    · exfalso
      apply hab
      rw [commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · rw [← h1]
      exact hmem
  refine ⟨?_, hzK, hKz⟩
  have hT2le := Hyp.T2_le ht₁H hts
  have hKsyl : IsSylowOf 2 K (H z ⊓ (Subgroup.centralizer ({t₁ * c} : Set G) ⊓
      Subgroup.centralizer ({s} : Set G))) := by
    have hxK : t₁ * c ∈ K :=
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, T2.mul_mem ht₁T (hCT hc)⟩
    refine isSylowOf_of_card_le_two_mul (B := C ⊓ Subgroup.centralizer ({t₁ * c} : Set G))
      (fun g hg => ⟨(hT2le hg.2).2, hg.1, (hT2le hg.2).1⟩)
      ((hy.isPGroup_T2 htC ht2).to_le inf_le_right) (fun g hg => ⟨hg.2, hCT hg.1⟩) hxK
      (fun h => hxJ ((CJ_le_J _) h.1)) ?_
    intro S hSL hS2
    have h := card_le_two_mul_card_inf_J D (hSL.trans inf_le_left)
      (hSL.trans (inf_le_right.trans inf_le_right)) hS2
    have hle : S ⊓ J z ≤ C ⊓ Subgroup.centralizer ({t₁ * c} : Set G) := fun g hg =>
      ⟨mem_CJ.mpr ⟨((hSL hg.1).2).2, hg.2⟩, ((hSL hg.1).2).1⟩
    have := Subgroup.card_le_of_le hle
    omega
  exact CFSG.GroupTheory.isSylowOf_of_forall_pElement_normalizer_le hKsyl
    fun g _ hgN _ => hy.mem_H_of_mem_normalizer hzK hKz hgN

end Inputs

omit [Finite G] in
theorem normalizer_zpowers_eq_mul {σ u : G} (hσ3 : orderOf σ = 3) (huH : u ∈ H z)
    (hu : u * σ * u⁻¹ = σ⁻¹) :
    ∀ n ∈ Subgroup.normalizer (zpowers σ : Set G),
      ∃ h ∈ Subgroup.normalizer (zpowers σ : Set G) ⊓ H z,
      ∃ c ∈ Subgroup.centralizer (zpowers σ : Set G), h * c = n := by
  intro n hn
  have hσ3' : σ ^ 3 = 1 := hσ3 ▸ pow_orderOf_eq_one σ
  have hcent : ∀ c : G, c * σ = σ * c → c ∈ Subgroup.centralizer (zpowers σ : Set G) := by
    intro c hcσ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute σ c from hcσ.symm) k).eq
  have hnσ : n * σ * n⁻¹ ∈ zpowers σ :=
    (Subgroup.mem_normalizer_iff.mp hn σ).mp (Subgroup.mem_zpowers σ)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnσ
  have hkmod : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  have hpow : σ ^ k = σ ^ (k % ((3 : ℕ) : ℤ)) := by rw [← hσ3, zpow_mod_orderOf]
  rcases hkmod with h0 | h1 | h2
  · exfalso
    have hσ1 : σ = 1 := by
      have e : n * σ * n⁻¹ = 1 := by
        rw [← hk, hpow]
        norm_num [h0]
      calc σ = n⁻¹ * (n * σ * n⁻¹) * n := by group
        _ = 1 := by rw [e]; group
    rw [hσ1, orderOf_one] at hσ3
    omega
  · have e : n * σ * n⁻¹ = σ := by
      rw [← hk, hpow]
      norm_num [h1]
    refine ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, n, hcent n ?_, one_mul n⟩
    calc n * σ = (n * σ * n⁻¹) * n := by group
      _ = σ * n := by rw [e]
  · have e : n * σ * n⁻¹ = σ⁻¹ := by
      rw [← hk, hpow]
      have : k % ((3 : ℕ) : ℤ) = 2 := by exact_mod_cast h2
      rw [this, eq_inv_iff_mul_eq_one, zpow_two, ← pow_three']
      exact hσ3'
    have huN : u ∈ Subgroup.normalizer (zpowers σ : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change zpowers (u * σ * u⁻¹) = zpowers σ
      rw [hu, Subgroup.zpowers_inv]
    refine ⟨u, ⟨huN, huH⟩, u⁻¹ * n, hcent _ ?_, by group⟩
    have hu' : u⁻¹ * σ⁻¹ = σ * u⁻¹ := by
      calc u⁻¹ * σ⁻¹ = u⁻¹ * (u * σ * u⁻¹) := by rw [hu]
        _ = σ * u⁻¹ := by group
    calc u⁻¹ * n * σ = u⁻¹ * (n * σ * n⁻¹) * n := by group
      _ = u⁻¹ * σ⁻¹ * n := by rw [e]
      _ = σ * u⁻¹ * n := by rw [hu']
      _ = σ * (u⁻¹ * n) := by group

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
