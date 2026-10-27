module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Q
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem s_mem : s1 * s2⁻¹ ∈ H z := (H z).mul_mem hy.s1_mem ((H z).inv_mem hy.s2_mem)

theorem s1_mul_s : s1 * (s1 * s2⁻¹) = (s1 * s2⁻¹) * s1 := by
  have h : s1 * s2⁻¹ = s2⁻¹ * s1 := by
    calc s1 * s2⁻¹ = s2⁻¹ * (s2 * s1) * s2⁻¹ := by group
      _ = s2⁻¹ * (s1 * s2) * s2⁻¹ := by rw [hy.comm12]
      _ = s2⁻¹ * s1 := by group
  calc s1 * (s1 * s2⁻¹) = s1 * (s2⁻¹ * s1) := by rw [h]
    _ = (s1 * s2⁻¹) * s1 := by group

theorem mem_zpowers_of_mem_CJs_of_mem_R {a : G} (haC : a ∈ CJ z (s1 * s2⁻¹)) (haR : a ∈ hy.R) :
    a ∈ zpowers z := by
  rw [← hy.infS]
  exact ⟨haC, haR⟩

theorem s1_fix_imV_R {v : V z} (hv : v ∈ imV z hy.R)
    (hfix : conjVA z (⟨s1, hy.s1_mem⟩ : ↥(H z)) v = v) : v = 1 := by
  obtain ⟨r, hr, rfl⟩ := mem_imV.mp hv
  have hc := (conjVA_pi_eq_iff hy.hA1 _ r).mp hfix
  have hcomm := hy.commute_of_cube hy.s1_mem hy.s1_pow_three hc
  have hrJ0 : (r : G) ∈ CJ z s1 := by
    refine mem_CJ.mpr ⟨?_, r.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  exact (pi_eq_one_iff hy.hA1).mpr (hy.mem_zpowers_of_mem_CJs_of_mem_R (hy.J0_le_CJs hrJ0) hr)

section Faithful

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

omit hy [Finite G]
  in
theorem isSimpleGroup_quotient (D : QuotientDataPSp (z := z) hN) :
    IsSimpleGroup (↥(H z) ⧸ (J z).subgroupOf (H z)) := by
  have hX : IsSimpleGroup D.X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) D.lie
  exact D.iso.isSimpleGroup

theorem mem_J_of_conjVA_eq_one (hs1 : s1 = ((s1HP D : ↥(H z)) : G)) {y : ↥(H z)}
    (hyV : ∀ v, conjVA z y v = v) : (y : G) ∈ J z := by
  have hsimple := isSimpleGroup_quotient D
  let N : Subgroup ↥(H z) := (conjVA z).ker
  have hJN : (J z).subgroupOf (H z) ≤ N := by
    intro j hj
    rw [MonoidHom.mem_ker]
    ext v
    exact conjVA_apply_of_mem_J hy.hA1 (Subgroup.mem_subgroupOf.mp hj) v
  let π := QuotientGroup.mk' ((J z).subgroupOf (H z))
  have hNmap : (N.map π).Normal := Subgroup.Normal.map (MonoidHom.normal_ker _) π
    (QuotientGroup.mk'_surjective _)
  rcases hNmap.eq_bot_or_eq_top with hbot | htop
  · have hyN : y ∈ N := by
      rw [MonoidHom.mem_ker]
      ext v
      exact hyV v
    have : π y ∈ N.map π := ⟨y, hyN, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    have hy' : y ∈ (J z).subgroupOf (H z) := (QuotientGroup.eq_one_iff y).mp this
    exact Subgroup.mem_subgroupOf.mp hy'
  · exfalso
    have hsm : π (s1HP D) ∈ N.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨n, hn, hnπ⟩ := hsm
    have hnJ : n⁻¹ * s1HP D ∈ (J z).subgroupOf (H z) := by
      rw [← QuotientGroup.eq]
      exact hnπ
    have hsN : s1HP D ∈ N := by
      have : s1HP D = n * (n⁻¹ * s1HP D) := by group
      rw [this]
      exact N.mul_mem hn (hJN hnJ)
    have hcent : ∀ j ∈ J z, s1 * j = j * s1 := by
      intro j hj
      have hfix : conjVA z (s1HP D) (pi z ⟨j, hj⟩) = pi z ⟨j, hj⟩ := by
        rw [MonoidHom.mem_ker] at hsN
        rw [hsN]
        rfl
      have hc := (conjVA_pi_eq_iff hy.hA1 _ ⟨j, hj⟩).mp hfix
      rw [hs1]
      exact hy.commute_of_cube (s1HP D).2 (by rw [← hs1]; exact hy.s1_pow_three) (by
        rw [← hs1] at hc ⊢; exact hc)
    have hs1J : s1 ∈ J z := hy.hA1.centralizer_le ⟨hy.s1_mem,
      Subgroup.mem_centralizer_iff.mpr fun j hj => (hcent j hj).symm⟩
    have h2 : IsPGroup 2 (J z) := hy.hA1.extraspecial.1
    obtain ⟨k, hk⟩ := h2 ⟨s1, hs1J⟩
    have hk' : s1 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : (3 : ℕ) ∣ 2 ^ k := hy.orderOf_s1 ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem card_fixIn_t1_sq_le (hs1 : s1 = ((s1HP D : ↥(H z)) : G)) {t₁ : G} (ht₁H : t₁ ∈ H z)
    (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z) (hts1 : t₁ * s1 = s1 * t₁)
    (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁) :
    Nat.card (fixIn (imV z hy.R) (conjVA z (⟨t₁, ht₁H⟩ : ↥(H z)))) ^ 2 ≤
      Nat.card (imV z hy.R) := by
  set tH : ↥(H z) := ⟨t₁, ht₁H⟩ with htH
  set sH : ↥(H z) := ⟨s1, hy.s1_mem⟩ with hsH
  set τ := conjVA z tH with hτ
  set β := conjVA z sH with hβ
  have hRJ : hy.R ≤ J z := hy.R_le_J
  have hB : Nat.card (imV z hy.R) = 16 := by
    have h := card_imV hy.hA1 hRJ hy.zpowers_le_R
    rw [hy.card_R] at h
    omega
  set B := imV z hy.R with hBdef
  have hβB : ∀ v, β v ∈ B ↔ v ∈ B :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R sH (mem_commutator_conj_iff hy.s1_mem hy.s1_mul_s)
  have hβτ : ∀ v, β (τ v) = τ (β v) := by
    intro v
    have e : sH * tH = tH * sH := Subtype.ext hts1.symm
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, e]
  have hβ3 : ∀ v, (β ^ 3) v = v := by
    intro v
    have : sH ^ 3 = 1 := Subtype.ext (by simpa [hsH] using hy.s1_pow_three)
    rw [← map_pow, this, map_one]
    rfl
  set F := fixIn B τ with hF
  have hβF : ∀ v, β v ∈ F ↔ v ∈ F := by
    have fwd : ∀ v, v ∈ F → β v ∈ F := fun v hv =>
      ⟨(hβB v).mpr hv.1, by rw [← hβτ, hv.2]⟩
    intro v
    refine ⟨fun h => ?_, fwd v⟩
    have h2 := fwd _ (fwd _ h)
    have e : β (β (β v)) = v := by
      have := hβ3 v
      simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using this
    rwa [e] at h2
  have hmod := card_modEq_one_of_cube F β hβF (fun v _ => hβ3 v)
    (fun v hv hfix => hy.s1_fix_imV_R hv.1 hfix)
  have hdvd : Nat.card F ∣ 16 := hB ▸ Subgroup.card_dvd_of_le (fixIn_le B τ)
  have hne : Nat.card F ≠ 16 := by
    intro h16
    have hFB : F = B := Subgroup.eq_of_le_of_card_ge (fixIn_le B τ) (by rw [h16, hB])
    have hall : ∀ v, τ v = v := by
      intro v
      obtain ⟨j, rfl⟩ := pi_surjective z v
      obtain ⟨c, hc, r, hr, hjcr⟩ := hy.exists_mul_of_mem_J j.2
      have hcJ : c ∈ J z := (CJ_le_J _) hc
      have hrJ : r ∈ J z := hy.R_le_J hr
      have hj : j = ⟨c, hcJ⟩ * ⟨r, hrJ⟩ := Subtype.ext hjcr
      rw [hj, map_mul, map_mul]
      have hτc : τ (pi z ⟨c, hcJ⟩) = pi z ⟨c, hcJ⟩ := by
        rw [hτ, conjVA_pi_eq_iff hy.hA1]
        change t₁ * c * t₁⁻¹ * c⁻¹ ∈ zpowers z
        rw [htC c hc, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      have hτr : τ (pi z ⟨r, hrJ⟩) = pi z ⟨r, hrJ⟩ := by
        have hmem : pi z ⟨r, hrJ⟩ ∈ F := by rw [hFB]; exact pi_mem_imV hr
        exact hmem.2
      rw [hτc, hτr]
    have ht₁J' : t₁ ∈ J z := hy.mem_J_of_conjVA_eq_one D hs1 (y := tH) hall
    have httJ : ((tHP D : ↥(H z)) : G) ∈ J z := by
      have e : ((tHP D : ↥(H z)) : G) = t₁ * (((tHP D : ↥(H z)) : G)⁻¹ * t₁)⁻¹ := by group
      rw [e]
      exact (J z).mul_mem ht₁J' ((J z).inv_mem ht₁J)
    have hq : qHP D (tHP D) = 1 := by
      have hk : tHP D ∈ (qHP D).ker := by
        rw [ker_qHP]
        exact Subgroup.mem_subgroupOf.mpr httJ
      exact hk
    rw [qHP_tHP] at hq
    exact t_ne_one (congrArg Subtype.val hq)
  have hle : Nat.card F ≤ 4 := by
    have hdvd' : Nat.card F ∣ 2 ^ 4 := by norm_num; exact hdvd
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hm : Nat.card F % 3 = 1 := by simpa [Nat.ModEq] using hmod
    rw [hkeq] at hm hne ⊢
    have arith : ∀ k : ℕ, k ≤ 4 → 2 ^ k % 3 = 1 → 2 ^ k ≠ 16 → 2 ^ k ≤ 4 := by decide
    exact arith k hk hm hne
  calc Nat.card F ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hle 2
    _ = Nat.card B := by rw [hB]

theorem free_of_t1 (hs1 : s1 = ((s1HP D : ↥(H z)) : G)) {t₁ : G} (ht₁H : t₁ ∈ H z)
    (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z) (hts1 : t₁ * s1 = s1 * t₁)
    (hts : t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁)
    (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁) (ht2 : t₁ * t₁ ∈ zpowers z) :
    ∀ v ∈ imV z hy.R, conjVA z (⟨t₁, ht₁H⟩ : ↥(H z)) v = v →
      ∃ w ∈ imV z hy.R, v = conjVA z (⟨t₁, ht₁H⟩ : ↥(H z)) w * w := by
  set tH : ↥(H z) := ⟨t₁, ht₁H⟩ with htH
  have hτB : ∀ v, conjVA z tH v ∈ imV z hy.R ↔ v ∈ imV z hy.R :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R tH (mem_commutator_conj_iff ht₁H hts)
  have htt : tH * tH ∈ (J z).subgroupOf (H z) := by
    rw [Subgroup.mem_subgroupOf]
    exact hy.zpowers_le_J ht2
  have hτ2 : ∀ v ∈ imV z hy.R, conjVA z tH (conjVA z tH v) = v := by
    intro v _
    have h := conjVA_apply_of_mem_J hy.hA1 (g := tH * tH) (Subgroup.mem_subgroupOf.mp htt) v
    rwa [map_mul, MulAut.mul_apply] at h
  exact exists_eq_mul_of_card_fix_sq_le (V_comm hy.hA1) (imV z hy.R) (conjVA z tH) hτB hτ2
    (fun v _ => V_sq hy.hA1 v) (hy.card_fixIn_t1_sq_le D hs1 ht₁H ht₁J hts1 htC)

end Faithful

theorem exists_mul_of_mem_CJs {c : G} (hc : c ∈ CJ z (s1 * s2⁻¹)) :
    ∃ a ∈ CJ z s1, ∃ q ∈ hy.Q, c = a * q := by
  have hn : hy.Q ≤ Subgroup.normalizer (CJ z s1 : Set G) :=
    le_normalizer_of_commute fun q hq a ha => (hy.commute_J0_Q a ha q hq).symm
  rw [hy.CJs_eq_sup, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hc
  obtain ⟨a, ha, q, hq, rfl⟩ := hc
  exact ⟨a, ha, q, hq, rfl⟩

theorem commute_of_mem_CJs_of_t1 {t₁ : G} (ht₁H : t₁ ∈ H z) (hts1 : t₁ * s1 = s1 * t₁)
    (hts2 : t₁ * s2 = s2 * t₁) (htJ0 : ∀ a ∈ CJ z s1, t₁ * a = a * t₁)
    (ht2 : t₁ * t₁ ∈ zpowers z) : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁ := by
  have hts2' : t₁ * s2⁻¹ = s2⁻¹ * t₁ := by
    calc t₁ * s2⁻¹ = s2⁻¹ * (s2 * t₁) * s2⁻¹ := by group
      _ = s2⁻¹ * (t₁ * s2) * s2⁻¹ := by rw [hts2]
      _ = s2⁻¹ * t₁ := by group
  have hts : t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁ := by
    calc t₁ * (s1 * s2⁻¹) = (t₁ * s1) * s2⁻¹ := by group
      _ = (s1 * t₁) * s2⁻¹ := by rw [hts1]
      _ = s1 * (t₁ * s2⁻¹) := by group
      _ = s1 * (s2⁻¹ * t₁) := by rw [hts2']
      _ = (s1 * s2⁻¹) * t₁ := by group
  have hQ : ∀ a : G, a ∈ hy.Q ↔ t₁ * a * t₁⁻¹ ∈ hy.Q := by
    intro a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_CJ_conj_iff ht₁H hts a).mp h1, (mem_commutator_conj_iff ht₁H hts1 a).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_CJ_conj_iff ht₁H hts a).mpr h1, (mem_commutator_conj_iff ht₁H hts1 a).mpr h2⟩
  have h4 : t₁ ^ 2 ^ 2 = 1 := by
    have hsq : (t₁ * t₁) * (t₁ * t₁) = 1 := by
      rcases hy.mem_zpowers_z_iff.mp ht2 with h1 | h1
      · rw [h1, one_mul]
      · rw [h1, hy.z_sq]
    calc t₁ ^ 2 ^ 2 = (t₁ * t₁) * (t₁ * t₁) := by
          rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := hsq
  have hbs : ∀ q ∈ hy.Q, t₁ * (s1 * q * s1⁻¹) * t₁⁻¹ = s1 * (t₁ * q * t₁⁻¹) * s1⁻¹ := by
    intro q _
    have hts1' : t₁ * s1⁻¹ = s1⁻¹ * t₁ := by
      calc t₁ * s1⁻¹ = s1⁻¹ * (s1 * t₁) * s1⁻¹ := by group
        _ = s1⁻¹ * (t₁ * s1) * s1⁻¹ := by rw [hts1]
        _ = s1⁻¹ * t₁ := by group
    calc t₁ * (s1 * q * s1⁻¹) * t₁⁻¹ = (t₁ * s1) * q * (s1⁻¹ * t₁⁻¹) := by group
      _ = (s1 * t₁) * q * (s1⁻¹ * t₁⁻¹) := by rw [hts1]
      _ = s1 * t₁ * q * (t₁ * s1)⁻¹ := by group
      _ = s1 * t₁ * q * (s1 * t₁)⁻¹ := by rw [hts1]
      _ = s1 * (t₁ * q * t₁⁻¹) * s1⁻¹ := by group
  have hQc := hy.commute_of_mem_Q ht₁H hQ h4 hbs
  intro c hc
  obtain ⟨a, ha, q, hq, rfl⟩ := hy.exists_mul_of_mem_CJs hc
  calc t₁ * (a * q) = (t₁ * a) * q := by group
    _ = (a * t₁) * q := by rw [htJ0 a ha]
    _ = a * (t₁ * q) := by group
    _ = a * (q * t₁) := by rw [hQc q hq]
    _ = a * q * t₁ := by group

theorem exists_conj_mem_of_free {g : G} (hg : g ∈ H z)
    (hgC : ∀ c ∈ CJ z (s1 * s2⁻¹), g * c = c * g)
    (hgR : ∀ a : G, a ∈ hy.R ↔ g * a * g⁻¹ ∈ hy.R) (hg2 : g * g ∈ zpowers z)
    (hfree : ∀ v ∈ imV z hy.R, conjVA z (⟨g, hg⟩ : ↥(H z)) v = v →
      ∃ w ∈ imV z hy.R, v = conjVA z (⟨g, hg⟩ : ↥(H z)) w * w)
    {x : G} (hx : ∃ j ∈ J z, x = g * j) (hx2 : x * x = 1) :
    ∃ h ∈ hy.R, ∃ c ∈ CJ z (s1 * s2⁻¹), h * x * h⁻¹ = g * c := by
  obtain ⟨j, hj, rfl⟩ := hx
  obtain ⟨c, hc, r, hr, rfl⟩ := hy.exists_mul_of_mem_J hj
  have hcJ : c ∈ J z := (CJ_le_J _) hc
  have hrJ : r ∈ J z := hy.R_le_J hr
  set r' := g * r * g⁻¹ with hr'
  have hr'R : r' ∈ hy.R := (hgR r).mp hr
  have hr'J : r' ∈ J z := hy.R_le_J hr'R
  have hg2c : ∀ y ∈ H z, (g * g) * y = y * (g * g) := fun y hy' =>
    (hy.commute_of_mem_zpowers_of_mem_H hy' hg2).symm
  have hcr' : c * r' = r' * c := hy.commute_CJs_R c hc r' hr'R
  have hxx : g * (c * r) * (g * (c * r)) = (c * c) * (r' * r) * (g * g) := by
    calc g * (c * r) * (g * (c * r)) = (g * c) * r * g * c * r := by group
      _ = (c * g) * r * g * c * r := by rw [hgC c hc]
      _ = c * r' * ((g * g) * c) * r := by rw [hr']; group
      _ = c * r' * (c * (g * g)) * r := by rw [hg2c c (J_le_H hcJ)]
      _ = c * (r' * c) * ((g * g) * r) := by group
      _ = c * (c * r') * (r * (g * g)) := by rw [← hcr', hg2c r (J_le_H hrJ)]
      _ = (c * c) * (r' * r) * (g * g) := by group
  have hrr : r' * r ∈ zpowers z := by
    have e : r' * r = (c * c)⁻¹ * (g * g)⁻¹ := by
      have h1 : (c * c) * (r' * r) * (g * g) = 1 := hxx ▸ hx2
      calc r' * r = (c * c)⁻¹ * ((c * c) * (r' * r) * (g * g)) * (g * g)⁻¹ := by group
        _ = (c * c)⁻¹ * (g * g)⁻¹ := by rw [h1]; group
    rw [e]
    exact (zpowers z).mul_mem ((zpowers z).inv_mem (hy.sq_mem hcJ)) ((zpowers z).inv_mem hg2)
  set gH : ↥(H z) := ⟨g, hg⟩
  have hfix : conjVA z gH (pi z ⟨r, hrJ⟩) = pi z ⟨r, hrJ⟩ := by
    rw [conjVA_pi_eq_iff hy.hA1]
    have e : g * r * g⁻¹ * r⁻¹ = (r' * r) * (r * r)⁻¹ := by rw [hr']; group
    change g * r * g⁻¹ * r⁻¹ ∈ zpowers z
    rw [e]
    exact (zpowers z).mul_mem hrr ((zpowers z).inv_mem (hy.sq_mem hrJ))
  obtain ⟨w, hw, hvw⟩ := hfree _ (pi_mem_imV hr) hfix
  obtain ⟨v₀, hv₀, rfl⟩ := mem_imV.mp hw
  have hv₀J : (v₀ : G) ∈ J z := v₀.2
  set w₀ := g * (v₀ : G) * g⁻¹ with hw₀
  have hw₀R : w₀ ∈ hy.R := (hgR v₀).mp hv₀
  have hw₀J : w₀ ∈ J z := hy.R_le_J hw₀R
  have he : r⁻¹ * (w₀ * v₀) ∈ zpowers z := by
    rw [conjVA_pi, ← map_mul] at hvw
    exact (pi_eq_pi_iff hy.hA1).mp hvw
  refine ⟨w₀, hw₀R, c * (v₀ * r * w₀⁻¹), (CJ z (s1 * s2⁻¹)).mul_mem hc ?_, ?_⟩
  ·
    apply hy.zpowers_le_CJs
    set e := r⁻¹ * (w₀ * v₀) with he_def
    have hr_eq : r = w₀ * v₀ * e⁻¹ := by rw [he_def]; group
    set k := w₀ * v₀ * w₀⁻¹ * (v₀ : G)⁻¹ with hk_def
    have hk : k ∈ zpowers z := hy.comm_mem hw₀J hv₀J
    have hkv : (v₀ : G) * k = k * v₀ := (hy.commute_of_mem_zpowers_of_mem_H (J_le_H hv₀J) hk)
    have hev : ∀ y ∈ H z, y * e⁻¹ = e⁻¹ * y := fun y hy' =>
      hy.commute_of_mem_zpowers_of_mem_H hy' ((zpowers z).inv_mem he)
    have e1 : (v₀ : G) * r * w₀⁻¹ = k * ((v₀ : G) * v₀) * e⁻¹ := by
      rw [hr_eq]
      calc (v₀ : G) * (w₀ * v₀ * e⁻¹) * w₀⁻¹ = (v₀ : G) * (w₀ * v₀) * (e⁻¹ * w₀⁻¹) := by group
        _ = (v₀ : G) * (w₀ * v₀) * (w₀⁻¹ * e⁻¹) := by
          rw [hev w₀⁻¹ ((H z).inv_mem (J_le_H hw₀J))]
        _ = (v₀ : G) * (w₀ * v₀ * w₀⁻¹ * (v₀ : G)⁻¹) * v₀ * e⁻¹ := by group
        _ = ((v₀ : G) * k) * v₀ * e⁻¹ := by rw [hk_def]
        _ = (k * v₀) * v₀ * e⁻¹ := by rw [hkv]
        _ = k * ((v₀ : G) * v₀) * e⁻¹ := by group
    rw [e1]
    exact (zpowers z).mul_mem ((zpowers z).mul_mem hk (hy.sq_mem hv₀J))
      ((zpowers z).inv_mem he)
  ·
    have hv₀c : (v₀ : G) * c = c * v₀ := (hy.commute_CJs_R c hc v₀ hv₀).symm
    calc w₀ * (g * (c * r)) * w₀⁻¹ = g * (g⁻¹ * w₀ * g) * c * r * w₀⁻¹ := by group
      _ = g * (v₀ : G) * c * r * w₀⁻¹ := by rw [hw₀]; group
      _ = g * ((v₀ : G) * c) * r * w₀⁻¹ := by group
      _ = g * (c * v₀) * r * w₀⁻¹ := by rw [hv₀c]
      _ = g * (c * ((v₀ : G) * r * w₀⁻¹)) := by group

end Hyp

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
