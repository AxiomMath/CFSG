module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFourOrestLK
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_pow_mul_eq_of_pow_eq_one_19 {p q : G} (hp : p * p = 1) (hq : q * q = 1)
    {N e : ℕ} (hN : (p * q) ^ N = 1) (he : 2 * e = N + 1) :
    ((p * q) ^ e)⁻¹ * p * (p * q) ^ e = q := by
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have h1 : p⁻¹ * (p * q) * p = (p * q)⁻¹ := by
    calc p⁻¹ * (p * q) * p = q * p := by group
      _ = q⁻¹ * p⁻¹ := by rw [hqinv, hpinv]
      _ = (p * q)⁻¹ := (mul_inv_rev p q).symm
  have h2 : p⁻¹ * (p * q) ^ e * p = ((p * q) ^ e)⁻¹ := by
    have h := conj_pow (a := p⁻¹) (b := p * q) (i := e)
    rw [inv_inv] at h
    rw [← h, h1, inv_pow]
  have h4 : (p * q) ^ e * (p * q) ^ e = p * q := by
    rw [← pow_add, show e + e = N + 1 by omega, pow_succ, hN, one_mul]
  calc ((p * q) ^ e)⁻¹ * p * (p * q) ^ e
      = p * (p⁻¹ * (p * q) ^ e * p)⁻¹ * (p * q) ^ e := by group
    _ = p * ((p * q) ^ e * (p * q) ^ e) := by rw [h2, inv_inv, mul_assoc]
    _ = q := by rw [h4, ← mul_assoc, hp, one_mul]

theorem false_of_commutator_mem_pCoreOf_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M)
    {H A : Subgroup G} (hHM : H ≤ D.M) (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAM : ¬ A ≤ pCoreOf 2 D.M) (hAH : A ≤ H)
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 H)) ≠ ⊥)
    {v x : G} (hv : v ∈ A) (hvQ : v ∉ pCoreOf 2 H) (hxH : x ∈ H)
    (hxQ : x ∉ pCoreOf 2 H) (hx5 : x ^ 5 ∈ pCoreOf 2 H)
    (hvx : v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub (by omega)
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := S17.hyp125_isTI h hne
  have hV : IsElemAbelian 2 V₀ := h.pairFacts.elemAbelian₀
  have hVp : IsPGroup 2 ↥V₀ := hV.isPGroup
  obtain ⟨-, g, hAg, hmq⟩ := E3.mem_gammaSet_iff.mp hA
  have hVg : IsPGroup 2 ↥(conjSubgroup V₀ g) := E3.isPGroup_conjSubgroup hVp g
  have hAeq : A = conjSubgroup V₀ g := (E3.mQuot_eq_zero_iff hVg hAg).mp hmq
  have hAp : IsPGroup 2 ↥A := hAeq.symm ▸ hVg
  have hAel : IsElemAbelian 2 A := by
    rw [hAeq]
    exact E3.isElemAbelian_conjSubgroup hV g
  have hinvA : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hAel.2 a ha
  have hQH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHQ : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQp : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hAO : ¬ A ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  have hv1 : v ≠ 1 := fun h1 => hvQ (h1 ▸ (pCoreOf 2 H).one_mem)
  have hvH : v ∈ H := hAH hv
  have hvv : v * v = 1 := hinvA v hv
  have hEab : IsMulCommutative ↥(centerOf (E3.wClos V₀ 2 (pCoreOf 2 H))) := by
    refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (mem_inf.mp hw).2 y (mem_inf.mp hy).1).symm
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp hZ
  have hzA : (z : G) ∈ A := (mem_inf.mp z.2).1
  have hzW : (z : G) ∈ E3.wClos V₀ 2 (pCoreOf 2 H) :=
    (mem_inf.mp (mem_inf.mp z.2).2).1
  have hzC : (z : G) ∈ centralizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G) :=
    (mem_inf.mp (mem_inf.mp z.2).2).2
  have hzne : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hΩ : ∀ y ∈ H,
      conjSubgroup A y ∈ omegaSet V₀ H (centerOf (E3.wClos V₀ 2 (pCoreOf 2 H))) := by
    intro y hyH
    have hyN : y ∈ normalizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G) :=
      E3.normalizer_le_normalizer_wClos (V := V₀) (i := 2) (pCoreOf 2 H) (hHQ hyH)
    have hzyW : y⁻¹ * (z : G) * y ∈ E3.wClos V₀ 2 (pCoreOf 2 H) := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) (z : G)).mp hzW
    have hzyC : y⁻¹ * (z : G) * y ∈
        centralizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G) := by
      have hCy : conjSubgroup (centralizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G)) y =
          centralizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G) := by
        rw [E3.conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.mpr hyN]
      have hmem : y⁻¹ * (z : G) * y ∈
          conjSubgroup (centralizer (E3.wClos V₀ 2 (pCoreOf 2 H) : Set G)) y := by
        rw [mem_conjSubgroup_iff]
        simpa [mul_assoc] using hzC
      rwa [hCy] at hmem
    have hzyA : y⁻¹ * (z : G) * y ∈ conjSubgroup A y := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hzA
    have hzyne : y⁻¹ * (z : G) * y ≠ 1 := by
      intro hh
      apply hzne
      have := congrArg (fun t => y * t * y⁻¹) hh
      simpa [mul_assoc] using this
    have hZ' : conjSubgroup A y ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 H)) ≠ ⊥ := by
      refine ne_bot_iff_exists_ne_one.mpr
        ⟨⟨y⁻¹ * (z : G) * y, mem_inf.mpr ⟨hzyA, mem_inf.mpr ⟨hzyW, hzyC⟩⟩⟩, ?_⟩
      exact fun hh => hzyne (congrArg Subtype.val hh)
    have hyO : y ∈ normalizer (pCoreOf 2 H : Set G) := hHQ hyH
    refine ⟨g * y, ?_, ?_, ?_⟩
    · rw [← conjSubgroup_conjSubgroup, hAeq]
    · rwa [inf_comm]
    · intro hle
      apply hAO
      have hconjO : conjSubgroup (pCoreOf 2 H) y⁻¹ = pCoreOf 2 H := by
        rw [conjSubgroup_eq_iff_mem_normalizer]
        simpa using inv_mem hyO
      have hAeqy : A = conjSubgroup (conjSubgroup A y) y⁻¹ := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [hAeqy]
      calc conjSubgroup (conjSubgroup A y) y⁻¹ ≤ conjSubgroup (pCoreOf 2 H) y⁻¹ :=
            E3.conjSubgroup_mono_left y⁻¹ hle
        _ = pCoreOf 2 H := hconjO
  have hAom : A ∈ omegaSet V₀ H (centerOf (E3.wClos V₀ 2 (pCoreOf 2 H))) := by
    simpa [conjSubgroup_one] using hΩ 1 H.one_mem
  obtain ⟨k, hkH, hk2⟩ : ∃ k ∈ H,
      ¬ IsPGroup 2 ↥(Subgroup.closure ({v, k * v * k⁻¹} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hvQ (mem_pCoreOf_of_forall_closure_isPGroup hvH hcon)
  have hwA : k * v * k⁻¹ ∈ conjSubgroup A k⁻¹ := by
    rw [mem_conjSubgroup_iff, show k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v by group]
    exact hv
  have hww : k * v * k⁻¹ * (k * v * k⁻¹) = 1 := by
    rw [show k * v * k⁻¹ * (k * v * k⁻¹) = k * (v * v) * k⁻¹ by group, hvv]
    group
  have hr : Odd (orderOf (v * (k * v * k⁻¹))) :=
    seven_three_A hV hTI hEab hAom (hΩ k⁻¹ (H.inv_mem hkH)) hv hwA hk2
  have huA : x * v * x⁻¹ ∈ conjSubgroup A x⁻¹ := by
    rw [mem_conjSubgroup_iff, show x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v by group]
    exact hv
  have huu : x * v * x⁻¹ * (x * v * x⁻¹) = 1 := by
    rw [show x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ by group, hvv]
    group
  have hwH : k * v * k⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hvH) (H.inv_mem hkH)
  have huH : x * v * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hvH) (H.inv_mem hxH)
  have hNn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHQ
  let π : H →* H ⧸ (pCoreOf 2 H).subgroupOf H := QuotientGroup.mk' _
  have hπ1 : ∀ a : H, π a = 1 ↔ (a : G) ∈ pCoreOf 2 H := by
    intro a
    simp only [π, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπeq : ∀ a b : H, π a = π b ↔ (a : G)⁻¹ * b ∈ pCoreOf 2 H := by
    intro a b
    simp only [π, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul, Subgroup.coe_inv]
  let vH : H := ⟨v, hvH⟩
  let wH : H := ⟨k * v * k⁻¹, hwH⟩
  let uH : H := ⟨x * v * x⁻¹, huH⟩
  let xH : H := ⟨x, hxH⟩
  have hπuv : π uH = π vH := by
    rw [hπeq]
    show (x * v * x⁻¹)⁻¹ * v ∈ pCoreOf 2 H
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hvH)) _).mp hvx
    rwa [show v⁻¹ * (v * x * v⁻¹ * x⁻¹) * v⁻¹⁻¹ = (x * v * x⁻¹)⁻¹ * v by group] at h1
  have hπrs : π (uH * wH) = π (vH * wH) := by rw [map_mul, map_mul, hπuv]
  have hnot' : ¬ IsPGroup 2 ↥(Subgroup.closure ({x * v * x⁻¹, k * v * k⁻¹} : Set G)) := by
    intro hp
    have hde : x * v * x⁻¹ * (k * v * k⁻¹) ∈
        Subgroup.closure ({x * v * x⁻¹, k * v * k⁻¹} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    have hs2 : orderOf (x * v * x⁻¹ * (k * v * k⁻¹)) ∣ 2 ^ n :=
      hn ▸ Subgroup.orderOf_dvd_natCard _ hde
    have hd1 : orderOf (π (vH * wH)) ∣ orderOf (v * (k * v * k⁻¹)) := by
      have h0 := orderOf_map_dvd π (vH * wH)
      rwa [← Subgroup.orderOf_coe] at h0
    have hd2 : orderOf (π (vH * wH)) ∣ 2 ^ n := by
      have h0 := orderOf_map_dvd π (uH * wH)
      rw [← Subgroup.orderOf_coe, hπrs] at h0
      exact h0.trans hs2
    have hodd : Odd (orderOf (π (vH * wH))) := Odd.of_dvd_nat hr hd1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff, hπ1] at hj
    have hrQ : v * (k * v * k⁻¹) ∈ pCoreOf 2 H := hj
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp hQp ⟨_, hrQ⟩
    rw [Subgroup.orderOf_mk] at hi
    have hi0 : i = 0 := by
      by_contra hi0
      rw [hi] at hr
      exact (Nat.not_even_iff_odd.mpr hr) ((Nat.even_pow' hi0).mpr even_two)
    rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
    have hwv : k * v * k⁻¹ = v := by
      calc k * v * k⁻¹ = v * v * (k * v * k⁻¹) := by rw [hvv, one_mul]
        _ = v * (v * (k * v * k⁻¹)) := by group
        _ = v := by rw [hi, mul_one]
    apply hk2
    refine hAp.to_le (Subgroup.closure_le A |>.mpr ?_)
    rintro y (rfl | rfl)
    · exact hv
    · show k * v * k⁻¹ ∈ A
      rw [hwv]
      exact hv
  have hs : Odd (orderOf (x * v * x⁻¹ * (k * v * k⁻¹))) :=
    seven_three_A hV hTI hEab (hΩ x⁻¹ (H.inv_mem hxH)) (hΩ k⁻¹ (H.inv_mem hkH)) huA hwA hnot'
  obtain ⟨t, ht⟩ := hr.mul hs
  have hN1 : (v * (k * v * k⁻¹)) ^ (orderOf (v * (k * v * k⁻¹)) *
      orderOf (x * v * x⁻¹ * (k * v * k⁻¹))) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hN2 : (x * v * x⁻¹ * (k * v * k⁻¹)) ^ (orderOf (v * (k * v * k⁻¹)) *
      orderOf (x * v * x⁻¹ * (k * v * k⁻¹))) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have he : 2 * (t + 1) = orderOf (v * (k * v * k⁻¹)) *
      orderOf (x * v * x⁻¹ * (k * v * k⁻¹)) + 1 := by
    rw [ht]; ring
  have hc1 := conj_pow_mul_eq_of_pow_eq_one_19 hvv hww hN1 he
  have hc2 := conj_pow_mul_eq_of_pow_eq_one_19 huu hww hN2 he
  let cH : H := (vH * wH) ^ (t + 1) * ((uH * wH) ^ (t + 1))⁻¹
  have hcG : (cH : G) = (v * (k * v * k⁻¹)) ^ (t + 1) *
      ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹ := by
    simp [cH, vH, wH, uH]
  have hcu : (cH : G)⁻¹ * v * cH = x * v * x⁻¹ := by
    rw [hcG]
    calc (((v * (k * v * k⁻¹)) ^ (t + 1) *
          ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹)⁻¹ * v *
          ((v * (k * v * k⁻¹)) ^ (t + 1) * ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹))
        = (x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1) *
            (((v * (k * v * k⁻¹)) ^ (t + 1))⁻¹ * v * (v * (k * v * k⁻¹)) ^ (t + 1)) *
            ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹ := by group
      _ = (x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1) * (k * v * k⁻¹) *
            ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹ := by rw [hc1]
      _ = (x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1) *
            (((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹ * (x * v * x⁻¹) *
              (x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1)) *
            ((x * v * x⁻¹ * (k * v * k⁻¹)) ^ (t + 1))⁻¹ := by rw [hc2]
      _ = x * v * x⁻¹ := by group
  have hπc : π cH = 1 := by
    simp only [cH, map_mul, map_pow, map_inv, hπrs, mul_inv_cancel]
  let nH : H := cH * xH
  have hnG : (nH : G) = (cH : G) * x := rfl
  have hncent : (nH : G) ∈ centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hnv : (nH : G) * v * (nH : G)⁻¹ = v := by
      rw [hnG]
      calc (cH : G) * x * v * ((cH : G) * x)⁻¹ = (cH : G) * (x * v * x⁻¹) * (cH : G)⁻¹ := by
            group
        _ = (cH : G) * ((cH : G)⁻¹ * v * cH) * (cH : G)⁻¹ := by rw [hcu]
        _ = v := by group
    calc v * (nH : G) = ((nH : G) * v * (nH : G)⁻¹) * (nH : G) := by rw [hnv]
      _ = (nH : G) * v := by group
  have hπn : π nH = π xH := by
    simp only [nH, map_mul, hπc, one_mul]
  have hπx5 : orderOf (π xH) = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hπ1]
      simpa [xH] using hx5
    · rw [Ne, hπ1]
      exact hxQ
  have h5n : 5 ∣ orderOf (nH : G) := by
    rw [Subgroup.orderOf_coe, ← hπx5, ← hπn]
    exact orderOf_map_dvd π nH
  have hgM : g ∉ D.M := by
    intro hg
    apply hAM
    have hV0 : conjSubgroup V₀ g = V₀ :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (h.pairFacts.le_normalizer₀ hg)
    rw [hAeq, hV0]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (h.pairFacts.le.trans h.pairFacts.le_M) h.pairFacts.le_normalizer₀ hVp
  have hvg : v ∈ conjSubgroup V₀ g := by rw [← hAeq]; exact hv
  have hXM : Subgroup.zpowers (nH : G) ≤ D.M := (Subgroup.zpowers_le).mpr (hHM nH.2)
  have hXN : Subgroup.zpowers (nH : G) ≤ normalizer (conjSubgroup V₀ g : Set G) :=
    (Subgroup.zpowers_le).mpr (centralizer_le_normalizer_conj hTI g hvg hv1 hncent)
  have h5 : 5 ∣ Nat.card ↥(Subgroup.zpowers (nH : G)) := by
    rw [Nat.card_zpowers]
    exact h5n
  exact not_le_normalizer_conj_of_five_dvd_19 h hm hsp hgM hXM h5 hXN

theorem false_of_commutator_mem_pCoreOf_of_orderOf_19 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hm : 4 < mSub V₀) (hsp : IsStronglyPEmbedded 5 D.M)
    {H A : Subgroup G} (hHM : H ≤ D.M) (hA : A ∈ E3.gammaSet V₀ 0 D.T)
    (hAM : ¬ A ≤ pCoreOf 2 D.M) (hAH : A ≤ H)
    (hZ : A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 H)) ≠ ⊥)
    {v x : G} (hv : v ∈ A) (hvQ : v ∉ pCoreOf 2 H) (hxH : x ∈ H)
    (hx5 : orderOf x = 5) (hvx : v * x * v⁻¹ * x⁻¹ ∈ pCoreOf 2 H) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxQ : x ∉ pCoreOf 2 H := by
    intro hxQ
    obtain ⟨i, hi⟩ := IsPGroup.iff_orderOf.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨x, hxQ⟩
    rw [Subgroup.orderOf_mk, hx5] at hi
    have h2 : 2 ∣ 5 := by
      rcases i with _ | i
      · norm_num at hi
      · exact ⟨2 ^ i, by rw [hi, pow_succ, mul_comm]⟩
    omega
  have hx5' : x ^ 5 ∈ pCoreOf 2 H := by
    rw [← hx5, pow_orderOf_eq_one]
    exact (pCoreOf 2 H).one_mem
  exact false_of_commutator_mem_pCoreOf_19 h hm hsp hHM hA hAM hAH hZ hv hvQ hxH hxQ hx5' hvx

theorem pCoreOf_le_pCoreOf_LKT_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K F : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hF : F = L ∨ F = K) :
    pCoreOf 2 F ≤ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hXM : L ⊔ K ⊔ D.T ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have hFc : F ∈ calC D.M := by rcases hF with rfl | rfl; exacts [h.hyp.hL.1, h.hK]
  have hFX : F ≤ L ⊔ K ⊔ D.T := by
    rcases hF with rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
  exact (le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 F).trans hFX)
    (UC22.P22s.pCoreOf_le_of_isSubnormal hFc.1)).trans
    (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXM)

theorem five_dvd_card_of_normal_LKT_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) {N : Subgroup G}
    (hNH : N ≤ L ⊔ K ⊔ D.T) (hHN : L ⊔ K ⊔ D.T ≤ normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 (L ⊔ K ⊔ D.T)) : 5 ∣ Nat.card N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5L : 5 ∣ Nat.card L := by
    have h1 := h.hyp.hL.2
    rw [h.p_eq] at h1
    exact h1.2
  have h5K : 5 ∣ Nat.card K := UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  have hO5 : ¬ 5 ∣ Nat.card (pCoreOf 2 (L ⊔ K)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ K))
    rw [hk]
    intro h5
    have h52 := Nat.prime_five.dvd_of_dvd_pow h5
    omega
  have hNO : N ⊓ (L ⊔ K) ≤ normalizer (pCoreOf 2 (L ⊔ K) : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ K))
  have hdvd :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      (pCoreOf 2 (L ⊔ K)) (N ⊓ (L ⊔ K)) hNO
  have hsup : 5 ∣ Nat.card (pCoreOf 2 (L ⊔ K) ⊔ (N ⊓ (L ⊔ K)) : Subgroup G) := by
    rw [sup_comm]
    rcases le_sup_pCoreOf_left_or_right_19 h hNH hHN hNQ with hL | hK
    · exact h5L.trans (Subgroup.card_dvd_of_le hL)
    · exact h5K.trans (Subgroup.card_dvd_of_le hK)
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 (hsup.trans hdvd) with h1 | h1
  · exact absurd h1 hO5
  · exact h1.trans (Subgroup.card_dvd_of_le inf_le_left)

theorem inf_centerOf_wClos_LKT_ne_bot_19 (D : Data G)
    (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hm : 4 < mSub V₀)
    (hN2 : ¬ normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hAM : ¬ A ≤ pCoreOf 2 D.M)
    (hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ K ⊔ D.T))
    (hq : E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ 2) :
    A ⊓ centerOf (E3.wClos V₀ 2 (pCoreOf 2 (L ⊔ K ⊔ D.T))) ≠ ⊥ := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hXle : L ⊔ K ⊔ D.T ≤ D.M := sup_le (sup_le hLM hKM) D.sylowM.le
  have h5sig : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hsp : IsStronglyPEmbedded 5 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1) h5sig
  have hTsyl : IsSylowIn 2 D.T (L ⊔ K ⊔ D.T) := TwelveShort.isSylowIn_of_le D le_sup_right
  have hQT : pCoreOf 2 (L ⊔ K ⊔ D.T) ≤ D.T :=
    CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow le_sup_right D.sylowM.isPGroup hTsyl.2.2
  exact inf_centerOf_wClos_two_ne_bot_19 h.hyp.hyp125 hm hsp hN2 hXle
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    hQT (hA.1.trans le_sup_right) hA hAM hAQ hq
    (fun x hx => Subgroup.mem_sup_right (Subgroup.mem_inf.mp hx).1)
    (fun N hNX hXN hNQ => five_dvd_card_of_normal_LKT_19 h hNX hXN hNQ)

theorem mQuot_LKT_le_add_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (hLN : (L.subgroupOf D.M).Normal) {A : Subgroup G}
    (hAT : A ≤ D.T) :
    E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤
      E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ D.T)) + E3.mQuot A (A ⊓ pCoreOf 2 (K ⊔ D.T)) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hKN : (K.subgroupOf D.M).Normal := normal_right_of_normal_left_19 h hLN
  have hTL : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
  have hTK : D.T ≤ normalizer (K : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKN)
  have hAp : IsPGroup 2 A := D.sylowM.isPGroup.to_le hAT
  have hle : (A ⊓ pCoreOf 2 (L ⊔ D.T)) ⊓ (A ⊓ pCoreOf 2 (K ⊔ D.T)) ≤
      A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨haA, haL⟩ := Subgroup.mem_inf.mp ha1
    obtain ⟨-, haK⟩ := Subgroup.mem_inf.mp ha2
    have haT : a ∈ D.T := hAT haA
    exact Subgroup.mem_inf.mpr ⟨haA, mem_pCoreOf_LKT_of_rhoL_eq_one_19 h haT (hTL haT) (hTK haT)
      (UC6S846.rhoL_eq_one_of_mem_pCoreOf le_sup_left (hTL haT) haL)
      (UC6S846.rhoL_eq_one_of_mem_pCoreOf le_sup_left (hTK haT) haK)⟩
  calc E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T))
      ≤ E3.mQuot A ((A ⊓ pCoreOf 2 (L ⊔ D.T)) ⊓ (A ⊓ pCoreOf 2 (K ⊔ D.T))) := E3.mQuot_mono hle
    _ ≤ _ := mQuot_inf_le_add hAp

theorem mQuot_LKT_le_of_trivial_19 {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hLN : (L.subgroupOf D.M).Normal)
    {A J F : Subgroup G} (hAT : A ≤ D.T) (hJF : (J = L ∧ F = K) ∨ (J = K ∧ F = L))
    (hFA : ⁅F, A⁆ ≤ pCoreOf 2 F) :
    E3.mQuot A (A ⊓ pCoreOf 2 (L ⊔ K ⊔ D.T)) ≤ E3.mQuot A (A ⊓ pCoreOf 2 (J ⊔ D.T)) := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hKN : (K.subgroupOf D.M).Normal := normal_right_of_normal_left_19 h hLN
  have hTL : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLN)
  have hTK : D.T ≤ normalizer (K : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKN)
  have hρF : ∀ a ∈ A, ∀ haF : a ∈ normalizer (F : Set G), UC6S846.rhoL F ⟨a, haF⟩ = 1 := by
    intro a haA haF
    apply MulEquiv.ext
    intro zbar
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥F) zbar
    rw [MulAut.one_apply]
    refine (UC6S846.rhoL_fix_iff F ⟨a, haF⟩ z).2 ?_
    have h1 : ⁅a, (z : G)⁆ ∈ ⁅A, F⁆ := Subgroup.commutator_mem_commutator haA z.2
    rw [Subgroup.commutator_comm] at h1
    have h2 := hFA h1
    rwa [commutatorElement_def] at h2
  apply E3.mQuot_mono
  intro a ha
  obtain ⟨haA, haQ⟩ := Subgroup.mem_inf.mp ha
  have haT : a ∈ D.T := hAT haA
  refine Subgroup.mem_inf.mpr ⟨haA, ?_⟩
  rcases hJF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mem_pCoreOf_LKT_of_rhoL_eq_one_19 h haT (hTL haT) (hTK haT)
      (UC6S846.rhoL_eq_one_of_mem_pCoreOf le_sup_left (hTL haT) haQ) (hρF a haA (hTK haT))
  · exact mem_pCoreOf_LKT_of_rhoL_eq_one_19 h haT (hTL haT) (hTK haT)
      (hρF a haA (hTL haT)) (UC6S846.rhoL_eq_one_of_mem_pCoreOf le_sup_left (hTK haT) haQ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
