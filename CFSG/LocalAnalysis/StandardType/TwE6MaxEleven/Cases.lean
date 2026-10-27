module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Local
public import CFSG.GH74.GLS.Balance.Bender.T59
public import Mathlib.GroupTheory.IsPerfect
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GH74.GLS.Balance.Bender.AuxSylow
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.StandardType.TwE6MaxEleven

open Subgroup CFSG.Assembly

variable {X : Type} [Group X] [Finite X]

private theorem eq_bot_of_perfect_of_solvable {G : Type*} [Group G] {H : Subgroup G}
    (hperf : ⁅H, H⁆ = H) (hsolv : Group.IsSolvable ↥H) : H = ⊥ := by
  by_contra hne
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable ↥H hsolv

private theorem orderOf_mul_eq_thirtyThree {y t : X} (hy : orderOf y = 3) (ht : orderOf t = 11)
    (hyt : Commute y t) : orderOf (y * t) = 33 := by
  rw [hyt.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hy, ht]; norm_num), hy, ht]

private theorem mem_of_three_pow_nine_dvd (hX : LocalFacts X) {M N : Subgroup X} {y : X}
    (hyM : y ∈ M) (hy : orderOf y = 3) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set X))
    (h39 : 3 ^ 9 ∣ Nat.card N) : y ∈ N := by
  by_contra hyN
  have hdisj : zpowers y ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxY, hxN⟩ := Subgroup.mem_inf.mp hx
    by_contra hx1
    have hxord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := by
        simpa [hy] using orderOf_dvd_of_mem_zpowers hxY
      exact (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) _ hdvd).resolve_left
        (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hle : zpowers x ≤ zpowers y := Subgroup.zpowers_le.mpr hxY
    have heq : zpowers x = zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hy])
    exact hyN (Subgroup.zpowers_le.mpr hxN (heq.symm ▸ Subgroup.mem_zpowers y))
  have hleN : zpowers y ≤ normalizer (N : Set X) :=
    (Subgroup.zpowers_le.mpr hyM).trans hMN
  have hform :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (G := X) (H := zpowers y) (K := N) hleN
  rw [hdisj, Subgroup.card_bot, Nat.card_zpowers, hy, mul_one] at hform
  have hform' : Nat.card (N ⊔ zpowers y : Subgroup X) = 3 * Nat.card N := by
    rw [sup_comm]
    simpa using hform
  have h310 : 3 ^ 10 ∣ Nat.card (N ⊔ zpowers y : Subgroup X) := by
    rw [hform', pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 3 h39
  have hX310 : 3 ^ 10 ∣ Nat.card X :=
    h310.trans (Subgroup.card_subgroup_dvd_card _)
  rw [hX.card] at hX310
  norm_num at hX310

private def conjAut {M N : Subgroup X} (hMN : M ≤ normalizer (N : Set X)) {y : X} (hyM : y ∈ M) :
    MulAut N where
  toFun n := ⟨y * n * y⁻¹, (Subgroup.mem_set_normalizer_iff.mp (hMN hyM) n).mp n.2⟩
  invFun n := ⟨y⁻¹ * n * y, (Subgroup.mem_set_normalizer_iff''.mp (hMN hyM) n).mp n.2⟩
  left_inv n := by
    ext
    simp [mul_assoc]
  right_inv n := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

private theorem coe_conjAut {M N : Subgroup X} (hMN : M ≤ normalizer (N : Set X)) {y : X}
    (hyM : y ∈ M) (n : N) : ((conjAut hMN hyM n : N) : X) = y * n * y⁻¹ := rfl

private theorem mem_of_suz (hSp : SporadicFacts) {M N : Subgroup X} {y : X} (hyM : y ∈ M)
    (hy : orderOf y = 3) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set X))
    (hcent : ∀ g ∈ M, (∀ n ∈ N, g * n = n * g) → g = 1)
    (e : N ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz) : y ∈ N := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  let σ : MulAut N := conjAut hMN hyM
  let σ' : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .Suz) := (e.symm.trans σ).trans e
  have hσ' : ∀ x, σ' x = e (σ (e.symm x)) := fun x => rfl
  have hσ3 : σ' ^ 3 = 1 := by
    ext x
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply,
      hσ', hσ', hσ', MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    conv_rhs => rw [← e.apply_symm_apply x]
    congr 1
    ext
    rw [coe_conjAut, coe_conjAut, coe_conjAut]
    have : y * (y * (y * (e.symm x : X) * y⁻¹) * y⁻¹) * y⁻¹ =
        y * y * y * (e.symm x : X) * (y * y * y)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [this, ← pow_three', hy3, one_mul, inv_one, mul_one]
  obtain ⟨c, hc⟩ := hSp.2.2.2 σ' hσ3
  let n₀ : N := e.symm c
  have hconj : ∀ m : N, y * (m : X) * y⁻¹ = (n₀ : X) * m * (n₀ : X)⁻¹ := by
    intro m
    have h1 : σ m = e.symm (σ' (e m)) := by rw [hσ', MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply]
    rw [hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun z : N => (z : X)) h1
    simpa [σ, coe_conjAut, n₀] using h2
  have hg : (n₀ : X)⁻¹ * y = 1 := by
    refine hcent _ (M.mul_mem (M.inv_mem (hNM n₀.2)) hyM) ?_
    intro m hm
    have h := hconj ⟨m, hm⟩
    simp only at h
    calc (n₀ : X)⁻¹ * y * m = (n₀ : X)⁻¹ * (y * m * y⁻¹) * y := by group
      _ = (n₀ : X)⁻¹ * ((n₀ : X) * m * (n₀ : X)⁻¹) * y := by rw [h]
      _ = m * ((n₀ : X)⁻¹ * y) := by group
  have hyn : y = n₀ := by
    rw [inv_mul_eq_one] at hg
    exact hg.symm
  rw [hyn]
  exact n₀.2

theorem maxElevenB_of_simple (hSp : SporadicFacts) (hE : ElevenSimpleCases) (hX : LocalFacts X)
    {M N : Subgroup X} (hM : IsCoatom M) (hd : 3 ^ 7 ∣ Nat.card M) {y t : X} (hyM : y ∈ M)
    (hy : orderOf y = 3) (ht : orderOf t = 11) (hyt : Commute y t) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set X)) (hNs : IsSimpleGroup N)
    (hNab : ∃ a b : N, a * b ≠ b * a) (htN : t ∈ N)
    (hcent : ∀ g ∈ M, (∀ n ∈ N, g * n = n * g) → g = 1) (hcat : InCatalog N) :
    ∃ N' : Subgroup X, N' ≤ M ∧ Nat.card N' = 9196830720 ∧
      ∀ P : Subgroup X, P ≤ M → ⁅P, P⁆ = P → P ≤ N' := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI := hNs
  have hN_card_dvd_X : Nat.card N ∣ 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
    rw [← hX.card]
    exact Subgroup.card_subgroup_dvd_card N
  have hN_card_lt_X : Nat.card N < 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
    rw [← hX.card]
    have hN_lt_top : N < ⊤ := lt_of_le_of_lt hNM (lt_top_iff_ne_top.mpr hM.1)
    simpa using Subgroup.card_lt_of_lt hN_lt_top
  have h11_dvd_N : 11 ∣ Nat.card N := by
    have h := Subgroup.orderOf_dvd_natCard N htN
    rwa [ht] at h
  have hN_ne_zero : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h11_sq_not_dvd_N : ¬ 11 ^ 2 ∣ Nat.card N := by
    intro h
    have h2 : 11 ^ 2 ∣ 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
      h.trans hN_card_dvd_X
    norm_num at h2
  have h11_factorization_N : (Nat.card N).factorization 11 = 1 := by
    have hpos : 0 < (Nat.card N).factorization 11 := by
      apply Nat.Prime.factorization_pos_of_dvd (by norm_num) hN_ne_zero h11_dvd_N
    have hle : (Nat.card N).factorization 11 ≤ 1 := by
      have h2 : ¬ 2 ≤ (Nat.card N).factorization 11 := by
        rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 11) (k := 2) (n := Nat.card N)
          (by norm_num) hN_ne_zero]
        exact h11_sq_not_dvd_N
      omega
    omega
  have hR_card : Nat.card (zpowers t) = 11 := by
    rw [Nat.card_zpowers, ht]
  have hR : Nat.card (zpowers t) = 11 ^ (Nat.card N).factorization 11 := by
    rw [hR_card, h11_factorization_N, pow_one]
  have hRN : zpowers t ≤ N := by
    rw [zpowers_le]
    exact htN
  rcases hE N hcat hNab hN_card_dvd_X hN_card_lt_X h11_dvd_N with h3 | hU6 | hO10 | hSuz | hFi22
  ·
    exfalso
    have hM_dvd := card_dvd_card_mul_card_normalizer hNM hMN hRN hR
    have hnormalizer_dvd : Nat.card (normalizer (zpowers t : Set X)) ∣ 660 :=
      card_normalizer_zpowers_eleven_dvd hX ht
    have hM_dvd_660 : Nat.card M ∣ Nat.card N * 660 := by
      exact hM_dvd.trans (Nat.mul_dvd_mul_left (Nat.card N) hnormalizer_dvd)
    have h37_dvd_N660 : 3 ^ 7 ∣ Nat.card N * 660 := hd.trans hM_dvd_660
    have h660 : 660 = 2 ^ 2 * 3 * 5 * 11 := by norm_num
    rw [h660] at h37_dvd_N660
    have h1 : 3 ^ 7 = 3 * 3 ^ 6 := by norm_num
    rw [h1] at h37_dvd_N660
    have h2 : Nat.card N * (2 ^ 2 * 3 * 5 * 11) = 3 * (Nat.card N * (2 ^ 2 * 5 * 11)) := by ring
    rw [h2] at h37_dvd_N660
    have h3_6_dvd : 3 ^ 6 ∣ Nat.card N * (2 ^ 2 * 5 * 11) := by
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h37_dvd_N660
    have hcop : Nat.Coprime (3 ^ 6) (2 ^ 2 * 5 * 11) := by norm_num
    have h36_dvd_N : 3 ^ 6 ∣ Nat.card N := hcop.dvd_mul_right.mp h3_6_dvd
    exact h3 h36_dvd_N
  ·
    refine ⟨N, hNM, hU6, ?_⟩
    intro P hPM hP
    have hNn : (N.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
    have hR_sylow : CFSG.GH74.GLS.Balance.IsSylowIn 11 (zpowers t) N := by
      refine ⟨hRN, ?_, ?_⟩
      · rw [IsPGroup.iff_card]
        exact ⟨1, by rw [hR_card, pow_one]⟩
      · intro S hSN hS
        have hS_dvd : Nat.card S ∣ Nat.card N := Subgroup.card_dvd_of_le hSN
        rw [IsPGroup.iff_card] at hS
        obtain ⟨k, hk⟩ := hS
        have hk_le : k ≤ 1 := by
          by_contra hk_gt
          have hk_ge : 2 ≤ k := by omega
          have hdvd : 11 ^ 2 ∣ Nat.card S := by
            rw [hk]
            exact pow_dvd_pow 11 hk_ge
          exact h11_sq_not_dvd_N (dvd_trans hdvd hS_dvd)
        rw [hk, hR_card]
        exact pow_le_pow_right₀ (by norm_num) hk_le
    have hfr := CFSG.GH74.GLS.Balance.t59_frattini (p := 11) (X := M) (N := N)
      (P := zpowers t) hNM hNn hR_sylow
    let K : Subgroup X := M ⊓ normalizer (zpowers t : Set X)
    have hK_le_M : K ≤ M := inf_le_left
    have hK_le_norm : K ≤ normalizer (zpowers t : Set X) := inf_le_right
    have hK_solvable : Group.IsSolvable K := by
      haveI : Group.IsSolvable (normalizer (zpowers t : Set X)) :=
        isSolvable_normalizer_zpowers_eleven hX ht
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK_le_norm)
    let f : K →* (M ⧸ N.subgroupOf M) :=
      (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hK_le_M)
    have hf_surj : Function.Surjective f := by
      intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf M) q
      have hm_sup : (m : X) ∈ ((K ⊔ N : Subgroup X) : Set X) := by
        rw [sup_comm]
        exact hfr m.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K N (hK_le_M.trans hMN)] at hm_sup
      obtain ⟨k, hk, n, hn, hkn⟩ := hm_sup
      refine ⟨⟨k, hk⟩, ?_⟩
      have hm_eq : m = ⟨k, hK_le_M hk⟩ * ⟨n, hNM hn⟩ := Subtype.ext hkn.symm
      rw [hm_eq, map_mul]
      have hn_ker : QuotientGroup.mk' (N.subgroupOf M) ⟨n, hNM hn⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hn
      rw [hn_ker, mul_one]
      rfl
    have hM_N_solvable : Group.IsSolvable (M ⧸ N.subgroupOf M) :=
      Group.isSolvable_of_surjective hf_surj
    have hPN : P ≤ N := by
      let fP : P →* (M ⧸ N.subgroupOf M) :=
        (QuotientGroup.mk' (N.subgroupOf M)).comp (Subgroup.inclusion hPM)
      let P' : Subgroup (M ⧸ N.subgroupOf M) := (⊤ : Subgroup P).map fP
      have hP'_perfect : ⁅P', P'⁆ = P' := by
        have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
        have : Group.IsPerfect P' := Group.IsPerfect.map fP
        exact Subgroup.commutator_eq_self
      have hP'_solvable : Group.IsSolvable P' := inferInstance
      have hP'_bot : P' = ⊥ := eq_bot_of_perfect_of_solvable hP'_perfect hP'_solvable
      intro p hp
      have hpM : p ∈ M := hPM hp
      have hpP' : fP (⟨p, hp⟩ : P) ∈ P' :=
        Subgroup.mem_map_of_mem fP (Subgroup.mem_top (⟨p, hp⟩ : P))
      rw [hP'_bot, Subgroup.mem_bot] at hpP'
      simp only [fP, MonoidHom.comp_apply, Subgroup.coe_inclusion, QuotientGroup.mk'_apply] at hpP'
      have hpN_M : (⟨p, hpM⟩ : M) ∈ N.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hpP'
      exact Subgroup.mem_subgroupOf.mp hpN_M
    exact hPN
  ·
    exfalso
    haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    have h17_dvd_N : 17 ∣ Nat.card N := by
      rw [hO10]
      norm_num
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := N) 17 h17_dvd_N
    have hs_X : orderOf (s : X) = 17 := by rwa [orderOf_coe]
    have hsN : (s : X) ∈ N := s.2
    have hS_card : Nat.card (zpowers (s : X)) = 17 := by
      rw [Nat.card_zpowers, hs_X]
    have h17_factorization_N : (Nat.card N).factorization 17 = 1 := by
      have hpos : 0 < (Nat.card N).factorization 17 := by
        apply Nat.Prime.factorization_pos_of_dvd (by norm_num) hN_ne_zero h17_dvd_N
      have hnot : ¬ 17 ^ 2 ∣ Nat.card N := by
        intro h
        have h2 : 17 ^ 2 ∣ 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 :=
          h.trans hN_card_dvd_X
        norm_num at h2
      have hle : (Nat.card N).factorization 17 ≤ 1 := by
        have h2 : ¬ 2 ≤ (Nat.card N).factorization 17 := by
          rw [← Nat.Prime.pow_dvd_iff_le_factorization (p := 17) (k := 2) (n := Nat.card N)
            (by norm_num) hN_ne_zero]
          exact hnot
        omega
      omega
    have hS : Nat.card (zpowers (s : X)) = 17 ^ (Nat.card N).factorization 17 := by
      rw [hS_card, h17_factorization_N, pow_one]
    have hSN : zpowers (s : X) ≤ N := by
      rw [zpowers_le]
      exact hsN
    have hM_dvd := card_dvd_card_mul_card_normalizer hNM hMN hSN hS
    have hnormalizer_dvd : Nat.card (normalizer (zpowers (s : X) : Set X)) ∣ 272 :=
      card_normalizer_zpowers_seventeen_dvd hX hs_X
    have hM_dvd_272 : Nat.card M ∣ Nat.card N * 272 := by
      exact hM_dvd.trans (Nat.mul_dvd_mul_left (Nat.card N) hnormalizer_dvd)
    have h37_dvd_N272 : 3 ^ 7 ∣ Nat.card N * 272 := hd.trans hM_dvd_272
    rw [hO10] at h37_dvd_N272
    norm_num at h37_dvd_N272
  ·
    exfalso
    obtain ⟨e⟩ := hSuz
    have hyN : y ∈ N := mem_of_suz hSp hyM hy hNM hMN hcent e
    exact hSp.2.2.1 (e ⟨y * t, N.mul_mem hyN htN⟩) (by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_mul_eq_thirtyThree hy ht hyt])
  ·
    exfalso
    obtain ⟨e⟩ := hFi22
    have hcardN : Nat.card N = 64561751654400 := (Nat.card_congr e.toEquiv).trans hSp.1
    have hyN : y ∈ N := mem_of_three_pow_nine_dvd hX hyM hy hNM hMN (by rw [hcardN]; norm_num)
    exact hSp.2.1 (e ⟨y * t, N.mul_mem hyN htN⟩) (by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_mul_eq_thirtyThree hy ht hyt])

end CFSG.StandardType.TwE6MaxEleven
