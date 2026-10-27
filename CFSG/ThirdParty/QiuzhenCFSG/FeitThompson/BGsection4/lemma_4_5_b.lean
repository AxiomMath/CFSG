module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

import Mathlib.GroupTheory.IndexNormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Infrastructure
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative commutatorElement

section Main

public theorem CFSG.lemma_4_5_b {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (hncyc : ¬ IsCyclic R)
    (hindex : ∃ S : Subgroup R, IsCyclic S ∧ Nat.card (R ⧸ S) = p) :
    Nat.card (omega₁ (G := R) (p := p)) = p ^ 2 ∧
      IsElementaryAbelian p (omega₁ (G := R) (p := p)) := by
  classical
  let Ω : Subgroup R := omega₁ (G := R) (p := p)
  obtain ⟨S, hScyc, hSquot⟩ := hindex
  have hR_p : IsPGroup p R := Fact.out
  letI : IsCyclic S := hScyc
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hSidx : S.index = p := by simpa [Subgroup.index_eq_card] using hSquot
  obtain ⟨n, hnR⟩ := IsPGroup.iff_card.mp hR_p
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hR_card_one : Nat.card R = 1 := by simpa [hn0] using hnR
    letI : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hR_card_one).1
    exact hncyc (isCyclic_of_subsingleton (α := R))
  have hS_normal : S.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hSidx, hnR]
    simpa using ((Fact.out : Nat.Prime p).pow_minFac hn_ne_zero).symm
  letI : S.Normal := hS_normal
  obtain ⟨A, hA_normal, hAcard, hAelem⟩ := lemma_4_5_a (R := R) (p := p) hpodd hncyc
  letI : A.Normal := hA_normal
  let q : R →* R ⧸ S := QuotientGroup.mk' S
  have hA_le_Ω : A ≤ Ω := by
    intro a ha
    change a ∈ Subgroup.closure {x : R | x ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using elemPow_eq_one_of_isElementaryAbelian a ha
  have hA_not_le_S : ¬ A ≤ S := by
    intro hAS
    have hAcyc : IsCyclic A := Subgroup.isCyclic_of_le hAS
    have hAexp_dvd : Nat.card A ∣ p := by
      simpa [hAcyc.exponent_eq_card] using (IsElementaryAbelian.exponent_dvd_p p A)
    have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
    have hp_sq_not_dvd : ¬ p ^ 2 ∣ p :=
      Nat.not_dvd_of_pos_of_lt (Fact.out : Nat.Prime p).pos hp_lt_sq
    exact hp_sq_not_dvd (by simpa [hAcard] using hAexp_dvd)
  have hAmap_ne_bot : A.map q ≠ ⊥ := by
    intro hbot
    have hAleKer : A ≤ q.ker := (Subgroup.map_eq_bot_iff (H := A) (f := q)).mp hbot
    exact hA_not_le_S (by simpa [q, QuotientGroup.ker_mk'] using hAleKer)
  letI : Fact (Nat.card (R ⧸ S)).Prime := ⟨by simpa [hSquot] using (Fact.out : Nat.Prime p)⟩
  have hAmap_top : A.map q = ⊤ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (H := A.map q) with hbot | htop
    · exact False.elim (hAmap_ne_bot hbot)
    · exact htop
  let qA : A →* A.map q := q.subgroupMap A
  have hqA_surj : Function.Surjective qA := MonoidHom.subgroupMap_surjective q A
  have hqA_range_top : qA.range = ⊤ := by
    ext y
    constructor
    · intro _hy
      simp
    · intro _hy
      rcases hqA_surj y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hAquot_card : Nat.card (A ⧸ qA.ker) = Nat.card (A.map q) := by
    have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange qA).toEquiv
    simpa [hqA_range_top] using hcard
  have hAmap_card : Nat.card (A.map q) = p := by
    calc
      Nat.card (A.map q) = Nat.card (R ⧸ S) := by simp [hAmap_top]
      _ = p := hSquot
  let C0 : Subgroup A := S.subgroupOf A
  have hqA_ker : qA.ker = C0 := by
    simpa [qA, C0, q, QuotientGroup.ker_mk'] using (Subgroup.ker_subgroupMap (f := q) (H := A))
  have hA_card_expr : Nat.card A = Nat.card (A ⧸ qA.ker) * Nat.card qA.ker := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := qA.ker))
  have hC0_card : Nat.card C0 = p := by
    have htmp : p ^ 2 = p * Nat.card qA.ker := by
      calc
        p ^ 2 = Nat.card A := hAcard.symm
        _ = Nat.card (A ⧸ qA.ker) * Nat.card qA.ker := hA_card_expr
        _ = p * Nat.card qA.ker := by rw [hAquot_card, hAmap_card]
    have hmul : p * p = p * Nat.card qA.ker := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using htmp
    have hker_card : Nat.card qA.ker = p :=
      Nat.eq_of_mul_eq_mul_left (Fact.out : Nat.Prime p).pos hmul.symm
    simpa [hqA_ker, C0] using hker_card
  let C : Subgroup R := A ⊓ S
  have hC_eq : C0.map A.subtype = C := by
    simp [C, C0, inf_comm]
  have hC_card : Nat.card C = p := by
    calc
      Nat.card C = Nat.card (C0.map A.subtype) := by rw [← hC_eq]
      _ = Nat.card C0 := Subgroup.card_map_of_injective (f := A.subtype) Subtype.coe_injective
      _ = p := hC0_card
  have hC_le_A : C ≤ A := inf_le_left
  have hC_le_S : C ≤ S := inf_le_right
  letI : C.Normal := by infer_instance
  have hAS_top : A ⊔ S = ⊤ := by
    apply (Subgroup.eq_top_iff' (H := A ⊔ S)).2
    intro r
    have hqr : q r ∈ A.map q := by simp [hAmap_top]
    rcases Subgroup.mem_map.mp hqr with ⟨a, haA, haq⟩
    have hker : a⁻¹ * r ∈ S := by
      apply (QuotientGroup.eq_one_iff (N := S) (x := a⁻¹ * r)).1
      have : (q a)⁻¹ * q r = 1 := by
        simpa using (congrArg (fun t => (q a)⁻¹ * t) haq).symm
      simpa [q, MonoidHom.map_mul] using this
    exact (Subgroup.mem_sup_of_normal_right).2 ⟨a, haA, a⁻¹ * r, hker, by simp⟩
  have hC_le_center : C ≤ Subgroup.center R := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro r
    have hrSup : r ∈ A ⊔ S := by simp [hAS_top]
    rcases (Subgroup.mem_sup_of_normal_right (s := A) (t := S)).1 hrSup with
      ⟨a, haA, s, hsS, har⟩
    letI : IsMulCommutative A := hAelem.toIsMulCommutative
    have hca : c * a = a * c := by
      exact congrArg Subtype.val (mul_comm (⟨c, hC_le_A hc⟩ : A) ⟨a, haA⟩)
    have hcs : c * s = s * c := by
      exact congrArg Subtype.val (mul_comm (⟨c, hC_le_S hc⟩ : S) ⟨s, hsS⟩)
    calc
      r * c = (a * s) * c := by rw [har]
      _ = a * (s * c) := by simp [mul_assoc]
      _ = a * (c * s) := by rw [hcs]
      _ = (a * c) * s := by simp [mul_assoc]
      _ = (c * a) * s := by rw [hca]
      _ = c * (a * s) := by simp [mul_assoc]
      _ = c * r := by rw [har]
  have hcomm_le_C : ⁅A, S⁆ ≤ C := by
    simpa [C] using (Subgroup.commutator_le_inf (H₁ := A) (H₂ := S))
  have hC_pow : ∀ c : C, c ^ p = 1 := by
    intro c
    have hpow : c ^ Nat.card C = 1 := by
      simp
    simpa [hC_card] using hpow
  have hmem_C_of_mem_S_of_pow : ∀ {s : R}, s ∈ S → s ^ p = 1 → s ∈ C := by
    intro s hsS hs_pow
    let T : Subgroup R := C ⊔ Subgroup.zpowers s
    have hT_le_S : T ≤ S := by
      refine sup_le hC_le_S (Subgroup.zpowers_le_of_mem hsS)
    have hTcyc : IsCyclic T := Subgroup.isCyclic_of_le hT_le_S
    have hTpow : ∀ t : T, t ^ p = 1 := by
      intro t
      rcases (Subgroup.mem_sup_of_normal_left (s := C) (t := Subgroup.zpowers s)).1 t.2 with
        ⟨c, hcC, z, hz, hcz⟩
      have hc_pow : c ^ p = 1 := by
        simpa using hC_pow ⟨c, hcC⟩
      have hz_pow : z ^ p = 1 := by
        have hz_order_dvd : orderOf z ∣ p := by
          exact dvd_trans (orderOf_dvd_of_mem_zpowers hz) ((orderOf_dvd_iff_pow_eq_one).2 hs_pow)
        exact (orderOf_dvd_iff_pow_eq_one).1 hz_order_dvd
      have hc_cent : c ∈ Subgroup.center R := hC_le_center hcC
      have hcomm_cent : ⁅c, z⁆ ∈ Subgroup.center R := by
        have hcomm_eq_one : ⁅c, z⁆ = 1 := by
          exact (commutatorElement_eq_one_iff_mul_comm).2 ((Subgroup.mem_center_iff.mp hc_cent) z).symm
        simp [hcomm_eq_one]
      apply Subtype.ext
      change ((t : R) ^ p = 1)
      rw [← hcz]
      calc
        (c * z) ^ p = c ^ p * z ^ p * ⁅z, c⁆ ^ Nat.choose p 2 := by
          exact lemma_4_2_b (G := R) (x := c) (y := z) (n := p) hp_one_lt hcomm_cent
        _ = 1 := by
          have hcomm_eq_one : ⁅z, c⁆ = 1 := by
            exact (commutatorElement_eq_one_iff_mul_comm).2 ((Subgroup.mem_center_iff.mp hc_cent) z)
          simp [hc_pow, hz_pow, hcomm_eq_one]
    have hTexp_dvd : Monoid.exponent T ∣ p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hTpow
    letI : IsCyclic T := hTcyc
    have hT_card_dvd : Nat.card T ∣ p := by
      simpa [hTcyc.exponent_eq_card] using hTexp_dvd
    have hC_le_T : C ≤ T := le_sup_left
    have hp_le_hT : p ≤ Nat.card T := by
      simpa [hC_card] using Subgroup.card_le_of_le hC_le_T
    have hT_card : Nat.card T = p := by
      rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hT_card_dvd with h1 | hp'
      · have hp_le_one : p ≤ 1 := by simpa [h1] using hp_le_hT
        exact False.elim ((not_le_of_gt hp_one_lt) hp_le_one)
      · exact hp'
    have hC_eq_T : C = T := Subgroup.eq_of_le_of_card_ge hC_le_T (by simp [hC_card, hT_card])
    have hsT : s ∈ T := by exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    rw [hC_eq_T]
    exact hsT
  have hgen_le_A : {x : R | x ^ (p ^ 1) = 1} ⊆ A := by
    intro x hx
    have hxp : x ^ p = 1 := by simpa [pow_one] using hx
    by_cases hxS : x ∈ S
    · exact hC_le_A (hmem_C_of_mem_S_of_pow hxS hxp)
    · have hxq_mem : q x ∈ A.map q := by simp [hAmap_top]
      rcases Subgroup.mem_map.mp hxq_mem with ⟨a, haA, haeq⟩
      let s : R := a⁻¹ * x
      have hxs : x = a * s := by
        dsimp [s]
        group
      have hsS : s ∈ S := by
        apply (QuotientGroup.eq_one_iff (N := S) (x := s)).1
        calc
          q s = (q a)⁻¹ * q x := by simp [q, s, MonoidHom.map_mul]
          _ = 1 := by simp [haeq]
      have ha_pow : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian a haA
      have hcomm_as_C : ⁅a, s⁆ ∈ C := hcomm_le_C (Subgroup.commutator_mem_commutator haA hsS)
      have hcomm_as_center : ⁅a, s⁆ ∈ Subgroup.center R := hC_le_center hcomm_as_C
      have hcomm_sa_C : ⁅s, a⁆ ∈ C := by
        simpa [commutatorElement_inv] using (C.inv_mem hcomm_as_C)
      have hcomm_sa_p : ⁅s, a⁆ ^ p = 1 := by
        simpa using hC_pow ⟨⁅s, a⁆, hcomm_sa_C⟩
      have hcomm_sa_choose : ⁅s, a⁆ ^ Nat.choose p 2 = 1 := choose_two_pow_eq_one (p := p) hpodd hcomm_sa_p
      have hxpow_eq : x ^ p = a ^ p * s ^ p * ⁅s, a⁆ ^ Nat.choose p 2 := by
        rw [hxs]
        exact lemma_4_2_b (G := R) (x := a) (y := s) (n := p) hp_one_lt hcomm_as_center
      have hs_pow : s ^ p = 1 := by
        have hxpow_eq' : x ^ p = s ^ p := by
          calc
            x ^ p = a ^ p * s ^ p * ⁅s, a⁆ ^ Nat.choose p 2 := hxpow_eq
            _ = s ^ p := by simp [ha_pow, hcomm_sa_choose]
        calc
          s ^ p = x ^ p := hxpow_eq'.symm
          _ = 1 := hxp
      have hsA : s ∈ A := hC_le_A (hmem_C_of_mem_S_of_pow hsS hs_pow)
      rw [hxs]
      exact A.mul_mem haA hsA
  have hΩ_le_A : Ω ≤ A := by
    change Subgroup.closure {x : R | x ^ (p ^ 1) = 1} ≤ A
    exact (Subgroup.closure_le (K := A)).2 hgen_le_A
  have hΩ_eq_A : Ω = A := le_antisymm hΩ_le_A hA_le_Ω
  constructor
  · change Nat.card Ω = p ^ 2
    rw [hΩ_eq_A]
    exact hAcard
  · change IsElementaryAbelian p Ω
    rw [hΩ_eq_A]
    exact hAelem


end Main
