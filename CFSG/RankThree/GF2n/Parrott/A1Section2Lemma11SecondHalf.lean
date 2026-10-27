module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma11FirstHalf
public import Certificates.Certificate946017
import all CFSG.RankThree.GF2n.Parrott.A1Section2Lemma11FirstHalf
import CFSG.RankThree.GF2n.Parrott.QA45SylowFacts
import CFSG.Monster.Existence.StdOdd.Coprime
import CFSG.GroupTheory.SupCommute
import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
private theorem mem_J_of_isPGroup_of_commute_five
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (hJ2 : IsPGroup 2 (J z)) {b : G} (hbH : b ∈ H z) (hb5 : orderOf b = 5) {x : G}
    (hxH : x ∈ H z) (hxb : x * b = b * x) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ J z := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set bA : ↥QA45.originalSubgroup := qHPA D ⟨b, hbH⟩ with hbA
  set yA : ↥QA45.originalSubgroup := qHPA D ⟨x, hxH⟩ with hyA
  have hbJ : b ∉ J z := by
    intro hbJ
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hJ2) ⟨b, hbJ⟩
    rw [Subgroup.orderOf_mk, hb5] at hk
    rcases k with _ | k
    · norm_num at hk
    · rw [pow_succ] at hk
      omega
  have hbA5 : orderOf bA = 5 := by
    have hdvd : orderOf bA ∣ 5 := by
      have e : orderOf (⟨b, hbH⟩ : ↥(H z)) = 5 := by rw [Subgroup.orderOf_mk, hb5]
      rw [← e]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h5
    · exfalso
      apply hbJ
      rw [mem_J_iff_qHPA_eq_one D hbH]
      exact orderOf_eq_one_iff.mp h1
    · exact h5
  have hBcard : Nat.card (Subgroup.zpowers bA) = 5 := by rw [Nat.card_zpowers, hbA5]
  obtain ⟨-, hCcard, w, hw2, hwconj, hCeq⟩ := qa45_sylowFive (Subgroup.zpowers bA) hBcard
  set P : Subgroup ↥QA45.originalSubgroup :=
    QP45.originalSubgroup.subgroupOf QA45.originalSubgroup with hP
  have hPn : P.Normal := Subgroup.normal_of_index_eq_two index_QP45
  have huvP : (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩ ∉ P := by
    intro h
    have hu : (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) ∈ P := u_mem_Q
    have hv : (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup) ∈ P := by
      have := P.mul_mem (P.inv_mem hu) h
      rwa [inv_mul_cancel_left] at this
    exact v_not_mem_Q hv
  have hwP : w ∉ P := by
    intro hw
    obtain ⟨c, hc⟩ := isConj_iff.mp hwconj
    apply huvP
    rw [← hc]
    exact hPn.conj_mem _ hw c
  set CB : Subgroup ↥QA45.originalSubgroup :=
    Subgroup.centralizer (Subgroup.zpowers bA : Set ↥QA45.originalSubgroup) with hCB
  have hBC : Subgroup.zpowers bA ≤ CB := by
    rw [hCeq]
    exact le_sup_left
  have hBP : Subgroup.zpowers bA ≤ P := by
    rw [Subgroup.zpowers_le, hP, ← range_qHPA D]
    exact ⟨_, rfl⟩
  have hCP5 : Nat.card ↥(CB ⊓ P) = 5 := by
    have h5 : 5 ∣ Nat.card ↥(CB ⊓ P) := by
      rw [← hBcard]
      exact Subgroup.card_dvd_of_le (le_inf hBC hBP)
    have h10 : Nat.card ↥(CB ⊓ P) ∣ 10 := by
      rw [← hCcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(CB ⊓ P) ≠ 10 := by
      intro h10'
      have heq : CB ⊓ P = CB :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hCcard, h10'])
      apply hwP
      have hwC : w ∈ CB := by
        rw [hCeq]
        exact le_sup_right (a := Subgroup.zpowers bA) (Subgroup.mem_zpowers w)
      rw [← heq] at hwC
      exact (Subgroup.mem_inf.mp hwC).2
    obtain ⟨m, hm⟩ := h5
    have hle := Nat.le_of_dvd (by norm_num) h10
    have hpos : 0 < Nat.card ↥(CB ⊓ P) := Nat.card_pos
    rw [hm] at hle hne hpos
    rw [hm]
    have hm1 : m = 1 := by omega
    rw [hm1]
  have hyC : yA ∈ CB ⊓ P := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hcomm : Commute bA yA := by
        have : (⟨b, hbH⟩ : ↥(H z)) * ⟨x, hxH⟩ = ⟨x, hxH⟩ * ⟨b, hbH⟩ :=
          Subtype.ext hxb.symm
        rw [hbA, hyA, Commute, SemiconjBy, ← map_mul, ← map_mul, this]
      exact (hcomm.zpow_left k).eq
    · rw [hP, ← range_qHPA D]
      exact ⟨_, rfl⟩
  have hy5 : orderOf yA ∣ 5 := by
    rw [← hCP5]
    exact Subgroup.orderOf_dvd_natCard _ hyC
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hx2) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have hy2 : orderOf yA ∣ 2 ^ k := by
    have e : orderOf (⟨x, hxH⟩ : ↥(H z)) = 2 ^ k := by rw [Subgroup.orderOf_mk, hk]
    rw [← e]
    exact orderOf_map_dvd _ _
  have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
  have hy1 : orderOf yA = 1 := Nat.eq_one_of_dvd_coprimes hcop hy2 hy5
  rw [mem_J_iff_qHPA_eq_one D hxH]
  exact orderOf_eq_one_iff.mp hy1

omit [Finite G] in
private theorem exists_mem_normalizer_not_mem_of_lt' {p : ℕ} [Fact p.Prime] {T Q : Subgroup G}
    [Finite Q] (hQ : IsPGroup p Q) (hTQ : T < Q) :
    ∃ x ∈ Q, x ∉ T ∧ x ∈ Subgroup.normalizer (T : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : T.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hTQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ T.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyT (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (Subgroup.normalizer (T : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hTQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

omit [Finite G] in
private theorem isPGroup_zpowers_conj {p : ℕ} {x : G} (hx : IsPGroup p (Subgroup.zpowers x))
    (c : G) : IsPGroup p (Subgroup.zpowers (c * x * c⁻¹)) := by
  have h := hx.map (MulAut.conj c).toMonoidHom
  rwa [MonoidHom.map_zpowers] at h

namespace CaseIData

variable {σ : G} {J₀ J₁ : Subgroup G}

private theorem commute_of_comm_mem_zpowers_five (d : CaseIData z σ J₀ J₁) {s b : G}
    (hs : s ∈ H z) (hs5 : s ^ 5 = 1) (hb : ⁅s, b⁆ ∈ Subgroup.zpowers z) : s * b = b * s := by
  rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hb with h1 | h1
  · exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exfalso
    have hz2 : z * z = 1 := by
      rw [← pow_two, ← d.orderOf_z]
      exact pow_orderOf_eq_one z
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp hs
    have e1 : s * b * s⁻¹ = z * b := by
      rw [← h1, commutatorElement_def]
      group
    have e2 : s * (z * b) * s⁻¹ = b := by
      calc s * (z * b) * s⁻¹ = (s * z) * b * s⁻¹ := by group
        _ = z * (s * b * s⁻¹) := by rw [hsz]; group
        _ = b := by rw [e1, ← mul_assoc, hz2, one_mul]
    have hpow : s ^ 5 = s * (s * (s * (s * s))) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    have e5 : s * (s * (s * (s * s))) * b * (s * (s * (s * (s * s))))⁻¹ = z * b := by
      calc s * (s * (s * (s * s))) * b * (s * (s * (s * (s * s))))⁻¹ =
          s * (s * (s * (s * (s * b * s⁻¹) * s⁻¹) * s⁻¹) * s⁻¹) * s⁻¹ := by group
        _ = z * b := by rw [e1, e2, e1, e2, e1]
    rw [← hpow, hs5, one_mul, inv_one, mul_one] at e5
    have hz1 : z = 1 := by
      calc z = z * b * b⁻¹ := by group
        _ = 1 := by rw [← e5, mul_inv_cancel]
    have hz := d.orderOf_z
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)

private theorem exists_not_commute₀ (d : CaseIData z σ J₀ J₁) :
    ∃ u ∈ J₀, ∃ v ∈ J₀, v * u ≠ u * v := by
  have hnle : ¬ (J₀ : Set G) ⊆ Subgroup.zpowers z := by
    intro hle
    have hc := Subgroup.card_le_of_le (show J₀ ≤ Subgroup.zpowers z from hle)
    rw [d.card₀, Nat.card_zpowers, d.orderOf_z] at hc
    omega
  obtain ⟨u, hu, huz⟩ := Set.not_subset.mp hnle
  have hnc : ¬ ∀ y ∈ J z, y * u = u * y := fun hc =>
    huz (d.mem_zpowers_of_commute (d.J₀_le hu) hc)
  push Not at hnc
  obtain ⟨y, hy, hyu⟩ := hnc
  obtain ⟨a, ha, c, hc, rfl⟩ := d.decomp hy
  refine ⟨u, hu, a, ha, fun hau => hyu ?_⟩
  have hcu : c * u = u * c := (d.comm u hu c hc).symm
  rw [mul_assoc, hcu, ← mul_assoc, hau, mul_assoc]

private theorem card_inf_centralizer₁ (d : CaseIData z σ J₀ J₁) {j : G} (hj1 : j ∈ J₁)
    (hjz : j ∉ Subgroup.zpowers z) :
    Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({j} : Set G)) = 64 := by
  have hjJ : j ∈ J z := d.J₁_le hj1
  have hT : ∀ y ∈ J₁, y * j * y⁻¹ ∈ ({j, z * j} : Set G) := by
    intro y hy
    have hc := d.comm_mem_zpowers (d.J₁_le hy) hjJ
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hc with h1 | h1
    · left
      show y * j * y⁻¹ = j
      rw [commutatorElement_eq_one_iff_mul_comm.mp h1, mul_inv_cancel_right]
    · right
      show y * j * y⁻¹ = z * j
      rw [← h1, commutatorElement_def]
      group
  have hidx : (J₁ ⊓ Subgroup.centralizer ({j} : Set G)).relIndex J₁ ≤ 2 :=
    (relIndex_inf_centralizer_le_ncard (Set.toFinite _) hT).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have hmul := Subgroup.relIndex_mul_card (J₁ ⊓ Subgroup.centralizer ({j} : Set G)) J₁
  rw [inf_eq_left.mpr (inf_le_left : J₁ ⊓ Subgroup.centralizer ({j} : Set G) ≤ J₁),
    d.card₁] at hmul
  have hne : Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({j} : Set G)) ≠ 128 := by
    intro h128
    have heq : J₁ ⊓ Subgroup.centralizer ({j} : Set G) = J₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h128, d.card₁])
    apply hjz
    refine d.mem_zpowers_of_commute₀₁ hjJ (fun a ha => ?_) (fun b hb => ?_)
    · have := (Subgroup.mem_inf.mp (d.eq_inf_centralizer ▸ hj1)).2
      exact Subgroup.mem_centralizer_iff.mp this a ha
    · have hbC : b ∈ J₁ ⊓ Subgroup.centralizer ({j} : Set G) := by rw [heq]; exact hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hbC).2
  have hdvd : Nat.card ↥(J₁ ⊓ Subgroup.centralizer ({j} : Set G)) ∣ 2 ^ 7 := by
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num, ← d.card₁]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk7, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hk] at hmul hne ⊢
  have hpos : 0 < (J₁ ⊓ Subgroup.centralizer ({j} : Set G)).relIndex J₁ := by
    rcases Nat.eq_zero_or_pos ((J₁ ⊓ Subgroup.centralizer ({j} : Set G)).relIndex J₁) with h0 | h0
    · rw [h0, zero_mul] at hmul
      norm_num at hmul
    · exact h0
  interval_cases k <;> omega

private theorem mem_normalizer_inf_centralizer (d : CaseIData z σ J₀ J₁) {b j : G}
    (hbH : b ∈ H z) (hbj : b * j = j * b) :
    b ∈ Subgroup.normalizer ((J₁ ⊓ Subgroup.centralizer ({j} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hJ := Subgroup.mem_normalizer_iff.mp (d.normal₁ hbH) x
  have hC := Subgroup.mem_normalizer_iff.mp
    (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hbj)) x
  simp only [Subgroup.mem_inf]
  exact and_congr hJ hC

private theorem no_conj_z_eq_of_mem₁
    [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)
    (d : CaseIData z σ J₀ J₁) {j : G} (hj1 : j ∈ J₁) (hj2 : orderOf j = 2) (hjz : j ≠ z)
    (h5 : 5 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G))) :
    ∀ g : G, g * z * g⁻¹ ≠ j := by
  have hF5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ2 : IsPGroup 2 (J z) := IsPGroup.of_card (n := 9) (card_J_A1 d.hyp)
  have hjJ : j ∈ J z := d.J₁_le hj1
  have hjzp : j ∉ Subgroup.zpowers z := by
    rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z]
    rintro (h1 | h1)
    · rw [h1, orderOf_one] at hj2
      norm_num at hj2
    · exact hjz h1
  obtain ⟨b', hb'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(H z ⊓ Subgroup.centralizer ({j} : Set G))) 5 h5
  have hb5 : orderOf (b' : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hb'
  have hbH : (b' : G) ∈ H z := (Subgroup.mem_inf.mp b'.2).1
  have hbj : (b' : G) * j = j * b' :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp b'.2).2
  set b : G := (b' : G) with hbdef
  have hb5' : b ^ 5 = 1 := by
    rw [← hb5]
    exact pow_orderOf_eq_one b
  have hbJ₀ : ∀ a ∈ J₀, b * a = a * b := fun a ha =>
    d.commute_of_comm_mem_zpowers_five hbH hb5' (d.comm_mem_zpowers₀ D hbH ha)
  obtain ⟨y, hyJ₁, hyb, hyj⟩ : ∃ y ∈ J₁, y ∈ Subgroup.centralizer ({b} : Set G) ∧
      y ∉ Subgroup.centralizer ({j} : Set G) := by
    have hX := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5 (d.normal₁ hbH)
    have hY := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers hb5
      (d.mem_normalizer_inf_centralizer hbH hbj)
    rw [d.card₁] at hX
    rw [d.card_inf_centralizer₁ hj1 hjzp] at hY
    by_contra hall
    push Not at hall
    have heq : J₁ ⊓ Subgroup.centralizer ({j} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) =
        J₁ ⊓ Subgroup.centralizer ({b} : Set G) := by
      apply le_antisymm (inf_le_inf_right _ inf_le_left)
      intro x hx
      obtain ⟨hxJ₁, hxb⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxJ₁, hall x hxJ₁ hxb⟩, hxb⟩
    rw [heq] at hY
    have := hX.trans hY.symm
    norm_num [Nat.ModEq] at this
  intro g hg
  set B : Subgroup G := Subgroup.zpowers b with hBdef
  have hBH : B ≤ H z := Subgroup.zpowers_le.mpr hbH
  have hBcard : Nat.card B = 5 := by rw [Nat.card_zpowers, hb5]
  have hH5 : (Nat.card (H z)).factorization 5 = 1 := by
    rw [card_H_A1 d.hyp, show (2 : ℕ) ^ 15 * 405 = 2 ^ 15 * 3 ^ 4 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2 ^ 15),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 3 ^ 4),
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  have hBsyl : IsSylowOf 5 B (H z) := isSylowOf_of_card hBH (by rw [hBcard, hH5, pow_one])
  set B' : Subgroup G := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'def
  have hmemB' : ∀ x, x ∈ B' ↔ g * x * g⁻¹ ∈ B := by
    intro x
    rw [hB'def, Subgroup.mem_map_equiv]
    simp
  have hBj : ∀ x ∈ B, x * j = j * x := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left hbj m)).eq
  have hB'H : B' ≤ H z := by
    intro x hx
    have h1 := hBj _ ((hmemB' x).mp hx)
    rw [← hg] at h1
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * (x * z) * g⁻¹ = g * (z * x) * g⁻¹ := by
      calc g * (x * z) * g⁻¹ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
        _ = g * z * g⁻¹ * (g * x * g⁻¹) := h1
        _ = g * (z * x) * g⁻¹ := by group
    simpa using h2
  have hB'card : Nat.card B' = 5 := by
    rw [hB'def, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hBcard]
  have hB'syl : IsSylowOf 5 B' (H z) := isSylowOf_of_card hB'H (by rw [hB'card, hH5, pow_one])
  obtain ⟨k, hkH, hk⟩ := hBsyl.exists_mem_conj hB'syl
  set n : G := g * k with hndef
  have hnz : n * z * n⁻¹ = j := by
    have hkz : k * z * k⁻¹ = z := by
      have hc : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkH
      rw [hc, mul_inv_cancel_right]
    rw [← hg, hndef, mul_inv_rev]
    calc g * k * z * (k⁻¹ * g⁻¹) = g * (k * z * k⁻¹) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hkz]
  have hnB : ∀ x, x ∈ B ↔ n * x * n⁻¹ ∈ B := by
    intro x
    have e1 : n * x * n⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by rw [hndef]; group
    have e2 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rw [e1, ← hmemB' (k * x * k⁻¹), hk (k * x * k⁻¹), e2]
  have hcent : ∀ {c x : G}, (∀ y, y ∈ B ↔ c * y * c⁻¹ ∈ B) →
      x ∈ Subgroup.centralizer ({b} : Set G) →
      c * x * c⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    intro c x hc hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hb' : c⁻¹ * b * c ∈ B := (hc _).mpr (by
      rw [show c * (c⁻¹ * b * c) * c⁻¹ = b by group]
      exact Subgroup.mem_zpowers b)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hxb' : x * (c⁻¹ * b * c) = (c⁻¹ * b * c) * x := by
      rw [← hm]
      exact ((Commute.zpow_right hx m)).eq
    calc c * x * c⁻¹ * b = c * (x * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * b * c) * x) * c⁻¹ := by rw [hxb']
      _ = b * (c * x * c⁻¹) := by group
  have hnB' : ∀ y, y ∈ B ↔ n⁻¹ * y * n⁻¹⁻¹ ∈ B := by
    intro y
    have := hnB (n⁻¹ * y * n)
    rw [show n * (n⁻¹ * y * n) * n⁻¹ = y by group] at this
    rw [inv_inv]
    exact this.symm
  have hMF := fun {x : G} (hxH : x ∈ H z) (hxb : x ∈ Subgroup.centralizer ({b} : Set G))
      (hx2 : IsPGroup 2 (Subgroup.zpowers x)) =>
    mem_J_of_isPGroup_of_commute_five D hJ2 hbH hb5 hxH
      (Subgroup.mem_centralizer_singleton_iff.mp hxb) hx2
  set P : Subgroup G := J z ⊓ Subgroup.centralizer ({b} : Set G) with hPdef
  set T : Subgroup G := P ⊓ Subgroup.centralizer ({j} : Set G) with hTdef
  set Q : Subgroup G := P.map (MulAut.conj n).toMonoidHom with hQdef
  have hmemQ : ∀ x, x ∈ Q ↔ n⁻¹ * x * n ∈ P := by
    intro x
    rw [hQdef, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hP2 : IsPGroup 2 P := hJ2.to_le inf_le_left
  have hQ2 : IsPGroup 2 Q := hP2.map _
  have hzc : ∀ {p : G}, p ∈ J z → p * z = z * p := fun hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (J_le_H hp)
  have hTQ : T ≤ Q := by
    intro t ht
    obtain ⟨⟨htJ, htb⟩, htj⟩ := Subgroup.mem_inf.mp ht |>.imp_left Subgroup.mem_inf.mp
    rw [hmemQ]
    have hconjH : n⁻¹ * t * n ∈ H z := by
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have htj' : t * j = j * t := Subgroup.mem_centralizer_singleton_iff.mp htj
      rw [← hnz] at htj'
      have : n⁻¹ * (t * (n * z * n⁻¹)) * n = n⁻¹ * ((n * z * n⁻¹) * t) * n := by rw [htj']
      calc n⁻¹ * t * n * z = n⁻¹ * (t * (n * z * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * z * n⁻¹) * t) * n := this
        _ = z * (n⁻¹ * t * n) := by group
    have hconjb : n⁻¹ * t * n ∈ Subgroup.centralizer ({b} : Set G) := by
      have := hcent hnB' htb
      rwa [inv_inv] at this
    have hconj2 : IsPGroup 2 (Subgroup.zpowers (n⁻¹ * t * n)) := by
      have := isPGroup_zpowers_conj (hJ2.to_le (Subgroup.zpowers_le.mpr htJ)) n⁻¹
      rwa [inv_inv] at this
    exact Subgroup.mem_inf.mpr ⟨hMF hconjH hconjb hconj2, hconjb⟩
  have hCQz : ∀ x ∈ Q, x * z = z * x → x ∈ T := by
    intro x hx hxz
    have hp := (hmemQ x).mp hx
    obtain ⟨hpJ, hpb⟩ := Subgroup.mem_inf.mp hp
    have hxe : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    have hxH : x ∈ H z := by
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hxz
    have hxb : x ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [hxe]
      exact hcent hnB hpb
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
      rw [hxe]
      exact isPGroup_zpowers_conj (hJ2.to_le (Subgroup.zpowers_le.mpr hpJ)) n
    have hxJ := hMF hxH hxb hx2
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxJ, hxb⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hnz, hxe]
    have := hzc hpJ
    calc n * (n⁻¹ * x * n) * n⁻¹ * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [this]
      _ = n * z * n⁻¹ * (n * (n⁻¹ * x * n) * n⁻¹) := by group
  have hyP : y ∈ P := Subgroup.mem_inf.mpr ⟨d.J₁_le hyJ₁, hyb⟩
  have hyT : y ∉ T := fun hyT => hyj (Subgroup.mem_inf.mp hyT).2
  have hTP : T < P := lt_of_le_of_ne inf_le_left fun heq => hyT (heq ▸ hyP)
  have hcardQ : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hTQlt : T < Q := by
    refine lt_of_le_of_ne hTQ fun heq => ?_
    have h1 := Subgroup.card_lt_of_lt hTP
    rw [heq, hcardQ] at h1
    exact lt_irrefl _ h1
  obtain ⟨x, hxQ, hxT, hxN⟩ := exists_mem_normalizer_not_mem_of_lt' hQ2 hTQlt
  have hxz : x * z ≠ z * x := fun h => hxT (hCQz x hxQ h)
  have hJ₀T : J₀ ≤ T := by
    intro a ha
    have hja : a * j = j * a := by
      have := (Subgroup.mem_inf.mp (d.eq_inf_centralizer ▸ hj1)).2
      exact Subgroup.mem_centralizer_iff.mp this a ha
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨d.J₀_le ha,
      Subgroup.mem_centralizer_singleton_iff.mpr (hbJ₀ a ha).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hja⟩
  have hTab : ∀ u ∈ T, ∀ v ∈ T, v * u = u * v := by
    intro u hu v hv
    have huJ : u ∈ J z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu).1).1
    have hvJ : v ∈ J z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).1).1
    have hxN' : x⁻¹ ∈ Subgroup.normalizer (T : Set G) := inv_mem hxN
    have hu' : x⁻¹ * u * x ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hxN' u).mp hu
      simpa using this
    have hv' : x⁻¹ * v * x ∈ T := by
      have := (Subgroup.mem_normalizer_iff.mp hxN' v).mp hv
      simpa using this
    have hu'J : x⁻¹ * u * x ∈ J z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hu').1).1
    have hv'J : x⁻¹ * v * x ∈ J z := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv').1).1
    have hc1 := d.comm_mem_zpowers hvJ huJ
    have hc2 := d.comm_mem_zpowers hv'J hu'J
    have he : ⁅x⁻¹ * v * x, x⁻¹ * u * x⁆ = x⁻¹ * ⁅v, u⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [he] at hc2
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hc1 with h1 | h1
    · exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · exfalso
      rw [h1] at hc2
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z).mp hc2 with h2 | h2
      · have hz1 : z = 1 := by
          calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
            _ = 1 := by rw [h2]; group
        have hz := d.orderOf_z
        rw [hz1, orderOf_one] at hz
        exact absurd hz (by norm_num)
      · apply hxz
        calc x * z = x * (x⁻¹ * z * x) := by rw [h2]
          _ = z * x := by group
  obtain ⟨u, hu, v, hv, huv⟩ := d.exists_not_commute₀
  exact huv (hTab u (hJ₀T hu) v (hJ₀T hv))

end CaseIData

theorem no_conj_z_eq_of_mem_J1_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G))
    (hS1 : ∀ j ∈ J z ⊓ Subgroup.centralizer
        (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) : Set G),
      orderOf j = 2 → j ≠ z → 5 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)))
    {j : G} (hj1 : j ∈ J z ⊓ Subgroup.centralizer
      (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) : Set G))
    (hj2 : orderOf j = 2) (hjz : j ≠ z) :
    ∀ g : G, g * z * g⁻¹ ≠ j := by
  have d := caseIData_s1HP h heq
  have hj1' : j ∈ ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ := by
    rw [d.eq_inf_centralizer]
    exact hj1
  exact d.no_conj_z_eq_of_mem₁ (quotientDataA1 h) hj1' hj2 hjz (hS1 j hj1 hj2 hjz)

end CFSG.RankThree.GF2n.Parrott
