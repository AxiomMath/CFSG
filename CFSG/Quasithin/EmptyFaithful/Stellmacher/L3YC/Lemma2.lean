module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section E27

variable {K : Type*} [Group K] [Finite K]

theorem isElemAbelian_zpowers_order_three {a : K} (ha : orderOf a = 3) :
    IsElemAbelian 3 (Subgroup.zpowers a) ∧ Nat.card (Subgroup.zpowers a) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := exists_elemAbelian_sup_zpowers (G := K) (p := 3) (E := ⊥)
    (CFSG.SectionRank.isElemAbelian_bot 3) ha (fun e he => by
      rw [Subgroup.mem_bot] at he
      rw [he]; exact Commute.one_left _) (fun h => by
        rw [Subgroup.mem_bot] at h
        rw [h, orderOf_one] at ha
        omega)
  rw [bot_sup_eq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, Subgroup.card_bot]

theorem exists_elemAbelian_card_27 {E : Subgroup K} (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) {c : K} (hc : orderOf c = 3) (hcomm : ∀ e ∈ E, Commute e c)
    (hcE : c ∉ E) : ∃ A : Subgroup K, IsElemAbelian 3 A ∧ Nat.card A = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hA, hAc⟩ := exists_elemAbelian_sup_zpowers hE hc hcomm hcE
  exact ⟨_, hA, by rw [hAc, hE9]⟩

end E27

section Decomp

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem three_element_decomp {N : Subgroup K} [N.Normal]
    (hZ : ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1)
    (hT2 : ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹)
    {g : K} {m : ℕ} (hg : g ^ 3 ^ m = 1) :
    ∃ n ∈ N, ∃ c : K, (∀ a ∈ N, c * a = a * c) ∧ g = n * c ∧ n * c = c * n ∧
      n ^ 3 ^ m = 1 ∧ c ^ 3 ^ m = 1 := by
  obtain ⟨n, hn, hgn⟩ := hT2 g ⟨m, hg⟩
  set c : K := n⁻¹ * g with hc
  have hcN : ∀ a ∈ N, c * a = a * c := by
    intro a ha
    have h1 := hgn a ha
    calc c * a = n⁻¹ * (g * a * g⁻¹) * g := by rw [hc]; group
      _ = n⁻¹ * (n * a * n⁻¹) * g := by rw [h1]
      _ = a * c := by rw [hc]; group
  have hgnc : g = n * c := by rw [hc]; group
  have hnc : n * c = c * n := (hcN n hn).symm
  have hpow : n ^ 3 ^ m * c ^ 3 ^ m = 1 := by
    rw [← (Commute.mul_pow hnc _), ← hgnc, hg]
  have hz : n ^ 3 ^ m = (c ^ 3 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hzN : n ^ 3 ^ m ∈ N := N.pow_mem hn _
  have hzc : ∀ a ∈ N, n ^ 3 ^ m * a = a * n ^ 3 ^ m := by
    intro a ha
    have h1 : c ^ 3 ^ m * a = a * c ^ 3 ^ m := ((show Commute c a from hcN a ha).pow_left _).eq
    rw [hz]
    have := congrArg (fun u => (c ^ 3 ^ m)⁻¹ * u * (c ^ 3 ^ m)⁻¹) h1
    simpa [mul_assoc] using this.symm
  have hn1 : n ^ 3 ^ m = 1 := hZ _ hzN hzc
  refine ⟨n, hn, c, hcN, hgnc, hnc, hn1, ?_⟩
  rw [hn1, one_mul] at hpow
  exact hpow

theorem mem_of_T1_T2 {N : Subgroup K} [N.Normal]
    (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hT1 : ∃ E : Subgroup K, E ≤ N ∧ IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hZ : ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1)
    (hT2 : ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹)
    {g : K} {m : ℕ} (hg : g ^ 3 ^ m = 1) : g ∈ N := by
  obtain ⟨n, hn, c, hcN, hgnc, -, -, hcm⟩ := three_element_decomp hZ hT2 hg
  by_cases hc1 : c = 1
  · rw [hgnc, hc1, mul_one]; exact hn
  exfalso
  obtain ⟨E, hEN, hE, hE9⟩ := hT1
  have hdvd : orderOf c ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hcm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hc1 hk
  have h3dvd : 3 ∣ orderOf c := by
    rw [hk]; exact dvd_pow_self 3 hk0
  have hord := orderOf_pow_orderOf_div (x := c) (orderOf_pos c).ne' h3dvd
  set c' : K := c ^ (orderOf c / 3) with hc'
  have hc'N : ∀ a ∈ N, c' * a = a * c' := fun a ha =>
    ((show Commute c a from hcN a ha).pow_left _).eq
  have hc'nN : c' ∉ N := fun h => by
    have := hZ c' h (fun a ha => hc'N a ha)
    rw [this, orderOf_one] at hord
    omega
  obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_card_27 hE hE9 hord
    (fun e he => (show Commute e c' from (hc'N e (hEN he)).symm)) (fun h => hc'nN (hEN h))
  have := hrank A hA
  omega

theorem lemma2_trivial_center {N Lb : Subgroup K} [N.Normal] (hLb : Lb ≤ N)
    (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    (hZ : ∀ z ∈ N, (∀ a ∈ N, z * a = a * z) → z = 1)
    (hT2 : ∀ g : K, (∃ m : ℕ, g ^ 3 ^ m = 1) →
      ∃ n ∈ N, ∀ a ∈ N, g * a * g⁻¹ = n * a * n⁻¹)
    {e x : K} (he : e ∈ Lb) (he3 : orderOf e = 3) (hx3 : orderOf x = 3) (hex : e * x = x * e)
    (hxL : x ∉ Subgroup.normalizer (Lb : Set K)) : x ∈ N := by
  have hx : x ^ 3 ^ 1 = 1 := by
    rw [pow_one, ← hx3]
    exact pow_orderOf_eq_one x
  obtain ⟨g, hg, c, hcN, hxgc, -, hg3, hc3⟩ := three_element_decomp hZ hT2 hx
  by_cases hc1 : c = 1
  · rw [hxgc, hc1, mul_one]; exact hg
  exfalso
  have hcnN : c ∉ N := fun h => hc1 (hZ c h hcN)
  have heg : e * g = g * e := by
    have h1 : e * (g * c) = (g * c) * e := by rw [← hxgc]; exact hex
    have hce : c * e = e * c := hcN e (hLb he)
    have : e * g * c = g * e * c := by
      calc e * g * c = e * (g * c) := by group
        _ = g * c * e := h1
        _ = g * (c * e) := by group
        _ = g * (e * c) := by rw [hce]
        _ = g * e * c := by group
    exact mul_right_cancel this
  have hxa : ∀ a ∈ N, x * a * x⁻¹ = g * a * g⁻¹ := by
    intro a ha
    have hca : c * a = a * c := hcN a ha
    calc x * a * x⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by rw [hxgc]; group
      _ = g * a * g⁻¹ := by rw [hca]; group
  by_cases hge : g ∈ Subgroup.zpowers e
  · apply hxL
    have hgLb : g ∈ Lb := (Subgroup.zpowers_le.mpr he) hge
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have haLb : a ∈ Lb := ha
    show x * a * x⁻¹ ∈ Lb
    rw [hxa a (hLb haLb)]
    exact Lb.mul_mem (Lb.mul_mem hgLb haLb) (Lb.inv_mem hgLb)
  · have hg1 : g ≠ 1 := fun h => hge (h ▸ Subgroup.one_mem _)
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    obtain ⟨hE1, -⟩ := isElemAbelian_zpowers_order_three he3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨hE2, hE2c⟩ := exists_elemAbelian_sup_zpowers hE1 hgo (fun u hu => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (show Commute e g from heg).zpow_left k) hge
    have hE2N : Subgroup.zpowers e ⊔ Subgroup.zpowers g ≤ N :=
      sup_le (Subgroup.zpowers_le.mpr (hLb he)) (Subgroup.zpowers_le.mpr hg)
    have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hcard : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers g) = 9 := by
      rw [hE2c, (isElemAbelian_zpowers_order_three he3).2]
    obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_card_27 hE2 hcard hc3'
      (fun u hu => (show Commute u c from (hcN u (hE2N hu)).symm)) (fun h => hcnN (hE2N h))
    have := hrank A hA
    omega

theorem lemma2_center_three {N : Subgroup K} [N.Normal]
    (hrank : ∀ E : Subgroup K, IsElemAbelian 3 E → Nat.card E ≤ 9)
    {z : K} (hzN : z ∈ N) (hzc : ∀ a ∈ N, z * a = a * z) (hz3 : orderOf z = 3)
    (hZ : ∀ w ∈ N, (∀ a ∈ N, w * a = a * w) → w ∈ Subgroup.zpowers z)
    {e x : K} (heN : e ∈ N) (he3 : orderOf e = 3) (hez : e ∉ Subgroup.zpowers z)
    (hx3 : orderOf x = 3) (hex : e * x = x * e) : x ∈ N := by
  by_contra hxN
  have hx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hxz : x * z * x⁻¹ = z := by
    have hwN : x * z * x⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance z hzN x
    have hwc : ∀ a ∈ N, (x * z * x⁻¹) * a = a * (x * z * x⁻¹) := by
      intro a ha
      have ha' : x⁻¹ * a * x ∈ N := by
        have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) a ha x⁻¹
        simpa using this
      have h1 := hzc _ ha'
      calc (x * z * x⁻¹) * a = x * (z * (x⁻¹ * a * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * z) * x⁻¹ := by rw [h1]
        _ = a * (x * z * x⁻¹) := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hZ _ hwN hwc)
    have hk' : z ^ (k % (3 : ℕ)) = x * z * x⁻¹ := by
      rw [← hz3, zpow_mod_orderOf]; exact hk
    have hk3 : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
    rcases hk3 with h | h | h
    · exfalso
      rw [h, zpow_zero] at hk'
      have : z = 1 := by
        calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
          _ = x⁻¹ * 1 * x := by rw [← hk']
          _ = 1 := by group
      rw [this, orderOf_one] at hz3
      omega
    · rw [h, zpow_one] at hk'
      exact hk'.symm
    · exfalso
      rw [h] at hk'
      have hz3' : z ^ (3 : ℕ) = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
      have hz2 : z ^ (2 : ℤ) = z⁻¹ := by
        calc z ^ (2 : ℤ) = z ^ (2 : ℕ) := by norm_cast
          _ = z⁻¹ := by
            apply eq_inv_of_mul_eq_one_left
            rw [← pow_succ]; exact hz3'
      rw [hz2] at hk'
      have hA : x * z * x⁻¹ = z⁻¹ := hk'.symm
      have hx2 : x * z⁻¹ * x⁻¹ = z := by
        have : x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
        rw [this, hA, inv_inv]
      have hxxx : x * x * x = 1 := by
        have e : x * x * x = x ^ 3 := by rw [pow_three, mul_assoc]
        rw [e]; exact hx
      have h3 : x * x * x * z * x⁻¹ * x⁻¹ * x⁻¹ = z := by
        calc x * x * x * z * x⁻¹ * x⁻¹ * x⁻¹ = (x * x * x) * z * (x * x * x)⁻¹ := by group
          _ = z := by rw [hxxx]; group
      have h4 : x * x * x * z * x⁻¹ * x⁻¹ * x⁻¹ = z⁻¹ := by
        calc x * x * x * z * x⁻¹ * x⁻¹ * x⁻¹ = x * (x * (x * z * x⁻¹) * x⁻¹) * x⁻¹ := by group
          _ = x * (x * z⁻¹ * x⁻¹) * x⁻¹ := by rw [hA]
          _ = x * z * x⁻¹ := by rw [hx2]
          _ = z⁻¹ := hA
      have hzz : z = z⁻¹ := h3.symm.trans h4
      have hzz' : z * z = 1 := mul_eq_one_iff_eq_inv.mpr hzz
      have : z = 1 := by
        calc z = z * z * z := by rw [hzz']; simp
          _ = 1 := by rw [← pow_three']; exact hz3'
      rw [this, orderOf_one] at hz3
      omega
  have hez' : e * z = z * e := (hzc e heN).symm
  have hxz' : x * z = z * x := by
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [hxz]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE1, -⟩ := isElemAbelian_zpowers_order_three hz3
  obtain ⟨hE2, hE2c⟩ := exists_elemAbelian_sup_zpowers hE1 he3 (fun u hu => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (show Commute z e from hez'.symm).zpow_left k) hez
  have hE2N : Subgroup.zpowers z ⊔ Subgroup.zpowers e ≤ N :=
    sup_le (Subgroup.zpowers_le.mpr hzN) (Subgroup.zpowers_le.mpr heN)
  have hcard : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers e) = 9 := by
    rw [hE2c, (isElemAbelian_zpowers_order_three hz3).2]
  have hcx : Subgroup.zpowers z ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({x} : Set K) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxz'.symm
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hex
  obtain ⟨A, hA, hA27⟩ := exists_elemAbelian_card_27 hE2 hcard hx3
    (fun u hu => (show Commute u x from Subgroup.mem_centralizer_singleton_iff.mp (hcx hu)))
    (fun h => hxN (hE2N h))
  have := hrank A hA
  omega

end Decomp

end Stellmacher.L3YC

end CFSG.Quasithin
