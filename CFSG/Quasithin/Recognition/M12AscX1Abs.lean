module

public import CFSG.Quasithin.Recognition.M12AscCoprime

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

@[expose] def conjP (P : Subgroup G) (g : G) (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) : ↥P →* ↥P where
  toFun p := ⟨g * p * g⁻¹, hg p p.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjP_coe (P : Subgroup G) (g : G) (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (p : ↥P) :
    (conjP P g hg p : G) = g * p * g⁻¹ := rfl

@[expose] def conjQ (P X : Subgroup G) [hXn : (X.subgroupOf P).Normal] (g : G)
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hgX : ∀ q ∈ X, g * q * g⁻¹ ∈ X) :
    (↥P ⧸ X.subgroupOf P) →* (↥P ⧸ X.subgroupOf P) :=
  QuotientGroup.map (X.subgroupOf P) (X.subgroupOf P) (conjP P g hg) (by
    intro q hq
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_subgroupOf.2 (hgX q (Subgroup.mem_subgroupOf.1 hq)))

theorem conjQ_mk (P X : Subgroup G) [hXn : (X.subgroupOf P).Normal] (g : G)
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hgX : ∀ q ∈ X, g * q * g⁻¹ ∈ X) (p : ↥P) :
    conjQ P X g hg hgX (QuotientGroup.mk p) = QuotientGroup.mk (conjP P g hg p) := rfl

theorem zpow_eq_one_of_eq_inv {x : G} (hx3 : x ^ 3 = 1) (l : ℤ) (h : x ^ l = (x ^ l)⁻¹) :
    x ^ l = 1 := by
  have hyy : x ^ l * x ^ l = 1 := by
    calc x ^ l * x ^ l = x ^ l * (x ^ l)⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  have hy3 : (x ^ l) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  calc x ^ l = x ^ l * (x ^ l * x ^ l) := by rw [hyy, mul_one]
    _ = (x ^ l) ^ 3 := by group
    _ = 1 := hy3

theorem lift_x1 {x z g p : G} (P : Subgroup G) (hx3 : x ^ 3 = 1) (hxP : x ∈ P)
    (hPx : ∀ q ∈ P, q * x = x * q) (hpP : p ∈ P)
    (hgx : g * x * g⁻¹ = x⁻¹) (hgz : g * z = z * g) (hzx : z * x = x * z)
    (hp1 : ∃ j : ℤ, g * p * g⁻¹ = p * x ^ j) (hp2 : ∃ k : ℤ, z * p * z⁻¹ = p⁻¹ * x ^ k)
    (hp3 : p ∉ zpowers x) (hp4 : ∃ i : ℤ, p ^ 3 = x ^ i) :
    ∃ x1 : G, x1 ∈ P ∧ orderOf x1 = 3 ∧ x1 ∉ zpowers x ∧ x1 * g = g * x1 ∧
      z * x1 * z⁻¹ = x1⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := hp1
  obtain ⟨k, hk⟩ := hp2
  obtain ⟨i, hi⟩ := hp4
  have hpx : Commute p x := hPx p hpP
  have hcomm : ∀ n : ℤ, p * x ^ n = x ^ n * p := fun n => Commute.zpow_right hpx n
  have hgzc : g * z * g⁻¹ = z := by rw [hgz]; group
  have hzxc : ∀ n : ℤ, z * x ^ n * z⁻¹ = x ^ n := fun n => by
    rw [← conj_zpow]
    have : z * x * z⁻¹ = x := by rw [hzx]; group
    rw [this]
  have hgxc : ∀ n : ℤ, g * x ^ n * g⁻¹ = x ^ (-n) := fun n => by
    rw [← conj_zpow, hgx, inv_zpow']
  have h3 : ∀ n : ℤ, x ^ (3 * n) = 1 := fun n => by
    rw [zpow_mul]
    simp [hx3]
  obtain ⟨p', hp'⟩ : ∃ p' : G, p' = p * x ^ (2 * j) := ⟨_, rfl⟩
  have hp'P : p' ∈ P := by rw [hp']; exact mul_mem hpP (zpow_mem hxP _)
  have hgp' : g * p' * g⁻¹ = p' := by
    calc g * p' * g⁻¹ = (g * p * g⁻¹) * (g * x ^ (2 * j) * g⁻¹) := by rw [hp']; group
      _ = (p * x ^ j) * x ^ (-(2 * j)) := by rw [hj, hgxc]
      _ = p * x ^ (-j) := by rw [mul_assoc, ← zpow_add]; congr 2; ring
      _ = p * (x ^ (-j) * x ^ (3 * j)) := by rw [h3, mul_one]
      _ = p' := by rw [hp', ← zpow_add]; congr 2; ring
  have hzp'p : (z * p' * z⁻¹) * p' = x ^ (k + 4 * j) := by
    calc (z * p' * z⁻¹) * p' = ((z * p * z⁻¹) * (z * x ^ (2 * j) * z⁻¹)) * (p * x ^ (2 * j)) := by
          rw [hp']; group
      _ = (p⁻¹ * x ^ k * x ^ (2 * j)) * (p * x ^ (2 * j)) := by rw [hk, hzxc]
      _ = p⁻¹ * (x ^ (k + 2 * j) * p) * x ^ (2 * j) := by rw [zpow_add]; group
      _ = p⁻¹ * (p * x ^ (k + 2 * j)) * x ^ (2 * j) := by rw [← hcomm]
      _ = x ^ (k + 4 * j) := by
        rw [← mul_assoc, inv_mul_cancel, one_mul, ← zpow_add]; congr 1; ring
  have hgw : g * (z * p' * z⁻¹) * g⁻¹ = z * p' * z⁻¹ := by
    calc g * (z * p' * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * (g * p' * g⁻¹) * (g * z * g⁻¹)⁻¹ := by group
      _ = z * p' * z⁻¹ := by rw [hgzc, hgp']
  have hzinv : z * p' * z⁻¹ = p'⁻¹ := by
    have hl : g * (x ^ (k + 4 * j)) * g⁻¹ = x ^ (k + 4 * j) := by
      rw [← hzp'p]
      calc g * ((z * p' * z⁻¹) * p') * g⁻¹ = (g * (z * p' * z⁻¹) * g⁻¹) * (g * p' * g⁻¹) := by
            group
        _ = (z * p' * z⁻¹) * p' := by rw [hgw, hgp']
    rw [hgxc] at hl
    have h1 : x ^ (k + 4 * j) = 1 := by
      apply zpow_eq_one_of_eq_inv hx3
      rw [← zpow_neg]
      exact hl.symm
    rw [h1] at hzp'p
    exact eq_inv_of_mul_eq_one_left hzp'p
  have hp'3 : p' ^ 3 = 1 := by
    have hc : Commute p (x ^ (2 * j)) := Commute.zpow_right hpx _
    have h6 : (x ^ (2 * j)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      rw [show (2 * j) * ((3 : ℕ) : ℤ) = 3 * (2 * j) by push_cast; ring]
      exact h3 _
    have e : p' ^ 3 = x ^ i := by rw [hp', hc.mul_pow, h6, mul_one, hi]
    have hgi : g * x ^ i * g⁻¹ = x ^ i := by
      rw [← e]
      calc g * p' ^ 3 * g⁻¹ = (g * p' * g⁻¹) ^ 3 := by rw [conj_pow]
        _ = p' ^ 3 := by rw [hgp']
    rw [hgxc] at hgi
    have h1 : x ^ i = 1 := by
      apply zpow_eq_one_of_eq_inv hx3
      rw [← zpow_neg]
      exact hgi.symm
    rw [e, h1]
  have hp'X : p' ∉ zpowers x := by
    intro hmem
    apply hp3
    have : p = p' * (x ^ (2 * j))⁻¹ := by rw [hp']; group
    rw [this]
    exact mul_mem hmem (inv_mem (zpow_mem (Subgroup.mem_zpowers x) _))
  have hp'1 : p' ≠ 1 := fun h => hp'X (h ▸ one_mem _)
  refine ⟨p', hp'P, orderOf_eq_prime hp'3 hp'1, hp'X, ?_, hzinv⟩
  calc p' * g = (g * p' * g⁻¹) * g := by rw [hgp']
    _ = g * p' := by group

theorem exists_x1_abstract [Finite G] {x z u : G} (P : Subgroup G)
    (hx3 : orderOf x = 3) (hxP : x ∈ P) (hPx : ∀ p ∈ P, p * x = x * p)
    (hP9 : 9 ∣ Nat.card P) (hz2 : z * z = 1) (hzx : z * x = x * z)
    (hzP : ∀ p ∈ P, z * p * z⁻¹ ∈ P) (hzfix : ∀ p ∈ P, z * p * z⁻¹ = p → p ∈ zpowers x)
    (hu2 : u * u = 1) (hux : u * x * u = x⁻¹) (hzu : z * u = u * z)
    (huP : ∀ p ∈ P, u * p * u⁻¹ ∈ P) :
    ∃ g x1 : G, (g = u ∨ g = u * z) ∧ x1 ∈ P ∧ orderOf x1 = 3 ∧ x1 ∉ zpowers x ∧
      x1 * g = g * x1 ∧ z * x1 * z⁻¹ = x1⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hXP : zpowers x ≤ P := (Subgroup.zpowers_le).2 hxP
  have hzxc : ∀ n : ℤ, z * x ^ n * z⁻¹ = x ^ n := fun n => by
    rw [← conj_zpow]
    have : z * x * z⁻¹ = x := by rw [hzx]; group
    rw [this]
  have huxc' : u * x * u⁻¹ = x⁻¹ := by rw [hui]; exact hux
  have huxc : ∀ n : ℤ, u * x ^ n * u⁻¹ = x ^ (-n) := fun n => by
    rw [← conj_zpow, huxc', inv_zpow']
  have huzxc' : (u * z) * x * (u * z)⁻¹ = x⁻¹ := by
    calc (u * z) * x * (u * z)⁻¹ = u * (z * x * z⁻¹) * u⁻¹ := by group
      _ = x⁻¹ := by rw [show z * x * z⁻¹ = x by rw [hzx]; group]; exact huxc'
  have huzxc : ∀ n : ℤ, (u * z) * x ^ n * (u * z)⁻¹ = x ^ (-n) := fun n => by
    rw [← conj_zpow, huzxc', inv_zpow']
  have hzX : ∀ q ∈ zpowers x, z * q * z⁻¹ ∈ zpowers x := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [hzxc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have huX : ∀ q ∈ zpowers x, u * q * u⁻¹ ∈ zpowers x := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [huxc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have huzP : ∀ p ∈ P, (u * z) * p * (u * z)⁻¹ ∈ P := by
    intro p hp
    have : (u * z) * p * (u * z)⁻¹ = u * (z * p * z⁻¹) * u⁻¹ := by group
    rw [this]
    exact huP _ (hzP p hp)
  have huzX : ∀ q ∈ zpowers x, (u * z) * q * (u * z)⁻¹ ∈ zpowers x := by
    intro q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [huzxc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have hXn : ((zpowers x).subgroupOf P).Normal := by
    refine ⟨fun q hq p => ?_⟩
    have hq' : (q : G) ∈ zpowers x := Subgroup.mem_subgroupOf.1 hq
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hq'
    have hcomm : (p : G) * (q : G) = (q : G) * (p : G) := by
      rw [← hn]
      exact Commute.zpow_right (hPx p p.2) n
    show ((p * q * p⁻¹ : ↥P) : G) ∈ zpowers x
    have : ((p * q * p⁻¹ : ↥P) : G) = (q : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (p : G) * q * (p : G)⁻¹ = ((q : G) * p) * (p : G)⁻¹ := by rw [hcomm]
        _ = q := by group
    rw [this]
    exact hq'
  let σ := conjQ P (zpowers x) z hzP hzX
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
    show conjQ P (zpowers x) z hzP hzX (conjQ P (zpowers x) z hzP hzX (QuotientGroup.mk p)) =
      QuotientGroup.mk p
    rw [conjQ_mk, conjQ_mk]
    congr 1
    apply Subtype.ext
    show z * (z * (p : G) * z⁻¹) * z⁻¹ = p
    rw [hzi]
    calc z * (z * (p : G) * z) * z = (z * z) * (p : G) * (z * z) := by group
      _ = p := by rw [hz2]; group
  have hσfix : ∀ a, σ a = a → a = 1 := by
    intro a ha
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
    have h1 : (QuotientGroup.mk (conjP P z hzP p) : ↥P ⧸ (zpowers x).subgroupOf P) =
        QuotientGroup.mk p := by
      rw [← conjQ_mk P (zpowers x) z hzP hzX]; exact ha
    have h2 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
    have h3 : ((z * (p : G) * z⁻¹)⁻¹ * (p : G)) ∈ zpowers x := by simpa [conjP_coe] using h2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h3
    have hc : z * (p : G) * z⁻¹ = (p : G) * (x ^ j)⁻¹ := by
      calc z * (p : G) * z⁻¹ = (p : G) * ((z * (p : G) * z⁻¹)⁻¹ * (p : G))⁻¹ := by group
        _ = (p : G) * (x ^ j)⁻¹ := by rw [← hj]
    have hp2 : (p : G) = (p : G) * (x ^ j)⁻¹ * (x ^ j)⁻¹ := by
      calc (p : G) = z * (z * (p : G) * z⁻¹) * z⁻¹ := by
            rw [hzi]; calc (p : G) = (z * z) * p * (z * z) := by rw [hz2]; group
              _ = z * (z * p * z) * z := by group
        _ = z * ((p : G) * (x ^ j)⁻¹) * z⁻¹ := by rw [hc]
        _ = (z * (p : G) * z⁻¹) * (z * (x ^ j)⁻¹ * z⁻¹) := by group
        _ = (p : G) * (x ^ j)⁻¹ * (x ^ j)⁻¹ := by
          rw [hc, ← zpow_neg, hzxc]
    have hy : (x ^ j)⁻¹ * (x ^ j)⁻¹ = 1 := by
      have h' : (p : G) * ((x ^ j)⁻¹ * (x ^ j)⁻¹) = (p : G) * 1 := by
        rw [mul_one, ← mul_assoc]; exact hp2.symm
      exact mul_left_cancel h'
    have hy1 : x ^ (-j) = 1 := by
      apply zpow_eq_one_of_eq_inv hx3'
      apply eq_inv_of_mul_eq_one_left
      rw [zpow_neg]
      exact hy
    have hfix : z * (p : G) * z⁻¹ = (p : G) := by
      rw [hc, ← zpow_neg, hy1, mul_one]
    have hpX : (p : G) ∈ zpowers x := hzfix p p.2 hfix
    exact (QuotientGroup.eq_one_iff p).2 (Subgroup.mem_subgroupOf.2 hpX)
  have hinv : ∀ a, σ a = a⁻¹ := fpf_inverts σ hσσ hσfix
  have habel : ∀ a b : ↥P ⧸ (zpowers x).subgroupOf P, a * b = b * a := by
    intro a b
    have h1 : σ (a * b) = (a * b)⁻¹ := hinv _
    rw [map_mul, hinv, hinv, mul_inv_rev] at h1
    calc a * b = (b⁻¹ * a⁻¹)⁻¹ := by group
      _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h1]
      _ = b * a := by group
  have hXpc : Nat.card ((zpowers x).subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv, Nat.card_zpowers, hx3]
  have h3dvd : 3 ∣ Nat.card (↥P ⧸ (zpowers x).subgroupOf P) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup ((zpowers x).subgroupOf P)
    rw [hXpc] at this
    omega
  obtain ⟨xb, hxb⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hxb1 : xb ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxb
    omega
  have hxb3 : xb ^ 3 = 1 := by rw [← hxb]; exact pow_orderOf_eq_one xb
  have key : ∀ (g : G) (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P)
      (hgX : ∀ q ∈ zpowers x, g * q * g⁻¹ ∈ zpowers x), g * x * g⁻¹ = x⁻¹ → g * z = z * g →
      ∀ yb : ↥P ⧸ (zpowers x).subgroupOf P, yb ≠ 1 → yb ^ 3 = 1 →
        conjQ P (zpowers x) g hg hgX yb = yb →
        ∃ x1 : G, x1 ∈ P ∧ orderOf x1 = 3 ∧ x1 ∉ zpowers x ∧ x1 * g = g * x1 ∧
          z * x1 * z⁻¹ = x1⁻¹ := by
    intro g hg hgX hgx hgz yb hy1 hy3 hfix
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective yb
    have hp1 : ∃ j : ℤ, g * (p : G) * g⁻¹ = (p : G) * x ^ j := by
      have h1 : (QuotientGroup.mk (conjP P g hg p) : ↥P ⧸ (zpowers x).subgroupOf P) =
          QuotientGroup.mk p := by
        rw [← conjQ_mk P (zpowers x) g hg hgX]; exact hfix
      have h2 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1)
      have h3 : ((g * (p : G) * g⁻¹)⁻¹ * (p : G)) ∈ zpowers x := by simpa [conjP_coe] using h2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h3
      refine ⟨-j, ?_⟩
      calc g * (p : G) * g⁻¹ = (p : G) * ((g * (p : G) * g⁻¹)⁻¹ * (p : G))⁻¹ := by group
        _ = (p : G) * x ^ (-j) := by rw [← hj, zpow_neg]
    have hp2 : ∃ k : ℤ, z * (p : G) * z⁻¹ = (p : G)⁻¹ * x ^ k := by
      have h1 : σ (QuotientGroup.mk p) = (QuotientGroup.mk p)⁻¹ := hinv _
      rw [← QuotientGroup.mk_inv] at h1
      have h1' : (QuotientGroup.mk (conjP P z hzP p) : ↥P ⧸ (zpowers x).subgroupOf P) =
          QuotientGroup.mk p⁻¹ := h1
      have h2 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1')
      have h3 : ((z * (p : G) * z⁻¹)⁻¹ * (p : G)⁻¹) ∈ zpowers x := by simpa [conjP_coe] using h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h3
      refine ⟨-k, ?_⟩
      calc z * (p : G) * z⁻¹ = (p : G)⁻¹ * ((z * (p : G) * z⁻¹)⁻¹ * (p : G)⁻¹)⁻¹ := by group
        _ = (p : G)⁻¹ * x ^ (-k) := by rw [← hk, zpow_neg]
    have hp3 : (p : G) ∉ zpowers x := fun h =>
      hy1 ((QuotientGroup.eq_one_iff p).2 (Subgroup.mem_subgroupOf.2 h))
    have hp4 : ∃ i : ℤ, (p : G) ^ 3 = x ^ i := by
      have h1 : (QuotientGroup.mk (p ^ 3) : ↥P ⧸ (zpowers x).subgroupOf P) = 1 := by
        rw [QuotientGroup.mk_pow]; exact hy3
      have h2 := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (by simpa using h2)
      exact ⟨i, hi.symm⟩
    exact lift_x1 P hx3' hxP hPx p.2 hgx hgz hzx hp1 hp2 hp3 hp4
  let τ := conjQ P (zpowers x) u huP huX
  have hττ : ∀ a, τ (τ a) = a := by
    intro a
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective a
    show conjQ P (zpowers x) u huP huX (conjQ P (zpowers x) u huP huX (QuotientGroup.mk p)) =
      QuotientGroup.mk p
    rw [conjQ_mk, conjQ_mk]
    congr 1
    apply Subtype.ext
    show u * (u * (p : G) * u⁻¹) * u⁻¹ = p
    rw [hui]
    calc u * (u * (p : G) * u) * u = (u * u) * (p : G) * (u * u) := by group
      _ = p := by rw [hu2]; group
  by_cases hy : xb * τ xb = 1
  ·
    have hτx : τ xb = xb⁻¹ := eq_inv_of_mul_eq_one_right hy
    have hfixx : conjQ P (zpowers x) (u * z) huzP huzX xb = xb := by
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective xb
      have e : conjQ P (zpowers x) (u * z) huzP huzX (QuotientGroup.mk p) =
          τ (σ (QuotientGroup.mk p)) := by
        show QuotientGroup.mk (conjP P (u * z) huzP p) =
          QuotientGroup.mk (conjP P u huP (conjP P z hzP p))
        congr 1
        apply Subtype.ext
        show (u * z) * (p : G) * (u * z)⁻¹ = u * (z * (p : G) * z⁻¹) * u⁻¹
        group
      rw [e, hinv, map_inv, hτx, inv_inv]
    obtain ⟨x1, hx1P, hx1o, hx1X, hx1g, hx1z⟩ := key (u * z) huzP huzX huzxc'
      (by rw [← mul_assoc, ← hzu]) xb hxb1 hxb3 hfixx
    exact ⟨u * z, x1, Or.inr rfl, hx1P, hx1o, hx1X, hx1g, hx1z⟩
  ·
    have hfixy : τ (xb * τ xb) = xb * τ xb := by
      rw [map_mul, hττ, habel]
    have hy3 : (xb * τ xb) ^ 3 = 1 := by
      rw [(show Commute xb (τ xb) from habel xb (τ xb)).mul_pow, hxb3, ← map_pow, hxb3, map_one,
        mul_one]
    obtain ⟨x1, hx1P, hx1o, hx1X, hx1g, hx1z⟩ := key u huP huX huxc' hzu.symm (xb * τ xb) hy hy3
      hfixy
    exact ⟨u, x1, Or.inl rfl, hx1P, hx1o, hx1X, hx1g, hx1z⟩

end CFSG.Quasithin
