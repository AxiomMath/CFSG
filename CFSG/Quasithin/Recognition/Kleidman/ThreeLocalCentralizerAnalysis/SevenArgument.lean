module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.CentralizerK

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem exists_pow_eq_of_mem_zpowers {G : Type} [Group G] {y : G} (hy3 : orderOf y = 3) {u : G}
    (hu : u ∈ Subgroup.zpowers y) : u = 1 ∨ u = y ∨ u = y ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h3 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have : y ^ k = y ^ (k % 3) := by
    have : (3 : ℤ) = (orderOf y : ℤ) := by rw [hy3]; rfl
    rw [← zpow_mod_orderOf, ← this]
  rw [this]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right; norm_cast

theorem _root_.CFSG.Quasithin.IsTypeH2.not_commute_of_orderOf_seven {G : Type} [Group G] [Finite G]
    {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1) {t u : G} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hu7 : orderOf u = 7) (htu : u * t = t * u) : False := by
  have hz2 : z * z = 1 := by rw [← pow_two]; exact h.sq
  obtain ⟨c, hc⟩ := exists_conj_of_one_class hz2 h.ne_one hone ht2 ht1
  have hmem : c⁻¹ * u * c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzc : z = c⁻¹ * t * c := by rw [← hc]; group
    calc c⁻¹ * u * c * z = c⁻¹ * (u * t) * c := by rw [hzc]; group
      _ = c⁻¹ * (t * u) * c := by rw [htu]
      _ = z * (c⁻¹ * u * c) := by rw [hzc]; group
  have hord : orderOf (⟨c⁻¹ * u * c, hmem⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 7 := by
    rw [Subgroup.orderOf_mk]
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) u
    simpa [MulAut.conj_apply, hu7] using this
  have hdvd := orderOf_dvd_natCard (⟨c⁻¹ * u * c, hmem⟩ : ↥(Subgroup.centralizer ({z} : Set G)))
  rw [hord, h.card_centralizer] at hdvd
  omega

theorem _root_.CFSG.Quasithin.IsTypeH2.false_of_pow_seven_mem_zpowers {G : Type} [Group G]
    [Finite G] {z : G} (h : IsTypeH2 G z) (hone : involutionClassCount G = 1) {y g : G}
    (hy3 : orderOf y = 3) (hg : g * y * g⁻¹ = y⁻¹) (hx1 : g ^ 2 ≠ 1)
    (hx7 : (g ^ 2) ^ 7 ∈ Subgroup.zpowers y) : False := by
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hy3; omega
  have hyinv : y⁻¹ ≠ y := by
    intro h1
    have : y ^ 2 = 1 := by
      calc y ^ 2 = y * y := pow_two y
        _ = y * y⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel y
    have hd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one this
    rw [hy3] at hd; omega
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx7
  have hcomm : g * (g ^ 2) ^ 7 * g⁻¹ = (g ^ 2) ^ 7 := by
    rw [← pow_mul]
    group
  have hgk : g * y ^ k * g⁻¹ = (y ^ k) := by rw [hk]; exact hcomm
  have hinvk : g * y ^ k * g⁻¹ = (y ^ k)⁻¹ := by
    calc g * y ^ k * g⁻¹ = (g * y * g⁻¹) ^ k := conj_zpow.symm
      _ = y⁻¹ ^ k := by rw [hg]
      _ = (y ^ k)⁻¹ := (inv_zpow _ _)
  have hyk : y ^ k = 1 := by
    have h2 : (y ^ k) * (y ^ k) = 1 := by
      calc (y ^ k) * (y ^ k) = (y ^ k)⁻¹⁻¹ * (y ^ k) := by simp
        _ = (g * y ^ k * g⁻¹)⁻¹ * (y ^ k) := by rw [hinvk]
        _ = (y ^ k)⁻¹ * (y ^ k) := by rw [hgk]
        _ = 1 := inv_mul_cancel _
    have hmem : y ^ k ∈ Subgroup.zpowers y := Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) k
    rcases exists_pow_eq_of_mem_zpowers hy3 hmem with h0 | h0 | h0
    · exact h0
    · exfalso
      rw [h0] at h2
      apply hyinv
      calc y⁻¹ = y⁻¹ * (y * y) := by rw [h2, mul_one]
        _ = y := by group
    · exfalso
      rw [h0] at h2
      apply hy1
      have : y ^ 4 = 1 := by
        calc y ^ 4 = y ^ 2 * y ^ 2 := by rw [← pow_add]
          _ = 1 := h2
      calc y = y ^ 4 * (y ^ 3)⁻¹ := by group
        _ = 1 := by rw [this, hy3']; group
  have hg14 : g ^ 14 = 1 := by
    have : (g ^ 2) ^ 7 = 1 := by rw [← hk, hyk]
    rw [← this, ← pow_mul]
  have ht2 : g ^ 7 * g ^ 7 = 1 := by rw [← pow_add]; exact hg14
  have ht1 : g ^ 7 ≠ 1 := by
    intro h7
    have hg8 : g = (g ^ 2) ^ 4 := by
      calc g = g ^ 7 * g := by rw [h7, one_mul]
        _ = g ^ 8 := by rw [← pow_succ]
        _ = (g ^ 2) ^ 4 := by rw [← pow_mul]
    have hc2 : g ^ 2 * y * (g ^ 2)⁻¹ = y := by
      calc g ^ 2 * y * (g ^ 2)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = g * y⁻¹ * g⁻¹ := by rw [hg]
        _ = (g * y * g⁻¹)⁻¹ := by group
        _ = y := by rw [hg]; simp
    have hc2' : Commute (g ^ 2) y := by
      have : g ^ 2 * y = y * g ^ 2 := by
        calc g ^ 2 * y = (g ^ 2 * y * (g ^ 2)⁻¹) * g ^ 2 := by simp only [mul_assoc, inv_mul_cancel, mul_one]
          _ = y * g ^ 2 := by rw [hc2]
      exact this
    have hcomm : (g ^ 2) ^ 4 * y * ((g ^ 2) ^ 4)⁻¹ = y := by
      have := (hc2'.pow_left 4).eq
      calc (g ^ 2) ^ 4 * y * ((g ^ 2) ^ 4)⁻¹ = (y * (g ^ 2) ^ 4) * ((g ^ 2) ^ 4)⁻¹ := by rw [this]
        _ = y := by group
    rw [← hg8, hg] at hcomm
    exact hyinv hcomm
  have hu7 : orderOf (g ^ 2) = 7 := by
    have h7 : (g ^ 2) ^ 7 = 1 := by rw [← pow_mul]; exact hg14
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime h7 hx1
  have hcg : g ^ 2 * g ^ 7 = g ^ 7 * g ^ 2 := by rw [← pow_add, ← pow_add, add_comm]
  exact h.not_commute_of_orderOf_seven hone ht2 ht1 hu7 hcg

end CFSG.Quasithin.Kleidman.ThreeLocal
