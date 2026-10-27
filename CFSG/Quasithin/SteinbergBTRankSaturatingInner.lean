module

public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.Quasithin.SteinbergBSSmallRankEscape

public noncomputable section

namespace CFSG.Quasithin.SteinbergBT

open Subgroup

variable {H : Type*} [Group H]

theorem not_orderOf_eq_of_mem_centralizer_inf {p : ℕ} [Finite H] {K : Subgroup H}
    (hZ : ¬p ∣ Nat.card (center K)) {x : H} (hxC : x ∈ centralizer (K : Set H)) (hxK : x ∈ K) :
    orderOf x ≠ p := by
  intro hx
  have hz : (⟨x, hxK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.1 hxC) y y.2)
  have h1 : orderOf (⟨⟨x, hxK⟩, hz⟩ : center K) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx]
  exact hZ (h1 ▸ orderOf_dvd_natCard _)

theorem rank_saturating_prime_centralizer_and_inner_containment [Finite H] {p : ℕ}
    (hp : p.Prime) (K : Subgroup H) (hZ : ¬p ∣ Nat.card (center K))
    (hrank : CFSG.pRank p K = CFSG.pRank p H) :
    ¬p ∣ Nat.card (centralizer (K : Set H)) ∧
      ∀ P : Subgroup H, IsPGroup p P → P ≤ normalizer (K : Set H) →
        (∀ x ∈ P, ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹) → P ≤ K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hC : ¬p ∣ Nat.card (centralizer (K : Set H)) := by
    intro hdvd
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (K : Set H)) p hdvd
    set c' : H := (c : H) with hc'def
    have hc' : orderOf c' = p := by rw [hc'def, Subgroup.orderOf_coe, hc]
    have hcC : c' ∈ centralizer (K : Set H) := c.2
    have hzK : zpowers c' ⊓ K = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxz, hxK⟩
      have hxC : x ∈ centralizer (K : Set H) := (zpowers_le.2 hcC) hxz
      have hdvdx : orderOf x ∣ p := hc' ▸ orderOf_dvd_of_mem_zpowers hxz
      rcases (Nat.dvd_prime hp).1 hdvdx with h1 | h1
      · exact mem_bot.2 (orderOf_eq_one_iff.1 h1)
      · exact absurd h1 (not_orderOf_eq_of_mem_centralizer_inf hZ hxC hxK)
    obtain ⟨B, hB, hBcard⟩ := SteinbergBM.exists_card_eq_pow_pRank (X := K) hp.one_lt
    set V : Subgroup H := B.map K.subtype with hVdef
    have hVK : V ≤ K := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hVcard : Nat.card V = p ^ CFSG.pRank p K := by
      rw [hVdef, card_map_of_injective K.subtype_injective, hBcard]
    have : CFSG.IsElementaryAbelian p B := hB
    have hVe : CFSG.IsElementaryAbelian p V := CFSG.IsElementaryAbelian.map_subtype
    have hce : CFSG.IsElementaryAbelian p (zpowers c') :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hc']; exact pow_orderOf_eq_one c')
    have hcV : zpowers c' ≤ centralizer (V : Set H) :=
      zpowers_le.2 (centralizer_le hVK hcC)
    have hdisj : V ⊓ zpowers c' = ⊥ := by
      rw [eq_bot_iff, ← hzK, inf_comm]
      exact inf_le_inf_left _ hVK
    have hcard : Nat.card (V ⊔ zpowers c' : Subgroup H) = p ^ (CFSG.pRank p K + 1) := by
      rw [SteinbergBM.card_sup_of_commute hcV hdisj, hVcard, Nat.card_zpowers, hc', pow_succ]
    have hsupe : CFSG.IsElementaryAbelian p (V ⊔ zpowers c' : Subgroup H) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hcV
    have hle := SteinbergBS.le_pRank_of_card hp.one_lt hsupe hcard
    omega
  refine ⟨hC, fun P hP _ hinner => ?_⟩
  intro x hx
  obtain ⟨k, hk, hxk⟩ := hinner x hx
  set c := k⁻¹ * x with hcdef
  have hcC : c ∈ centralizer (K : Set H) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := hxk y hy
    calc y * c = k⁻¹ * (k * y * k⁻¹) * x := by rw [hcdef]; group
      _ = k⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = c * y := by rw [hcdef]; group
  have hxkc : x = k * c := by rw [hcdef]; group
  obtain ⟨a, ha⟩ := hP ⟨x, hx⟩
  have hxpow : x ^ p ^ a = 1 := by
    have := congrArg Subtype.val ha
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hkc : Commute k c := (mem_centralizer_iff.1 hcC) k hk
  have hcpow : c ^ p ^ a ∈ K := by
    have h1 : k ^ p ^ a * c ^ p ^ a = 1 := by rw [← hkc.mul_pow, ← hxkc, hxpow]
    have h2 : c ^ p ^ a = (k ^ p ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact inv_mem (pow_mem hk _)
  have hcop : (p ^ a).Coprime (orderOf c) := by
    refine Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hC ?_)
    exact h.trans (Subgroup.orderOf_dvd_natCard _ hcC)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hcK : c ∈ K := by
    rw [← hm]
    exact pow_mem hcpow m
  rw [hxkc]
  exact mul_mem hk hcK

end CFSG.Quasithin.SteinbergBT
