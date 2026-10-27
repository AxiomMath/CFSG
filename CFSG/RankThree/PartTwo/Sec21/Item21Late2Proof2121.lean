module

public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

section Elementary

theorem exists_pow_of_mem_zpowers {x y : G} (hx : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x) :
    ∃ k : ℕ, y = x ^ k := by
  obtain ⟨k, -, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hx hy
  exact ⟨k, rfl⟩

theorem eq_one_of_inv_eq {x : G} (hx : x ^ 3 = 1) (h : x⁻¹ = x) : x = 1 := by
  have h2 : x * x = 1 := by rw [← mul_inv_cancel x, h]
  calc x = x ^ 3 * (x * x)⁻¹ := by rw [pow_three]; group
    _ = 1 := by rw [hx, h2]; group

theorem eq_one_of_pow_mem [Finite G] {X : Subgroup G} {x : G} (hx : x ^ 3 = 1) (hxX : x ∉ X)
    {y : G} (hy : y ∈ Subgroup.zpowers x) (hyX : y ∈ X) : y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy1
  apply hxX
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hy1 (by simpa using hy)
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := exists_pow_of_mem_zpowers hx hy
    rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
  have hZ : Subgroup.zpowers y = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx hx1,
        orderOf_eq_prime hy3 hy1])
  have hxy : x ∈ Subgroup.zpowers y := hZ ▸ Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr hyX) hxy

theorem conj_eq_of_fix [Finite G] {A X : Subgroup G} (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (h3 : ∀ x ∈ A, x ^ 3 = 1) (hXA : X ≤ A) (hAX : Nat.card A = 3 * Nat.card X) {c k : G}
    (hcA : c ∈ A) (hcX : c ∉ X) (hkX : ∀ y ∈ X, k * y * k⁻¹ = y) (hkc : k * c * k⁻¹ = c) :
    ∀ a ∈ A, k * a * k⁻¹ = a := by
  intro a ha
  obtain ⟨j, -, y, hyX, rfl⟩ :=
    Item21LateProof.exists_pow_mul_of_card hcomm h3 hXA hAX hcA hcX a ha
  rw [show k * (c ^ j * y) * k⁻¹ = (k * c * k⁻¹) ^ j * (k * y * k⁻¹) by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply, map_mul, map_pow],
    hkc, hkX y hyX]

end Elementary

section Pure

variable [Finite G]

theorem false_of_invariant_nine {A X : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (hA : Nat.card A = 27) (hXA : X ≤ A) (hX : Nat.card X = 9)
    (hXW : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    {c d : G} (hcA : c ∈ A) (hcX : c ∉ X) (hdX : d ∈ X) (hd1 : d ≠ 1)
    {w t g : G} (hwW : w ∈ Subgroup.normalizer (A : Set G)) (hwc : w * c * w⁻¹ = c)
    (hwd : w * d * w⁻¹ = d) (hwA : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ Subgroup.zpowers d)
    (hwmove : ∃ a ∈ A, w * a * w⁻¹ ≠ a)
    (htW : t ∈ Subgroup.normalizer (A : Set G)) (htc : t * c * t⁻¹ = c)
    (htd : t * d * t⁻¹ = d⁻¹)
    (hgW : g ∈ Subgroup.normalizer (A : Set G)) (hgd : g * d * g⁻¹ ∉ Subgroup.zpowers d)
    (hH : ∀ h ∈ Subgroup.normalizer (A : Set G), h * c * h⁻¹ ∈ Subgroup.zpowers c →
      h * d * h⁻¹ ∈ Subgroup.zpowers d) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := Subgroup.normalizer (A : Set G) with hWdef
  have hAX : Nat.card A = 3 * Nat.card X := by rw [hA, hX]
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => hcomm x (hXA hx) y (hXA hy)
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := fun x hx => h3 x (hXA hx)
  have hd3 : d ^ 3 = 1 := hX3 d hdX
  have hdXle : Subgroup.zpowers d ≤ X := Subgroup.zpowers_le.mpr hdX
  have hZd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hconj : ∀ g x y : G, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) :=
    fun g x y => by group
  have hconjpow : ∀ (g x : G) (k : ℕ), g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun g x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have hWA : ∀ h ∈ W, ∀ a ∈ A, h * a * h⁻¹ ∈ A :=
    fun h hh a ha => (Subgroup.mem_normalizer_iff.mp hh a).mp ha
  have hWinv : ∀ h ∈ W, h⁻¹ ∈ W := fun h hh => W.inv_mem hh
  have hWinvA : ∀ h ∈ W, ∀ a ∈ A, h⁻¹ * a * h ∈ A := fun h hh a ha => by
    simpa using hWA h⁻¹ (hWinv h hh) a ha
  have hWinvX : ∀ h ∈ W, ∀ x ∈ X, h⁻¹ * x * h ∈ X := fun h hh x hx => by
    simpa using hXW h⁻¹ (hWinv h hh) x hx
  set d' := g * d * g⁻¹ with hd'
  have hd'X : d' ∈ X := hXW g hgW d hdX
  have hd'3 : d' ^ 3 = 1 := hX3 d' hd'X
  have hdecX := Item21LateProof.exists_pow_mul_of_card hXc hX3 hdXle (by rw [hX, hZd]) hd'X hgd
  have hfixX : ∀ k : G, k * d * k⁻¹ = d → k * d' * k⁻¹ = d' → ∀ x ∈ X, k * x * k⁻¹ = x := by
    intro k hkd hkd' x hx
    obtain ⟨j, -, y, hy, rfl⟩ := hdecX x hx
    rw [hconj, hconjpow, hkd', Item21LateProof.conj_eq_of_mem_zpowers hkd hy]
  have hwd' : w * d' * w⁻¹ ≠ d' := by
    intro h
    obtain ⟨a, ha, hne⟩ := hwmove
    exact hne (conj_eq_of_fix hcomm h3 hXA hAX hcA hcX (hfixX w hwd h) hwc a ha)
  set u := g * w * g⁻¹ with hu
  have huW : u ∈ W := W.mul_mem (W.mul_mem hgW hwW) (hWinv g hgW)
  have hud' : u * d' * u⁻¹ = d' := by
    calc u * d' * u⁻¹ = g * (w * d * w⁻¹) * g⁻¹ := by rw [hu, hd']; group
      _ = d' := by rw [hwd]
  have huA : ∀ a ∈ A, a⁻¹ * (u * a * u⁻¹) ∈ Subgroup.zpowers d' := by
    intro a ha
    have h1 := hwA _ (hWinvA g hgW a ha)
    have e : a⁻¹ * (u * a * u⁻¹) =
        g * ((g⁻¹ * a * g)⁻¹ * (w * (g⁻¹ * a * g) * w⁻¹)) * g⁻¹ := by rw [hu]; group
    rw [e]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact Subgroup.zpow_mem_zpowers _ k
  have hud : u * d * u⁻¹ ≠ d := by
    intro h
    obtain ⟨a, ha, hne⟩ := hwmove
    have hc'A : g * c * g⁻¹ ∈ A := hWA g hgW c hcA
    have hc'X : g * c * g⁻¹ ∉ X := fun h' => hcX (by
      have := hWinvX g hgW _ h'
      rwa [show g⁻¹ * (g * c * g⁻¹) * g = c by group] at this)
    have huc' : u * (g * c * g⁻¹) * u⁻¹ = g * c * g⁻¹ := by
      calc u * (g * c * g⁻¹) * u⁻¹ = g * (w * c * w⁻¹) * g⁻¹ := by rw [hu]; group
        _ = g * c * g⁻¹ := by rw [hwc]
    have hfu := conj_eq_of_fix hcomm h3 hXA hAX hc'A hc'X (hfixX u h hud') huc'
    apply hne
    have h1 := hfu (g * a * g⁻¹) (hWA g hgW a ha)
    have e : u * (g * a * g⁻¹) * u⁻¹ = g * (w * a * w⁻¹) * g⁻¹ := by rw [hu]; group
    rw [e] at h1
    calc w * a * w⁻¹ = g⁻¹ * (g * (w * a * w⁻¹) * g⁻¹) * g := by group
      _ = a := by rw [h1]; group
  have hwBc : ∀ y ∈ X, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers d := fun y hy => hwA y (hXA hy)
  have hw'Bc : ∀ y ∈ X, y⁻¹ * (u * y * u⁻¹) ∈ Subgroup.zpowers d' := fun y hy => huA y (hXA hy)
  obtain ⟨d₁, hd₁X, hd₁d, hwd₁, v, hv, hvd₁, hvd⟩ :=
    Item21LateProof.exists_normal_pair hXc hX3 hdX hd'X hgd hwBc hwd' hud' hw'Bc hud
  have hzinv := Item21LateProof.conj_sq_eq_inv hXc hX3 hX hdX hd1 hd₁X hd₁d hwd hwd₁ hvd₁ hvd
  have hvW : v ∈ W := by
    rcases hv with rfl | rfl
    · exact huW
    · exact W.mul_mem huW huW
  have hwAX : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ X := fun a ha => hdXle (hwA a ha)
  have huAX : ∀ a ∈ A, a⁻¹ * (u * a * u⁻¹) ∈ X :=
    fun a ha => (Subgroup.zpowers_le.mpr hd'X) (huA a ha)
  have hvAX : ∀ a ∈ A, a⁻¹ * (v * a * v⁻¹) ∈ X := by
    rcases hv with rfl | rfl
    · exact huAX
    · exact Item21LateProof.inv_mul_conj_mul_mem (hXW u huW) huAX huAX
  have hwvW : w * v ∈ W := W.mul_mem hwW hvW
  have hwvAX := Item21LateProof.inv_mul_conj_mul_mem (hXW w hwW) hwAX hvAX
  have hzAX := Item21LateProof.inv_mul_conj_mul_mem (hXW (w * v) hwvW) hwvAX hwvAX
  set z := w * v * (w * v) with hz
  have hzW : z ∈ W := W.mul_mem hwvW hwvW
  have hdecA := Item21LateProof.exists_pow_mul_of_card hcomm h3 hXA hAX hcA hcX
  by_cases hcase : ∃ k ∈ W, (∀ y ∈ X, k * y * k⁻¹ = y) ∧ c⁻¹ * (k * c * k⁻¹) ∈ X ∧
      k * c * k⁻¹ ≠ c
  ·
    obtain ⟨k₀, hk₀W, hk₀X, hk₀c, hk₀ne⟩ := hcase
    let Tr : G → Prop := fun x => ∃ k ∈ W, (∀ y ∈ X, k * y * k⁻¹ = y) ∧ k * c * k⁻¹ = c * x
    have hTr_mul : ∀ x₁ x₂, Tr x₁ → Tr x₂ → x₂ ∈ X → Tr (x₁ * x₂) := by
      rintro x₁ x₂ ⟨k₁, hk₁W, hk₁X, hk₁c⟩ ⟨k₂, hk₂W, hk₂X, hk₂c⟩ hx₂
      refine ⟨k₁ * k₂, W.mul_mem hk₁W hk₂W, fun y hy => ?_, ?_⟩
      · calc k₁ * k₂ * y * (k₁ * k₂)⁻¹ = k₁ * (k₂ * y * k₂⁻¹) * k₁⁻¹ := by group
          _ = y := by rw [hk₂X y hy, hk₁X y hy]
      · calc k₁ * k₂ * c * (k₁ * k₂)⁻¹ = k₁ * (k₂ * c * k₂⁻¹) * k₁⁻¹ := by group
          _ = (k₁ * c * k₁⁻¹) * (k₁ * x₂ * k₁⁻¹) := by rw [hk₂c, hconj]
          _ = c * (x₁ * x₂) := by rw [hk₁c, hk₁X x₂ hx₂, mul_assoc]
    have hTr_one : Tr 1 := ⟨1, W.one_mem, fun y _ => by group, by group⟩
    have hTr_pow : ∀ x, Tr x → x ∈ X → ∀ n : ℕ, Tr (x ^ n) := by
      intro x hx hxX n
      induction n with
      | zero => simpa using hTr_one
      | succ n ih =>
        rw [pow_succ]
        exact hTr_mul _ _ ih hx hxX
    have hTr_zpowers : ∀ x, Tr x → x ∈ X → ∀ y ∈ Subgroup.zpowers x, Tr y := by
      intro x hx hxX y hy
      obtain ⟨n, rfl⟩ := exists_pow_of_mem_zpowers (hX3 x hxX) hy
      exact hTr_pow x hx hxX n
    have hTr_inv : ∀ x, Tr x → x ∈ X → Tr x⁻¹ := fun x hx hxX =>
      hTr_zpowers x hx hxX _ ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))
    have hTr_conj : ∀ x, Tr x → x ∈ X → ∀ h ∈ W, Tr (h * x * h⁻¹) := by
      rintro x ⟨k, hkW, hkX, hkc⟩ hxX h hh
      obtain ⟨e, he3, y₁, hy₁, he⟩ := hdecA _ (hWinvA h hh c hcA)
      have hhxX : h * x * h⁻¹ ∈ X := hXW h hh x hxX
      have hxA : x ∈ A := hXA hxX
      have hy₁A : y₁ ∈ A := hXA hy₁
      have hk' : Tr ((h * x * h⁻¹) ^ e) := by
        refine ⟨h * k * h⁻¹, W.mul_mem (W.mul_mem hh hkW) (hWinv h hh), fun y hy => ?_, ?_⟩
        · have hy' := hWinvX h hh y hy
          calc h * k * h⁻¹ * y * (h * k * h⁻¹)⁻¹ = h * (k * (h⁻¹ * y * h) * k⁻¹) * h⁻¹ := by
                group
            _ = y := by rw [hkX _ hy']; group
        · calc h * k * h⁻¹ * c * (h * k * h⁻¹)⁻¹ = h * (k * (h⁻¹ * c * h) * k⁻¹) * h⁻¹ := by
                group
            _ = h * ((k * c * k⁻¹) ^ e * (k * y₁ * k⁻¹)) * h⁻¹ := by
                rw [he, hconj k (c ^ e) y₁, hconjpow k c e]
            _ = h * ((c * x) ^ e * y₁) * h⁻¹ := by rw [hkc, hkX y₁ hy₁]
            _ = h * ((c ^ e * y₁) * x ^ e) * h⁻¹ := by
                have hin : (c * x) ^ e * y₁ = (c ^ e * y₁) * x ^ e := by
                  rw [Commute.mul_pow (hcomm c hcA x hxA) e, mul_assoc,
                    hcomm (x ^ e) (A.pow_mem hxA e) y₁ hy₁A, ← mul_assoc]
                rw [hin]
            _ = (h * (c ^ e * y₁) * h⁻¹) * (h * x * h⁻¹) ^ e := by rw [hconj, hconjpow]
            _ = c * (h * x * h⁻¹) ^ e := by rw [← he]; group
      interval_cases e
      · exfalso
        apply hcX
        have h1 : h⁻¹ * c * h ∈ X := by rw [he, pow_zero, one_mul]; exact hy₁
        have h2 := hXW h hh _ h1
        rwa [show h * (h⁻¹ * c * h) * h⁻¹ = c by group] at h2
      · simpa using hk'
      · have h1 := hTr_pow _ hk' (X.pow_mem hhxX 2) 2
        rwa [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hX3 _ hhxX, one_mul] at h1
    set x₀ := c⁻¹ * (k₀ * c * k₀⁻¹) with hx₀
    have hTrx₀ : Tr x₀ := ⟨k₀, hk₀W, hk₀X, by rw [hx₀]; group⟩
    have hx₀1 : x₀ ≠ 1 := fun h => hk₀ne (by rw [hx₀, inv_mul_eq_one] at h; exact h.symm)
    have hTrd : Tr d := by
      by_cases hx₀d : x₀ ∈ Subgroup.zpowers d
      · have hZ : Subgroup.zpowers x₀ = Subgroup.zpowers d :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx₀d)
            (by rw [hZd, Nat.card_zpowers, orderOf_eq_prime (hX3 x₀ hk₀c) hx₀1])
        exact hTr_zpowers x₀ hTrx₀ hk₀c d (hZ ▸ Subgroup.mem_zpowers d)
      · set δ := x₀⁻¹ * (w * x₀ * w⁻¹) with hδ
        have hδd : δ ∈ Subgroup.zpowers d := hwA x₀ (hXA hk₀c)
        have hδ1 : δ ≠ 1 := by
          intro h1
          have hwx₀ : w * x₀ * w⁻¹ = x₀ := by
            rw [hδ, inv_mul_eq_one] at h1
            exact h1.symm
          have hdecX' := Item21LateProof.exists_pow_mul_of_card hXc hX3 hdXle (by rw [hX, hZd])
            hk₀c hx₀d
          obtain ⟨a, ha, hne⟩ := hwmove
          apply hne
          refine conj_eq_of_fix hcomm h3 hXA hAX hcA hcX ?_ hwc a ha
          intro x hx
          obtain ⟨j, -, y, hy', rfl⟩ := hdecX' x hx
          rw [hconj, hconjpow, hwx₀, Item21LateProof.conj_eq_of_mem_zpowers hwd hy']
        have hTrδ : Tr δ := hTr_mul _ _ (hTr_inv x₀ hTrx₀ hk₀c)
          (hTr_conj x₀ hTrx₀ hk₀c w hwW) (hXW w hwW x₀ hk₀c)
        have hZ : Subgroup.zpowers δ = Subgroup.zpowers d :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hδd)
            (by rw [hZd, Nat.card_zpowers, orderOf_eq_prime (hX3 δ (hdXle hδd)) hδ1])
        exact hTr_zpowers δ hTrδ (hdXle hδd) d (hZ ▸ Subgroup.mem_zpowers d)
    have hTrd' : Tr d' := hTr_conj d hTrd hdX g hgW
    have hTrX : ∀ x ∈ X, Tr x := by
      intro x hx
      obtain ⟨j, -, y, hy, rfl⟩ := hdecX x hx
      exact hTr_mul _ _ (hTr_pow d' hTrd' hd'X j) (hTr_zpowers d hTrd hdX y hy) (hdXle hy)
    set x_u := c⁻¹ * (u * c * u⁻¹) with hxu
    have hxuX : x_u ∈ X := huAX c hcA
    obtain ⟨τ, hτW, hτX, hτc⟩ := hTrX _ (X.inv_mem hxuX)
    have hτuc : (τ * u) * c * (τ * u)⁻¹ = c := by
      have h1 : u * c * u⁻¹ = c * x_u := by rw [hxu]; group
      calc (τ * u) * c * (τ * u)⁻¹ = τ * (u * c * u⁻¹) * τ⁻¹ := by group
        _ = (τ * c * τ⁻¹) * (τ * x_u * τ⁻¹) := by rw [h1, hconj]
        _ = c := by rw [hτc, hτX x_u hxuX]; group
    have h1 := hH (τ * u) (W.mul_mem hτW huW) (by rw [hτuc]; exact Subgroup.mem_zpowers c)
    have hudX : u * d * u⁻¹ ∈ X := hXW u huW d hdX
    have e1 : (τ * u) * d * (τ * u)⁻¹ = u * d * u⁻¹ := by
      calc (τ * u) * d * (τ * u)⁻¹ = τ * (u * d * u⁻¹) * τ⁻¹ := by group
        _ = u * d * u⁻¹ := hτX _ hudX
    rw [e1] at h1
    have hδ'd' : d⁻¹ * (u * d * u⁻¹) ∈ Subgroup.zpowers d' := huA d (hXA hdX)
    have hδ'd : d⁻¹ * (u * d * u⁻¹) ∈ Subgroup.zpowers d :=
      (Subgroup.zpowers d).mul_mem ((Subgroup.zpowers d).inv_mem (Subgroup.mem_zpowers d)) h1
    have hδ'1 := eq_one_of_pow_mem hd'3 hgd hδ'd' hδ'd
    apply hud
    rw [inv_mul_eq_one] at hδ'1
    exact hδ'1.symm
  ·
    push Not at hcase
    have hzinv' : ∀ y ∈ X, z⁻¹ * y * z = y⁻¹ := by
      intro y hy
      have hy' : z⁻¹ * y * z ∈ X := hWinvX z hzW y hy
      have h1 := hzinv _ hy'
      rw [show z * (z⁻¹ * y * z) * z⁻¹ = y by group] at h1
      have h2 := congrArg (·⁻¹) h1
      simp only [inv_inv] at h2
      exact h2.symm
    have hcomz : ∀ h ∈ W, ∀ b ∈ A, (h * z * h⁻¹) * b * (h * z * h⁻¹)⁻¹ = z * b * z⁻¹ := by
      intro h hh b hb
      have hhzW : h * z * h⁻¹ ∈ W := W.mul_mem (W.mul_mem hh hzW) (hWinv h hh)
      have hkW : h * z * h⁻¹ * z⁻¹ ∈ W := W.mul_mem hhzW (hWinv z hzW)
      have hkX : ∀ y ∈ X, (h * z * h⁻¹ * z⁻¹) * y * (h * z * h⁻¹ * z⁻¹)⁻¹ = y := by
        intro y hy
        have hy1 : h⁻¹ * y⁻¹ * h ∈ X := hWinvX h hh _ (X.inv_mem hy)
        calc (h * z * h⁻¹ * z⁻¹) * y * (h * z * h⁻¹ * z⁻¹)⁻¹ =
            h * (z * (h⁻¹ * (z⁻¹ * y * z) * h) * z⁻¹) * h⁻¹ := by group
          _ = h * (z * (h⁻¹ * y⁻¹ * h) * z⁻¹) * h⁻¹ := by rw [hzinv' y hy]
          _ = h * (h⁻¹ * y⁻¹ * h)⁻¹ * h⁻¹ := by rw [hzinv _ hy1]
          _ = y := by group
      have hhzAX : ∀ a ∈ A, a⁻¹ * ((h * z * h⁻¹) * a * (h * z * h⁻¹)⁻¹) ∈ X := by
        intro a ha
        have h1 := hzAX _ (hWinvA h hh a ha)
        have e : a⁻¹ * ((h * z * h⁻¹) * a * (h * z * h⁻¹)⁻¹) =
            h * ((h⁻¹ * a * h)⁻¹ * (z * (h⁻¹ * a * h) * z⁻¹)) * h⁻¹ := by group
        rw [e]
        exact hXW h hh _ h1
      have hzinvAX : ∀ a ∈ A, a⁻¹ * (z⁻¹ * a * z⁻¹⁻¹) ∈ X := by
        intro a ha
        have h1 := hzAX _ (hWinvA z hzW a ha)
        rw [show z * (z⁻¹ * a * z) * z⁻¹ = a by group] at h1
        have e : a⁻¹ * (z⁻¹ * a * z⁻¹⁻¹) = ((z⁻¹ * a * z)⁻¹ * a)⁻¹ := by group
        rw [e]
        exact X.inv_mem h1
      have hkAX := Item21LateProof.inv_mul_conj_mul_mem (hXW _ hhzW) hhzAX hzinvAX
      have hkc : (h * z * h⁻¹ * z⁻¹) * c * (h * z * h⁻¹ * z⁻¹)⁻¹ = c :=
        hcase _ hkW hkX (hkAX c hcA)
      have hkfix := conj_eq_of_fix hcomm h3 hXA hAX hcA hcX hkX hkc
      have h1 := hkfix (z * b * z⁻¹) (hWA z hzW b hb)
      calc (h * z * h⁻¹) * b * (h * z * h⁻¹)⁻¹ =
          (h * z * h⁻¹ * z⁻¹) * (z * b * z⁻¹) * (h * z * h⁻¹ * z⁻¹)⁻¹ := by group
        _ = z * b * z⁻¹ := h1
    set x_z := c⁻¹ * (z * c * z⁻¹) with hxz
    have hxzX : x_z ∈ X := hzAX c hcA
    have hxz3 : x_z ^ 3 = 1 := hX3 x_z hxzX
    set c₀ := c * x_z⁻¹ with hc₀
    have hc₀A : c₀ ∈ A := A.mul_mem hcA (A.inv_mem (hXA hxzX))
    have hc₀X : c₀ ∉ X := fun h => hcX (by
      have h1 := X.mul_mem h hxzX
      rwa [hc₀, inv_mul_cancel_right] at h1)
    have hc₀3 : c₀ ^ 3 = 1 := h3 c₀ hc₀A
    have hzc₀ : z * c₀ * z⁻¹ = c₀ := by
      have h1 : z * c * z⁻¹ = c * x_z := by rw [hxz]; group
      have h2 : z * x_z⁻¹ * z⁻¹ = x_z := by
        rw [show z * x_z⁻¹ * z⁻¹ = (z * x_z * z⁻¹)⁻¹ by group, hzinv x_z hxzX, inv_inv]
      rw [hc₀, hconj, h1, h2, mul_assoc, ← pow_two,
        Item21LateProof.sq_eq_inv_of_pow_three hxz3]
    have hdecA₀ := Item21LateProof.exists_pow_mul_of_card hcomm h3 hXA hAX hc₀A hc₀X
    have hfixz : ∀ a ∈ A, z * a * z⁻¹ = a → a ∈ Subgroup.zpowers c₀ := by
      intro a ha hza
      obtain ⟨j, -, y, hy, rfl⟩ := hdecA₀ a ha
      rw [hconj, hconjpow, hzc₀, hzinv y hy] at hza
      have hyy : y⁻¹ = y := mul_left_cancel hza
      rw [eq_one_of_inv_eq (hX3 y hy) hyy, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c₀) j
    have hWc₀ : ∀ h ∈ W, h * c₀ * h⁻¹ ∈ Subgroup.zpowers c₀ := by
      intro h hh
      refine hfixz _ (hWA h hh c₀ hc₀A) ?_
      rw [← hcomz h hh _ (hWA h hh c₀ hc₀A)]
      calc (h * z * h⁻¹) * (h * c₀ * h⁻¹) * (h * z * h⁻¹)⁻¹ = h * (z * c₀ * z⁻¹) * h⁻¹ := by
            group
        _ = h * c₀ * h⁻¹ := by rw [hzc₀]
    have hzc₀mem : ∀ x : G, x ∈ Subgroup.zpowers c₀ → c₀⁻¹ * x ∈ Subgroup.zpowers c₀ :=
      fun x hx => (Subgroup.zpowers c₀).mul_mem
        ((Subgroup.zpowers c₀).inv_mem (Subgroup.mem_zpowers c₀)) hx
    have hwc₀ : w * c₀ * w⁻¹ = c₀ := by
      have h4 := eq_one_of_pow_mem hc₀3 hc₀X (hzc₀mem _ (hWc₀ w hwW)) (hdXle (hwA c₀ hc₀A))
      rw [inv_mul_eq_one] at h4
      exact h4.symm
    have hwy : w * x_z⁻¹ * w⁻¹ = x_z⁻¹ := by
      have e : x_z⁻¹ = c⁻¹ * c₀ := by rw [hc₀]; group
      rw [e, hconj, show w * c⁻¹ * w⁻¹ = (w * c * w⁻¹)⁻¹ by group, hwc, hwc₀]
    have hyd : x_z⁻¹ ∈ Subgroup.zpowers d := by
      by_contra hy
      have hdecX' := Item21LateProof.exists_pow_mul_of_card hXc hX3 hdXle (by rw [hX, hZd])
        (X.inv_mem hxzX) hy
      obtain ⟨a, ha, hne⟩ := hwmove
      apply hne
      refine conj_eq_of_fix hcomm h3 hXA hAX hcA hcX ?_ hwc a ha
      intro x hx
      obtain ⟨j, -, y, hy', rfl⟩ := hdecX' x hx
      rw [hconj, hconjpow, hwy, Item21LateProof.conj_eq_of_mem_zpowers hwd hy']
    have hty : t * x_z⁻¹ * t⁻¹ = (x_z⁻¹)⁻¹ := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyd
      rw [← hj, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htd, inv_zpow]
    have hxz1 : x_z = 1 := by
      have e1 : c₀⁻¹ * (t * c₀ * t⁻¹) = x_z * x_z := by
        rw [hc₀, hconj, htc, hty, inv_inv]
        group
      have h2 := eq_one_of_pow_mem hc₀3 hc₀X (hzc₀mem _ (hWc₀ t htW))
        (by rw [e1]; exact X.mul_mem hxzX hxzX)
      rw [e1] at h2
      calc x_z = x_z ^ 3 * (x_z * x_z)⁻¹ := by rw [pow_three]; group
        _ = 1 := by rw [hxz3, h2]; group
    have hc₀c : c₀ = c := by rw [hc₀, hxz1, inv_one, mul_one]
    have h1 := hWc₀ g hgW
    rw [hc₀c] at h1
    exact hgd (hH g hgW h1)

end Pure

end CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

theorem item2121_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2121 := by
  intro G _ _ A E U c L hcfg d hdB hd1 hdT ⟨g, hgW, hgd⟩ X hXA hXW hX9 hdX hcX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, d₀, -, hd₀1, -, hTU, -, hHd, -, ⟨w, ⟨hwL, hwN⟩, -, hwd, hwA, hwmove⟩, t,
    ⟨htL, htN⟩, htd⟩ := Item21Late2Proof.frame_of h45 h66 hcfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A c hpairs.2.2.1)
  have hfixc : ∀ {y : G}, y ∈ L → y * c * y⁻¹ = c := fun hy => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hy), mul_inv_cancel_right]
  have hdd₀ : d ∈ Subgroup.zpowers d₀ ∧ d₀ ∈ Subgroup.zpowers d := by
    rcases hTU d hdB hd1 hdT with rfl | rfl
    · exact ⟨Subgroup.mem_zpowers _, Subgroup.mem_zpowers _⟩
    · refine ⟨(Subgroup.zpowers d₀).inv_mem (Subgroup.mem_zpowers _), ?_⟩
      have h1 := (Subgroup.zpowers d₀⁻¹).inv_mem (Subgroup.mem_zpowers d₀⁻¹)
      rwa [inv_inv] at h1
  have hZ : Subgroup.zpowers d = Subgroup.zpowers d₀ :=
    le_antisymm (Subgroup.zpowers_le.mpr hdd₀.1) (Subgroup.zpowers_le.mpr hdd₀.2)
  have hd₀X : d₀ ∈ X := (Subgroup.zpowers_le.mpr hdX) hdd₀.2
  have hgd₀ : g * d₀ * g⁻¹ ∉ Subgroup.zpowers d₀ := by
    intro h
    apply hgd
    rw [hZ]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdd₀.1
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact (Subgroup.zpowers d₀).zpow_mem h k
  have hH : ∀ h ∈ Subgroup.normalizer (A : Set G), h * c * h⁻¹ ∈ Subgroup.zpowers c →
      h * d₀ * h⁻¹ ∈ Subgroup.zpowers d₀ := by
    intro h hhW hhc
    have hhN : h ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      exact (Subgroup.zpowers c).zpow_mem hhc k
    rcases hHd h ⟨hhN, hhW⟩ with h1 | h1
    · rw [h1]
      exact Subgroup.mem_zpowers d₀
    · rw [h1]
      exact (Subgroup.zpowers d₀).inv_mem (Subgroup.mem_zpowers d₀)
  exact Item21Late2Proof.false_of_invariant_nine hcomm h3 hA27 hXA hX9 hXW hcA hcX hd₀X hd₀1
    hwN (hfixc hwL) hwd hwA hwmove htN (hfixc htL) htd hgW hgd₀ hH

end CFSG.RankThree.PartTwo.Sec21
