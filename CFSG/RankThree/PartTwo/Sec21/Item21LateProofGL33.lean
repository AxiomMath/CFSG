module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21LateProof

variable {G : Type*} [Group G]

theorem pow_eq_pow_mod_three {x : G} (hx : x ^ 3 = 1) (k : ℕ) : x ^ k = x ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

theorem exists_pow_lt_three_of_mem_zpowers {h x : G} (hh : h ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers h) : ∃ k : ℕ, k < 3 ∧ x = h ^ k := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h1 : h ^ k = h ^ (k % 3) := zpow_eq_zpow_emod' k hh
  rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]

theorem exists_pow_mul_of_card [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h3 : ∀ x ∈ H, x ^ 3 = 1) (hKH : K ≤ H)
    (hcard : Nat.card H = 3 * Nat.card K) {h₀ : G} (h₀H : h₀ ∈ H) (h₀K : h₀ ∉ K) :
    ∀ h ∈ H, ∃ k : ℕ, k < 3 ∧ ∃ y ∈ K, h = h₀ ^ k * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZH : Subgroup.zpowers h₀ ≤ H := Subgroup.zpowers_le.mpr h₀H
  have hc : ∀ x ∈ Subgroup.zpowers h₀, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    hcomm x (hZH hx) y (hKH hy)
  obtain ⟨hcd, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc
  have h₀1 : h₀ ≠ 1 := fun h => h₀K (h ▸ K.one_mem)
  have hZ3 : Nat.card (Subgroup.zpowers h₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h3 h₀ h₀H) h₀1]
  have hinf : Nat.card (Subgroup.zpowers h₀ ⊓ K : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers h₀ ⊓ K : Subgroup G) ∣ 3 :=
      hZ3 ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers h₀ ⊓ K = Subgroup.zpowers h₀ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZ3, h])
      have hmem : h₀ ∈ Subgroup.zpowers h₀ ⊓ K := by
        rw [heq]
        exact Subgroup.mem_zpowers h₀
      exact h₀K hmem.2
  rw [hinf, mul_one, hZ3, ← hcard] at hcd
  have hsup : Subgroup.zpowers h₀ ⊔ K = H :=
    Subgroup.eq_of_le_of_card_ge (sup_le hZH hKH) hcd.ge
  intro h hh
  rw [← hsup] at hh
  have hh' : h ∈ ((Subgroup.zpowers h₀ ⊔ K : Subgroup G) : Set G) := hh
  rw [hset] at hh'
  obtain ⟨x, hx, y, hy, rfl⟩ := hh'
  obtain ⟨k, hk, rfl⟩ := exists_pow_lt_three_of_mem_zpowers (h3 h₀ h₀H) hx
  exact ⟨k, hk, y, hy, rfl⟩

theorem inv_mul_conj_mem_of_pow_three [Finite G] {H K : Subgroup G}
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (h3 : ∀ x ∈ H, x ^ 3 = 1) (hKH : K ≤ H)
    (hcard : Nat.card H = 3 * Nat.card K) {w : G} (hwH : ∀ h ∈ H, w * h * w⁻¹ ∈ H)
    (hwK : ∀ y ∈ K, w * y * w⁻¹ ∈ K) (hw3 : ∀ h ∈ H, w ^ 3 * h * (w ^ 3)⁻¹ = h) :
    ∀ h ∈ H, h⁻¹ * (w * h * w⁻¹) ∈ K := by
  obtain ⟨h₀, h₀H, h₀K⟩ : ∃ h₀ ∈ H, h₀ ∉ K := by
    by_contra hno
    push Not at hno
    have hle : Nat.card H ≤ Nat.card K := Subgroup.card_le_of_le fun x hx => hno x hx
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega
  have hdec := exists_pow_mul_of_card hcomm h3 hKH hcard h₀H h₀K
  have hwK' : ∀ y ∈ K, w⁻¹ * y * w ∈ K := by
    intro y hy
    have e : w⁻¹ * y * w = w * (w * y * w⁻¹) * w⁻¹ := by
      have h1 := hw3 y (hKH hy)
      calc w⁻¹ * y * w = w⁻¹ * (w ^ 3 * y * (w ^ 3)⁻¹) * w := by rw [h1]
        _ = w * (w * y * w⁻¹) * w⁻¹ := by rw [pow_succ' w 2, pow_two]; group
    rw [e]
    exact hwK _ (hwK y hy)
  have hconj : ∀ x y : G, w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := fun x y => by
    group
  have hconjpow : ∀ (x : G) (k : ℕ), w * x ^ k * w⁻¹ = (w * x * w⁻¹) ^ k := fun x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have h₀3 : h₀ ^ 3 = 1 := h3 h₀ h₀H
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ ∈ K, w * h₀ * w⁻¹ = h₀ * y₀ := by
    obtain ⟨k, hk, y, hyK, hy⟩ := hdec _ (hwH h₀ h₀H)
    interval_cases k
    · exfalso
      rw [pow_zero, one_mul] at hy
      apply h₀K
      have e : h₀ = w⁻¹ * (w * h₀ * w⁻¹) * w := by group
      rw [e, hy]
      exact hwK' y hyK
    · exact ⟨y, hyK, by rw [hy, pow_one]⟩
    · exfalso
      have hyH : y ∈ H := hKH hyK
      set y₁ := w * y * w⁻¹ with hy₁
      have hy₁K : y₁ ∈ K := hwK y hyK
      have e2 : w ^ 2 * h₀ * (w ^ 2)⁻¹ = h₀ * (y ^ 2 * y₁) := by
        calc w ^ 2 * h₀ * (w ^ 2)⁻¹ = w * (w * h₀ * w⁻¹) * w⁻¹ := by rw [pow_two]; group
          _ = w * (h₀ ^ 2 * y) * w⁻¹ := by rw [hy]
          _ = (w * h₀ * w⁻¹) ^ 2 * y₁ := by rw [hconj, hconjpow]
          _ = (h₀ ^ 2 * y) ^ 2 * y₁ := by rw [hy]
          _ = h₀ ^ 4 * y ^ 2 * y₁ := by
              rw [(Commute.mul_pow (hcomm _ (H.pow_mem h₀H 2) _ hyH) 2), ← pow_mul]
          _ = h₀ * (y ^ 2 * y₁) := by
              rw [show 4 = 3 + 1 by norm_num, pow_succ, h₀3, one_mul, mul_assoc]
      have e3 : w ^ 3 * h₀ * (w ^ 3)⁻¹ = h₀ ^ 2 * (y * (w * (y ^ 2 * y₁) * w⁻¹)) := by
        calc w ^ 3 * h₀ * (w ^ 3)⁻¹ = w * (w ^ 2 * h₀ * (w ^ 2)⁻¹) * w⁻¹ := by
              rw [pow_succ' w 2]; group
          _ = (w * h₀ * w⁻¹) * (w * (y ^ 2 * y₁) * w⁻¹) := by rw [e2, hconj]
          _ = h₀ ^ 2 * (y * (w * (y ^ 2 * y₁) * w⁻¹)) := by rw [hy, mul_assoc]
      have hzK : y * (w * (y ^ 2 * y₁) * w⁻¹) ∈ K :=
        K.mul_mem hyK (hwK _ (K.mul_mem (K.pow_mem hyK 2) hy₁K))
      rw [hw3 h₀ h₀H] at e3
      apply h₀K
      have e4 : h₀ = (y * (w * (y ^ 2 * y₁) * w⁻¹))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc h₀ * (y * (w * (y ^ 2 * y₁) * w⁻¹)) =
            h₀⁻¹ * (h₀ ^ 2 * (y * (w * (y ^ 2 * y₁) * w⁻¹))) := by
              rw [pow_two]
              group
          _ = h₀⁻¹ * h₀ := by rw [← e3]
          _ = 1 := inv_mul_cancel h₀
      rw [e4]
      exact K.inv_mem hzK
  intro h hh
  obtain ⟨k, -, y, hyK, rfl⟩ := hdec h hh
  have hyH : y ∈ H := hKH hyK
  have hy₀H : y₀ ∈ H := hKH hy₀K
  rw [hconj, hconjpow, hy₀, Commute.mul_pow (hcomm _ h₀H _ hy₀H), mul_inv_rev]
  have e : y⁻¹ * (h₀ ^ k)⁻¹ * (h₀ ^ k * y₀ ^ k * (w * y * w⁻¹)) =
      y⁻¹ * (y₀ ^ k * (w * y * w⁻¹)) := by group
  rw [e]
  exact K.mul_mem (K.inv_mem hyK) (K.mul_mem (K.pow_mem hy₀K k) (hwK y hyK))

theorem inv_mul_conj_mul_mem {A B : Subgroup G} {g h : G} (hgB : ∀ y ∈ B, g * y * g⁻¹ ∈ B)
    (hg : ∀ a ∈ A, a⁻¹ * (g * a * g⁻¹) ∈ B) (hh : ∀ a ∈ A, a⁻¹ * (h * a * h⁻¹) ∈ B) :
    ∀ a ∈ A, a⁻¹ * (g * h * a * (g * h)⁻¹) ∈ B := by
  intro a ha
  have e : a⁻¹ * (g * h * a * (g * h)⁻¹) =
      (a⁻¹ * (g * a * g⁻¹)) * (g * (a⁻¹ * (h * a * h⁻¹)) * g⁻¹) := by group
  rw [e]
  exact B.mul_mem (hg a ha) (hgB _ (hh a ha))

theorem conj_eq_of_mem_zpowers {g c : G} (hgc : g * c * g⁻¹ = c) {y : G}
    (hy : y ∈ Subgroup.zpowers c) : g * y * g⁻¹ = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hgc]

theorem transvection_of_inverting [Finite G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1) (hBA : B ≤ A)
    (hAB : Nat.card A = 3 * Nat.card B) {c : G} (hcB : c ∈ B) {w t : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwB : w ∈ Subgroup.normalizer (B : Set G))
    (hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) (hwc : w * c * w⁻¹ = c)
    (hwBc : ∀ y ∈ B, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers c)
    (hwAB : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ B) (htinv : ∀ y ∈ B, t * y * t⁻¹ = y⁻¹)
    (htAB : ∀ a ∈ A, a⁻¹ * (t * a * t⁻¹) ∈ B) :
    (∀ y ∈ B, (w ^ 2 * t * w⁻¹ * t) * y * (w ^ 2 * t * w⁻¹ * t)⁻¹ = w * y * w⁻¹) ∧
      ∀ a ∈ A, a⁻¹ * ((w ^ 2 * t * w⁻¹ * t) * a * (w ^ 2 * t * w⁻¹ * t)⁻¹) ∈
        Subgroup.zpowers c := by
  have hxconj : ∀ g : G, (w ^ 2 * t * w⁻¹ * t) * g * (w ^ 2 * t * w⁻¹ * t)⁻¹ =
      w * (w * (t * (w⁻¹ * (t * g * t⁻¹) * w) * t⁻¹) * w⁻¹) * w⁻¹ := by
    intro g
    rw [pow_two]
    group
  have hconj : ∀ g x y : G, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by
    group
  have hconjinv : ∀ g x : G, g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := fun g x => by group
  have nA : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) → ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun hg a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have nB : ∀ {g : G}, g ∈ Subgroup.normalizer (B : Set G) → ∀ y ∈ B, g * y * g⁻¹ ∈ B :=
    fun hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have nBinv : ∀ y ∈ B, w⁻¹ * y * w ∈ B := by
    intro y hy
    have h := nB ((Subgroup.normalizer (B : Set G)).inv_mem hwB) y hy
    rwa [inv_inv] at h
  have nAinv : ∀ a ∈ A, w⁻¹ * a * w ∈ A := by
    intro a ha
    have h := nA ((Subgroup.normalizer (A : Set G)).inv_mem hwA) a ha
    rwa [inv_inv] at h
  have hB : ∀ y ∈ B, (w ^ 2 * t * w⁻¹ * t) * y * (w ^ 2 * t * w⁻¹ * t)⁻¹ = w * y * w⁻¹ := by
    intro y hy
    have e1 : w⁻¹ * y⁻¹ * w = (w⁻¹ * y * w)⁻¹ := by group
    rw [hxconj, htinv y hy, e1, hconjinv t, htinv _ (nBinv y hy), inv_inv]
    group
  refine ⟨hB, ?_⟩
  obtain ⟨e, heA, heB⟩ : ∃ e ∈ A, e ∉ B := by
    by_contra hno
    push Not at hno
    have hle : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le fun x hx => hno x hx
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  set v₀ := e⁻¹ * (t * e * t⁻¹) with hv₀
  have hv₀B : v₀ ∈ B := htAB e heA
  have hv₀A : v₀ ∈ A := hBA hv₀B
  have hv₀3 : v₀ ^ 3 = 1 := h3 v₀ hv₀A
  set e₀ := e * v₀ ^ 2 with he₀
  have he₀A : e₀ ∈ A := A.mul_mem heA (A.pow_mem hv₀A 2)
  have he₀B : e₀ ∉ B := by
    intro h
    apply heB
    have e' : e = e₀ * (v₀ ^ 2)⁻¹ := by rw [he₀, mul_inv_cancel_right]
    rw [e']
    exact B.mul_mem h (B.inv_mem (B.pow_mem hv₀B 2))
  have hte : t * e * t⁻¹ = e * v₀ := by rw [hv₀, mul_inv_cancel_left]
  have hte₀ : t * e₀ * t⁻¹ = e₀ := by
    rw [he₀, hconj, hte, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, htinv v₀ hv₀B]
    have hinv : v₀⁻¹ = v₀ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hv₀3]
    rw [inv_pow, mul_assoc, show v₀ * (v₀ ^ 2)⁻¹ = v₀⁻¹ by rw [pow_two]; group, hinv]
  set u₀ := e₀⁻¹ * (w⁻¹ * e₀ * w) with hu₀
  have hu₀B : u₀ ∈ B := by
    have h := hwAB _ (nAinv e₀ he₀A)
    have e' : (w⁻¹ * e₀ * w)⁻¹ * (w * (w⁻¹ * e₀ * w) * w⁻¹) = u₀⁻¹ := by
      rw [hu₀]
      group
    rw [e'] at h
    simpa using B.inv_mem h
  have hwe₀ : w⁻¹ * e₀ * w = e₀ * u₀ := by rw [hu₀, mul_inv_cancel_left]
  set d₁ := u₀⁻¹ * (w * u₀ * w⁻¹) with hd₁
  have hd₁c : d₁ ∈ Subgroup.zpowers c := hwBc u₀ hu₀B
  have hwu₀ : w * u₀ * w⁻¹ = u₀ * d₁ := by rw [hd₁, mul_inv_cancel_left]
  have hwd₁ : w * d₁ * w⁻¹ = d₁ := conj_eq_of_mem_zpowers hwc hd₁c
  have hw2e₀ : w * (w * e₀ * w⁻¹) * w⁻¹ = e₀ * u₀ := by
    have h1 := hw3 e₀ he₀A
    calc w * (w * e₀ * w⁻¹) * w⁻¹ = w⁻¹ * (w ^ 3 * e₀ * (w ^ 3)⁻¹) * w := by
          rw [pow_succ' w 2, pow_two]
          group
      _ = e₀ * u₀ := by rw [h1, hwe₀]
  have hxe₀ : (w ^ 2 * t * w⁻¹ * t) * e₀ * (w ^ 2 * t * w⁻¹ * t)⁻¹ =
      e₀ * u₀ * (u₀ * d₁ * d₁)⁻¹ := by
    calc (w ^ 2 * t * w⁻¹ * t) * e₀ * (w ^ 2 * t * w⁻¹ * t)⁻¹ =
        w * (w * (t * (w⁻¹ * (t * e₀ * t⁻¹) * w) * t⁻¹) * w⁻¹) * w⁻¹ := hxconj e₀
      _ = w * (w * (t * (e₀ * u₀) * t⁻¹) * w⁻¹) * w⁻¹ := by rw [hte₀, hwe₀]
      _ = w * (w * (e₀ * u₀⁻¹) * w⁻¹) * w⁻¹ := by rw [hconj t, hte₀, htinv u₀ hu₀B]
      _ = (w * (w * e₀ * w⁻¹) * w⁻¹) * (w * (w * u₀ * w⁻¹) * w⁻¹)⁻¹ := by group
      _ = (e₀ * u₀) * (w * (u₀ * d₁) * w⁻¹)⁻¹ := by rw [hw2e₀, hwu₀]
      _ = e₀ * u₀ * (u₀ * d₁ * d₁)⁻¹ := by rw [hconj, hwu₀, hwd₁]
  have hZA : ∀ z ∈ Subgroup.zpowers c, z ∈ A := fun z hz =>
    hBA ((Subgroup.zpowers_le.mpr hcB) hz)
  have hd₁A : d₁ ∈ A := hZA d₁ hd₁c
  have hu₀A : u₀ ∈ A := hBA hu₀B
  set f₀ := (d₁ * d₁)⁻¹ with hf₀
  have hf₀c : f₀ ∈ Subgroup.zpowers c :=
    (Subgroup.zpowers c).inv_mem ((Subgroup.zpowers c).mul_mem hd₁c hd₁c)
  have hf₀A : f₀ ∈ A := hZA f₀ hf₀c
  have hxe : (w ^ 2 * t * w⁻¹ * t) * e₀ * (w ^ 2 * t * w⁻¹ * t)⁻¹ = e₀ * f₀ := by
    rw [hxe₀, hf₀]
    have hcu : u₀ * d₁ * d₁ = d₁ * d₁ * u₀ := by
      rw [mul_assoc]
      exact hcomm u₀ hu₀A _ (A.mul_mem hd₁A hd₁A)
    rw [hcu, mul_inv_rev, ← mul_assoc, mul_assoc e₀, mul_inv_cancel, mul_one]
  intro a ha
  obtain ⟨k, -, y, hyB, rfl⟩ :=
    exists_pow_mul_of_card hcomm h3 hBA hAB he₀A he₀B a ha
  have hyA : y ∈ A := hBA hyB
  have hconjpow : ∀ (g z : G) (k : ℕ), g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := fun g z k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  rw [hconj, hconjpow, hxe, hB y hyB, Commute.mul_pow (hcomm e₀ he₀A f₀ hf₀A)]
  have hyf : y⁻¹ * f₀ ^ k = f₀ ^ k * y⁻¹ :=
    hcomm _ (A.inv_mem hyA) _ (A.pow_mem hf₀A k)
  have e' : (e₀ ^ k * y)⁻¹ * (e₀ ^ k * f₀ ^ k * (w * y * w⁻¹)) =
      f₀ ^ k * (y⁻¹ * (w * y * w⁻¹)) := by
    have e1 : (e₀ ^ k * y)⁻¹ * (e₀ ^ k * f₀ ^ k * (w * y * w⁻¹)) =
        y⁻¹ * f₀ ^ k * (w * y * w⁻¹) := by group
    rw [e1, hyf, mul_assoc]
  rw [e']
  exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).pow_mem hf₀c k) (hwBc y hyB)

section Rho

variable {c d : G}

theorem pow_mul_pow_mul_pow_mul_pow (hcd : Commute c d) (a b a' b' : ℕ) :
    c ^ a * d ^ b * (c ^ a' * d ^ b') = c ^ (a + a') * d ^ (b + b') := by
  have h : d ^ b * c ^ a' = c ^ a' * d ^ b := (hcd.symm.pow_pow b a').eq
  calc c ^ a * d ^ b * (c ^ a' * d ^ b') = c ^ a * (d ^ b * c ^ a') * d ^ b' := by
        simp only [mul_assoc]
    _ = c ^ a * (c ^ a' * d ^ b) * d ^ b' := by rw [h]
    _ = c ^ (a + a') * d ^ (b + b') := by simp only [pow_add, mul_assoc]

theorem pow_mul_pow_pow (hcd : Commute c d) (a b k : ℕ) :
    (c ^ a * d ^ b) ^ k = c ^ (a * k) * d ^ (b * k) := by
  rw [(hcd.pow_pow a b).mul_pow, pow_mul, pow_mul]

theorem pow_mul_pow_mod (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (a b : ℕ) :
    c ^ a * d ^ b = c ^ (a % 3) * d ^ (b % 3) := by
  rw [pow_eq_pow_mod_three hc3 a, pow_eq_pow_mod_three hd3 b]

theorem sq_eq_inv_of_pow_three {x : G} (hx : x ^ 3 = 1) : x ^ 2 = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx]

end Rho

theorem conj_sq_eq_inv [Finite G] {B : Subgroup G} (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h3 : ∀ x ∈ B, x ^ 3 = 1) (hB : Nat.card B = 9) {c d : G} (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hdB : d ∈ B) (hdc : d ∉ Subgroup.zpowers c) {w v : G} (hwc : w * c * w⁻¹ = c)
    (hwd : w * d * w⁻¹ = d * c) (hvd : v * d * v⁻¹ = d) (hvc : v * c * v⁻¹ = c * d) :
    ∀ y ∈ B, (w * v * (w * v)) * y * (w * v * (w * v))⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcd : Commute c d := hcomm c hcB d hdB
  have hc3 : c ^ 3 = 1 := h3 c hcB
  have hd3 : d ^ 3 = 1 := h3 d hdB
  have hconj : ∀ g x y : G, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by
    group
  have hconjpow : ∀ (g x : G) (k : ℕ), g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun g x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have hφc : (w * v) * c * (w * v)⁻¹ = c ^ 2 * d ^ 1 := by
    calc (w * v) * c * (w * v)⁻¹ = w * (v * c * v⁻¹) * w⁻¹ := by group
      _ = c * (d * c) := by rw [hvc, hconj, hwc, hwd]
      _ = c ^ 2 * d ^ 1 := by rw [← hcd.eq, ← mul_assoc, ← pow_two, pow_one]
  have hφd : (w * v) * d * (w * v)⁻¹ = c ^ 1 * d ^ 1 := by
    calc (w * v) * d * (w * v)⁻¹ = w * (v * d * v⁻¹) * w⁻¹ := by group
      _ = d * c := by rw [hvd, hwd]
      _ = c ^ 1 * d ^ 1 := by rw [pow_one, pow_one, hcd.eq]
  have hφρ : ∀ a b : ℕ, (w * v) * (c ^ a * d ^ b) * (w * v)⁻¹ =
      c ^ (2 * a + b) * d ^ (a + b) := by
    intro a b
    rw [hconj, hconjpow, hconjpow, hφc, hφd, pow_mul_pow_pow hcd, pow_mul_pow_pow hcd,
      pow_mul_pow_mul_pow_mul_pow hcd]
    congr 2 <;> ring
  have htρ : ∀ a b : ℕ, (w * v * (w * v)) * (c ^ a * d ^ b) * (w * v * (w * v))⁻¹ =
      c ^ (5 * a + 3 * b) * d ^ (3 * a + 2 * b) := by
    intro a b
    have e : (w * v * (w * v)) * (c ^ a * d ^ b) * (w * v * (w * v))⁻¹ =
        (w * v) * ((w * v) * (c ^ a * d ^ b) * (w * v)⁻¹) * (w * v)⁻¹ := by group
    rw [e, hφρ, hφρ]
    congr 2 <;> ring
  have htc : (w * v * (w * v)) * c * (w * v * (w * v))⁻¹ = c⁻¹ := by
    have h := htρ 1 0
    rw [pow_one, pow_zero, mul_one] at h
    rw [h, pow_mul_pow_mod hc3 hd3]
    norm_num
    exact sq_eq_inv_of_pow_three hc3
  have htd : (w * v * (w * v)) * d * (w * v * (w * v))⁻¹ = d⁻¹ := by
    have h := htρ 0 1
    rw [pow_zero, one_mul, pow_one] at h
    rw [h, pow_mul_pow_mod hc3 hd3]
    norm_num
    exact sq_eq_inv_of_pow_three hd3
  intro y hy
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  obtain ⟨k, -, z, hz, rfl⟩ := exists_pow_mul_of_card hcomm h3 (Subgroup.zpowers_le.mpr hcB)
    (by rw [hB, hZc]) hdB hdc y hy
  obtain ⟨l, -, rfl⟩ := exists_pow_lt_three_of_mem_zpowers hc3 hz
  rw [hconj, hconjpow, hconjpow, htc, htd, inv_pow, inv_pow, mul_inv_rev]
  exact (hcd.symm.pow_pow k l).inv_inv.eq

theorem exists_normal_pair [Finite G] {B : Subgroup G}
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h3 : ∀ x ∈ B, x ^ 3 = 1) {c c' : G}
    (hcB : c ∈ B) (hc'B : c' ∈ B) (hc'c : c' ∉ Subgroup.zpowers c) {w w' : G}
    (hwBc : ∀ y ∈ B, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers c) (hwc' : w * c' * w⁻¹ ≠ c')
    (hw'c' : w' * c' * w'⁻¹ = c')
    (hw'Bc : ∀ y ∈ B, y⁻¹ * (w' * y * w'⁻¹) ∈ Subgroup.zpowers c') (hw'c : w' * c * w'⁻¹ ≠ c) :
    ∃ d ∈ B, d ∉ Subgroup.zpowers c ∧ w * d * w⁻¹ = d * c ∧
      ∃ v ∈ ({w', w' * w'} : Set G), v * d * v⁻¹ = d ∧ v * c * v⁻¹ = c * d := by
  have hc3 : c ^ 3 = 1 := h3 c hcB
  have hc'3 : c' ^ 3 = 1 := h3 c' hc'B
  have hcc' : Commute c c' := hcomm c hcB c' hc'B
  have hconj : ∀ g x y : G, g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := fun g x y => by
    group
  have hconjpow : ∀ (g x : G) (k : ℕ), g * x ^ k * g⁻¹ = (g * x * g⁻¹) ^ k := fun g x k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  obtain ⟨i, hi, hwi⟩ := exists_pow_lt_three_of_mem_zpowers hc3 (hwBc c' hc'B)
  obtain ⟨j, hj, hw'j⟩ := exists_pow_lt_three_of_mem_zpowers hc'3 (hw'Bc c hcB)
  have hwc'i : w * c' * w⁻¹ = c' * c ^ i := by rw [← hwi, mul_inv_cancel_left]
  have hw'cj : w' * c * w'⁻¹ = c * c' ^ j := by rw [← hw'j, mul_inv_cancel_left]
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hwc'i
    exact hwc' hwc'i
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hw'cj
    exact hw'c hw'cj
  have hw'2 : (w' * w') * c' * (w' * w')⁻¹ = c' := by
    calc (w' * w') * c' * (w' * w')⁻¹ = w' * (w' * c' * w'⁻¹) * w'⁻¹ := by group
      _ = c' := by rw [hw'c', hw'c']
  have hc'2c : c' ^ 2 ∉ Subgroup.zpowers c := by
    intro h
    apply hc'c
    have e : c' = (c' ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc'3, one_mul]
    rw [e]
    exact (Subgroup.zpowers c).pow_mem h 2
  have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
  have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
  interval_cases i <;> interval_cases j
  ·
    refine ⟨c', hc'B, hc'c, by rw [hwc'i, pow_one], w', Or.inl rfl, hw'c', ?_⟩
    rw [hw'cj, pow_one]
  ·
    refine ⟨c', hc'B, hc'c, by rw [hwc'i, pow_one], w' * w', Or.inr rfl, hw'2, ?_⟩
    calc (w' * w') * c * (w' * w')⁻¹ = w' * (w' * c * w'⁻¹) * w'⁻¹ := by group
      _ = c * c' ^ 4 := by
          rw [hw'cj, hconj, hconjpow, hw'cj, hw'c', mul_assoc, ← pow_add]
      _ = c * c' := by
          rw [show 4 = 3 + 1 by norm_num, pow_succ, hc'3, one_mul]
  ·
    refine ⟨c' ^ 2, B.pow_mem hc'B 2, hc'2c, ?_, w' * w', Or.inr rfl, ?_, ?_⟩
    · rw [hconjpow, hwc'i, (hcc'.symm.pow_right 2).mul_pow, ← pow_mul,
        show 2 * 2 = 3 + 1 by norm_num, pow_succ c, hc3, one_mul]
    · rw [hconjpow, hw'2]
    · calc (w' * w') * c * (w' * w')⁻¹ = w' * (w' * c * w'⁻¹) * w'⁻¹ := by group
        _ = c * c' ^ 2 := by
            rw [hw'cj, hconj, hw'cj, hconjpow, hw'c', pow_one, mul_assoc, ← pow_two]
  ·
    refine ⟨c' ^ 2, B.pow_mem hc'B 2, hc'2c, ?_, w', Or.inl rfl, ?_, hw'cj⟩
    · rw [hconjpow, hwc'i, (hcc'.symm.pow_right 2).mul_pow, ← pow_mul,
        show 2 * 2 = 3 + 1 by norm_num, pow_succ c, hc3, one_mul]
    · rw [hconjpow, hw'c']

theorem exists_transvection_of_conj [Finite G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1)
    (hA : Nat.card A = 27) (hBA : B ≤ A) (hB : Nat.card B = 9) {c : G} (hcB : c ∈ B)
    (hc1 : c ≠ 1) {w s : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hsA : s ∈ Subgroup.normalizer (A : Set G))
    (hwB : w ∈ Subgroup.normalizer (B : Set G)) (hsB : s ∈ Subgroup.normalizer (B : Set G))
    (hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a) (hwc : w * c * w⁻¹ = c)
    (hwfix : ∀ a ∈ A, w * a * w⁻¹ = a → a ∈ Subgroup.zpowers c)
    (hsc : s * c * s⁻¹ ∉ Subgroup.zpowers c) :
    ∃ x ∈ Subgroup.closure ({w, s} : Set G), x * c * x⁻¹ = c ∧
      (∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.zpowers c) ∧ ∃ y ∈ B, x * y * x⁻¹ ≠ y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hcomm x (hBA hx) y (hBA hy)
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := fun x hx => h3 x (hBA hx)
  have hAB : Nat.card A = 3 * Nat.card B := by rw [hA, hB]
  have nA : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) → ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun hg a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have nB : ∀ {g : G}, g ∈ Subgroup.normalizer (B : Set G) → ∀ y ∈ B, g * y * g⁻¹ ∈ B :=
    fun hg y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hc3 : c ^ 3 = 1 := hB3 c hcB
  have hZc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hZcB : Subgroup.zpowers c ≤ B := Subgroup.zpowers_le.mpr hcB
  have hwBc : ∀ y ∈ B, y⁻¹ * (w * y * w⁻¹) ∈ Subgroup.zpowers c :=
    inv_mul_conj_mem_of_pow_three hBc hB3 hZcB (by rw [hB, hZc]) (nB hwB)
      (fun y hy => by rw [conj_eq_of_mem_zpowers hwc hy]; exact hy)
      (fun y hy => hw3 y (hBA hy))
  have hwAB : ∀ a ∈ A, a⁻¹ * (w * a * w⁻¹) ∈ B :=
    inv_mul_conj_mem_of_pow_three hcomm h3 hBA hAB (nA hwA) (nB hwB) hw3
  set c' := s * c * s⁻¹ with hc'
  set w' := s * w * s⁻¹ with hw'
  have hc'B : c' ∈ B := nB hsB c hcB
  have hw'A : w' ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsA hwA) (Subgroup.inv_mem _ hsA)
  have hw'B : w' ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsB hwB) (Subgroup.inv_mem _ hsB)
  have hsinvA : ∀ a ∈ A, s⁻¹ * a * s ∈ A := by
    intro a ha
    have h := nA (Subgroup.inv_mem _ hsA) a ha
    rwa [inv_inv] at h
  have hw'c' : w' * c' * w'⁻¹ = c' := by
    calc w' * c' * w'⁻¹ = s * (w * c * w⁻¹) * s⁻¹ := by rw [hw', hc']; group
      _ = c' := by rw [hwc]
  have hw'3 : ∀ a ∈ A, w' ^ 3 * a * (w' ^ 3)⁻¹ = a := by
    intro a ha
    have h := hw3 _ (hsinvA a ha)
    calc w' ^ 3 * a * (w' ^ 3)⁻¹ = s * (w ^ 3 * (s⁻¹ * a * s) * (w ^ 3)⁻¹) * s⁻¹ := by
          rw [hw', conj_pow]
          group
      _ = a := by rw [h]; group
  have hw'fix : ∀ a ∈ A, w' * a * w'⁻¹ = a → a ∈ Subgroup.zpowers c' := by
    intro a ha hfix
    have h1 : w * (s⁻¹ * a * s) * w⁻¹ = s⁻¹ * a * s := by
      calc w * (s⁻¹ * a * s) * w⁻¹ = s⁻¹ * (w' * a * w'⁻¹) * s := by rw [hw']; group
        _ = s⁻¹ * a * s := by rw [hfix]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hwfix _ (hsinvA a ha) h1)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [hc', ← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply, hk]
    group
  have hc'3 : c' ^ 3 = 1 := hB3 c' hc'B
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    calc c = s⁻¹ * c' * s := by rw [hc']; group
      _ = 1 := by rw [h]; group
  have hZc' : Nat.card (Subgroup.zpowers c') = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc'3 hc'1]
  have hZc'B : Subgroup.zpowers c' ≤ B := Subgroup.zpowers_le.mpr hc'B
  have hw'Bc : ∀ y ∈ B, y⁻¹ * (w' * y * w'⁻¹) ∈ Subgroup.zpowers c' :=
    inv_mul_conj_mem_of_pow_three hBc hB3 hZc'B (by rw [hB, hZc']) (nB hw'B)
      (fun y hy => by rw [conj_eq_of_mem_zpowers hw'c' hy]; exact hy)
      (fun y hy => hw'3 y (hBA hy))
  have hw'AB : ∀ a ∈ A, a⁻¹ * (w' * a * w'⁻¹) ∈ B :=
    inv_mul_conj_mem_of_pow_three hcomm h3 hBA hAB (nA hw'A) (nB hw'B) hw'3
  have hwc' : w * c' * w⁻¹ ≠ c' := fun h => hsc (hwfix c' (hBA hc'B) h)
  have hw'c : w' * c * w'⁻¹ ≠ c := by
    intro h
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers c' :=
      Subgroup.zpowers_le.mpr (hw'fix c (hBA hcB) h)
    have heq : Subgroup.zpowers c = Subgroup.zpowers c' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hZc, hZc'])
    apply hsc
    rw [heq]
    exact Subgroup.mem_zpowers c'
  obtain ⟨d, hdB, hdc, hwd, v, hv, hvd, hvc⟩ :=
    exists_normal_pair hBc hB3 hcB hc'B hsc hwBc hwc' hw'c' hw'Bc hw'c
  have hwS : w ∈ Subgroup.closure ({w, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsS : s ∈ Subgroup.closure ({w, s} : Set G) := Subgroup.subset_closure (by simp)
  have hw'S : w' ∈ Subgroup.closure ({w, s} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsS hwS) (Subgroup.inv_mem _ hsS)
  have hvB : v ∈ Subgroup.normalizer (B : Set G) := by
    rcases hv with rfl | rfl
    · exact hw'B
    · exact Subgroup.mul_mem _ hw'B hw'B
  have hvAB : ∀ a ∈ A, a⁻¹ * (v * a * v⁻¹) ∈ B := by
    rcases hv with rfl | rfl
    · exact hw'AB
    · exact inv_mul_conj_mul_mem (nB hw'B) hw'AB hw'AB
  have hvS : v ∈ Subgroup.closure ({w, s} : Set G) := by
    rcases hv with rfl | rfl
    · exact hw'S
    · exact Subgroup.mul_mem _ hw'S hw'S
  have htinv : ∀ y ∈ B, (w * v * (w * v)) * y * (w * v * (w * v))⁻¹ = y⁻¹ :=
    conj_sq_eq_inv hBc hB3 hB hcB hc1 hdB hdc hwc hwd hvd hvc
  have hwvB : w * v ∈ Subgroup.normalizer (B : Set G) := Subgroup.mul_mem _ hwB hvB
  have hwvAB : ∀ a ∈ A, a⁻¹ * ((w * v) * a * (w * v)⁻¹) ∈ B :=
    inv_mul_conj_mul_mem (nB hwB) hwAB hvAB
  have htAB : ∀ a ∈ A, a⁻¹ * ((w * v * (w * v)) * a * (w * v * (w * v))⁻¹) ∈ B :=
    inv_mul_conj_mul_mem (nB hwvB) hwvAB hwvAB
  obtain ⟨hxB, hxA⟩ :=
    transvection_of_inverting hcomm h3 hBA hAB hcB hwA hwB hw3 hwc hwBc hwAB htinv htAB
  have htS : w * v * (w * v) ∈ Subgroup.closure ({w, s} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hwS hvS) (Subgroup.mul_mem _ hwS hvS)
  refine ⟨w ^ 2 * (w * v * (w * v)) * w⁻¹ * (w * v * (w * v)), ?_, ?_, hxA, d, hdB, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hwS 2)
      htS) (Subgroup.inv_mem _ hwS)) htS
  · rw [hxB c hcB, hwc]
  · rw [hxB d hdB, hwd]
    intro h
    exact hc1 (mul_left_cancel (h.trans (mul_one d).symm))

theorem exists_pPow_transvection [Finite G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1) (hBA : B ≤ A)
    (hAB : Nat.card A = 3 * Nat.card B) {c : G} (hcB : c ∈ B) {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxc : x * c * x⁻¹ = c)
    (hxt : ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ Subgroup.zpowers c) {y : G} (hyB : y ∈ B)
    (hxy : x * y * x⁻¹ ≠ y) :
    ∃ m : ℕ, ¬ 3 ∣ m ∧ IsPGroup 3 (Subgroup.zpowers (x ^ m)) ∧ x ^ m * c * (x ^ m)⁻¹ = c ∧
      x ^ m * y * (x ^ m)⁻¹ ≠ y ∧ ∃ e ∈ A, e ∉ B ∧ x ^ m * e * (x ^ m)⁻¹ = e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : ∀ g u v : G, g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := fun g u v => by
    group
  have hconjpow : ∀ (g u : G) (k : ℕ), g * u ^ k * g⁻¹ = (g * u * g⁻¹) ^ k := fun g u k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have hZA : ∀ z ∈ Subgroup.zpowers c, z ∈ A := fun z hz =>
    hBA ((Subgroup.zpowers_le.mpr hcB) hz)
  have hxA' : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hxA a).mp ha
  have hpow : ∀ a ∈ A, ∀ n : ℕ, x ^ n * a * (x ^ n)⁻¹ = a * (a⁻¹ * (x * a * x⁻¹)) ^ n := by
    intro a ha n
    have hf := hxt a ha
    have hfx : x * (a⁻¹ * (x * a * x⁻¹)) * x⁻¹ = a⁻¹ * (x * a * x⁻¹) :=
      conj_eq_of_mem_zpowers hxc hf
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ = x * (x ^ n * a * (x ^ n)⁻¹) * x⁻¹ := by
            rw [pow_succ']
            group
        _ = (x * a * x⁻¹) * (a⁻¹ * (x * a * x⁻¹)) ^ n := by rw [ih, hconj, hconjpow, hfx]
        _ = a * (a⁻¹ * (x * a * x⁻¹)) * (a⁻¹ * (x * a * x⁻¹)) ^ n := by
            rw [mul_inv_cancel_left]
        _ = a * (a⁻¹ * (x * a * x⁻¹)) ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have hfmul : ∀ a ∈ A, ∀ b ∈ A, (a * b)⁻¹ * (x * (a * b) * x⁻¹) =
      (a⁻¹ * (x * a * x⁻¹)) * (b⁻¹ * (x * b * x⁻¹)) := by
    intro a ha b hb
    have hc' : b⁻¹ * (a⁻¹ * (x * a * x⁻¹)) = (a⁻¹ * (x * a * x⁻¹)) * b⁻¹ :=
      hcomm _ (A.inv_mem hb) _ (A.mul_mem (A.inv_mem ha) (hxA' a ha))
    rw [hconj, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (x * a * x⁻¹ * (x * b * x⁻¹)) =
        (b⁻¹ * (a⁻¹ * (x * a * x⁻¹))) * (x * b * x⁻¹) := by group
      _ = (a⁻¹ * (x * a * x⁻¹)) * (b⁻¹ * (x * b * x⁻¹)) := by rw [hc']; group
  set fy := y⁻¹ * (x * y * x⁻¹) with hfy
  have hfyc : fy ∈ Subgroup.zpowers c := hxt y (hBA hyB)
  have hfy1 : fy ≠ 1 := by
    intro h
    apply hxy
    rw [hfy, inv_mul_eq_one] at h
    exact h.symm
  have hfy3 : fy ^ 3 = 1 := h3 fy (hZA fy hfyc)
  have hfyo : orderOf fy = 3 := orderOf_eq_prime hfy3 hfy1
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hfyc
    exact hfy1 hfyc
  have hc3 : c ^ 3 = 1 := h3 c (hBA hcB)
  have hZ : Subgroup.zpowers fy = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfyc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hfyo, orderOf_eq_prime hc3 hc1])
  obtain ⟨e₁, he₁A, he₁B⟩ : ∃ e₁ ∈ A, e₁ ∉ B := by
    by_contra hno
    push Not at hno
    have hle : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le fun z hz => hno z hz
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hf₁ : e₁⁻¹ * (x * e₁ * x⁻¹) ∈ Subgroup.zpowers fy := hZ ▸ hxt e₁ he₁A
  obtain ⟨k, hk, hk'⟩ := exists_pow_lt_three_of_mem_zpowers hfy3 hf₁
  have hyA : y ∈ A := hBA hyB
  have hfyn : ∀ n : ℕ, (y ^ n)⁻¹ * (x * y ^ n * x⁻¹) = fy ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hfmul _ (A.pow_mem hyA n) _ hyA, ih, pow_succ]
  set e := e₁ * y ^ (3 - k) with he
  have heA : e ∈ A := A.mul_mem he₁A (A.pow_mem hyA _)
  have heB : e ∉ B := by
    intro h
    apply he₁B
    have e' : e₁ = e * (y ^ (3 - k))⁻¹ := by rw [he, mul_inv_cancel_right]
    rw [e']
    exact B.mul_mem h (B.inv_mem (B.pow_mem hyB _))
  have hfe : e⁻¹ * (x * e * x⁻¹) = 1 := by
    rw [he, hfmul _ he₁A _ (A.pow_mem hyA _), hk', hfyn, ← pow_add,
      show k + (3 - k) = 3 by omega, hfy3]
  have hxe : x * e * x⁻¹ = e := by
    rw [inv_mul_eq_one] at hfe
    exact hfe.symm
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  refine ⟨m, hm, ?_, ?_, ?_, e, heA, heB, ?_⟩
  · refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · rw [hpow c (hBA hcB) m, hxc, inv_mul_cancel, one_pow, mul_one]
  · rw [hpow y hyA m]
    intro h
    have h1 : fy ^ m = 1 := by
      have := congrArg (fun z => y⁻¹ * z) h
      simpa [hfy] using this
    exact hm (hfyo ▸ orderOf_dvd_of_pow_eq_one h1)
  · rw [hpow e heA m, hxe, inv_mul_cancel, one_pow, mul_one]

end CFSG.RankThree.PartTwo.Sec21.Item21LateProof
