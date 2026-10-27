module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S152N

abbrev W3 : Type := Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)

namespace W3

noncomputable local instance instFintype : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance instDecEq : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

theorem card_eq : Nat.card W3 = 72 := by
  rw [Nat.card_congr
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  decide

@[expose] def N0 : Subgroup W3 where
  carrier := {a | a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1}
  one_mem' := by decide +kernel
  mul_mem' := by
    have : ∀ a b : W3, (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1) →
        (b.right = 1 ∧ ∀ q, b.left q * b.left q * b.left q = 1) →
        ((a * b).right = 1 ∧ ∀ q, (a * b).left q * (a * b).left q * (a * b).left q = 1) := by
      decide +kernel
    exact fun {a b} ha hb => this a b ha hb
  inv_mem' := by
    have : ∀ a : W3, (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1) →
        (a⁻¹.right = 1 ∧ ∀ q, a⁻¹.left q * a⁻¹.left q * a⁻¹.left q = 1) := by
      decide +kernel
    exact fun {a} ha => this a ha

@[expose] def s01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

@[expose] def P0 : Subgroup W3 where
  carrier := {a | ∀ q, a.left q = 1 ∨ a.left q = s01}
  one_mem' := by decide +kernel
  mul_mem' := by
    have : ∀ a b : W3, (∀ q, a.left q = 1 ∨ a.left q = s01) →
        (∀ q, b.left q = 1 ∨ b.left q = s01) →
        (∀ q, (a * b).left q = 1 ∨ (a * b).left q = s01) := by
      decide +kernel
    exact fun {a b} ha hb => this a b ha hb
  inv_mem' := by
    have : ∀ a : W3, (∀ q, a.left q = 1 ∨ a.left q = s01) →
        (∀ q, a⁻¹.left q = 1 ∨ a⁻¹.left q = s01) := by
      decide +kernel
    exact fun {a} ha => this a ha

local instance : DecidablePred (· ∈ N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))

local instance : DecidablePred (· ∈ P0) := fun a =>
  inferInstanceAs (Decidable (∀ q, a.left q = 1 ∨ a.left q = s01))

theorem N0_normal : N0.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have : ∀ g n : W3, (n.right = 1 ∧ ∀ q, n.left q * n.left q * n.left q = 1) →
      ((g * n * g⁻¹).right = 1 ∧
        ∀ q, (g * n * g⁻¹).left q * (g * n * g⁻¹).left q * (g * n * g⁻¹).left q = 1) := by
    decide +kernel
  exact this g n hn

local instance N0_normal_inst : N0.Normal := N0_normal

theorem card_N0 : Nat.card N0 = 9 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_P0 : Nat.card P0 = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem N0_cert : ∀ c c' : W3, c ∈ N0 → c' ∈ N0 → c ≠ 1 →
    ∃ p₁ ∈ P0, ∃ p₂ ∈ P0, ∃ i j : Fin 3,
      c' = (p₁ * c * p₁⁻¹) ^ (i : ℕ) * (p₂ * c * p₂⁻¹) ^ (j : ℕ) := by
  decide +kernel

theorem N0_irred {C : Subgroup W3} (hC : C ≤ N0) (hP : ∀ p ∈ P0, ∀ c ∈ C, p * c * p⁻¹ ∈ C) :
    C = ⊥ ∨ C = N0 := by
  by_cases hbot : C = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  refine le_antisymm hC (fun c' hc' => ?_)
  obtain ⟨p₁, hp₁, p₂, hp₂, i, j, h⟩ := N0_cert c c' (hC hc) hc' hc1'
  rw [h]
  exact C.mul_mem (C.pow_mem (hP p₁ hp₁ c hc) _) (C.pow_mem (hP p₂ hp₂ c hc) _)

theorem decomp : ∀ w : W3, ∃ n ∈ N0, ∃ p ∈ P0, w = n * p := by
  decide +kernel

theorem eq_or_eq_top_of_P0_le {S : Subgroup W3} (hPS : P0 ≤ S) : S = P0 ∨ S = ⊤ := by
  have hinv : ∀ p ∈ P0, ∀ c ∈ N0 ⊓ S, p * c * p⁻¹ ∈ N0 ⊓ S := fun p hp c hc =>
    ⟨N0_normal.conj_mem c hc.1 p, S.mul_mem (S.mul_mem (hPS hp) hc.2) (S.inv_mem (hPS hp))⟩
  rcases N0_irred inf_le_left hinv with h | h
  · left
    refine le_antisymm (fun s hs => ?_) hPS
    obtain ⟨n, hn, p, hp, rfl⟩ := decomp s
    have hnS : n ∈ N0 ⊓ S := ⟨hn, by
      have := S.mul_mem hs (S.inv_mem (hPS hp))
      simpa using this⟩
    rw [h] at hnS
    have hn1 : n = 1 := Subgroup.mem_bot.mp hnS
    rw [hn1, one_mul]
    exact hp
  · right
    have hNS : N0 ≤ S := by
      intro x hx
      have : x ∈ N0 ⊓ S := by rw [h]; exact hx
      exact this.2
    refine eq_top_iff.mpr (fun w _ => ?_)
    obtain ⟨n, hn, p, hp, rfl⟩ := decomp w
    exact S.mul_mem (hNS hn) (hPS hp)

theorem P0_isPGroup : IsPGroup 2 P0 :=
  IsPGroup.of_card (n := 3) (by rw [card_P0]; norm_num)

theorem P0_isSylowTwoOf : IsSylowTwoOf P0 ⊤ := by
  refine ⟨le_top, P0_isPGroup, ?_⟩
  have h1 : (P0.subgroupOf ⊤).index = P0.index := Subgroup.relIndex_top_right (H := P0)
  have h2 := P0.index_mul_card
  rw [card_P0, card_eq] at h2
  rw [h1]
  omega

theorem sylow_maximal {P S : Subgroup W3} (hP : IsSylowTwoOf P ⊤) (hPS : P ≤ S) :
    S = P ∨ S = ⊤ := by
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf P0_isSylowTwoOf hP
  have hP0S' : P0 ≤ S.comap (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine hPS ((hg (g * x * g⁻¹)).mpr ?_)
    simpa [mul_assoc] using hx
  rcases eq_or_eq_top_of_P0_le hP0S' with h | h
  · left
    refine le_antisymm (fun y hy => ?_) hPS
    have hy' : g⁻¹ * y * g ∈ S.comap (MulAut.conj g).toMonoidHom := by
      show g * (g⁻¹ * y * g) * g⁻¹ ∈ S
      simpa [mul_assoc] using hy
    rw [h] at hy'
    exact (hg y).mpr hy'
  · right
    refine eq_top_iff.mpr (fun y _ => ?_)
    have : g⁻¹ * y * g ∈ S.comap (MulAut.conj g).toMonoidHom := by rw [h]; exact Subgroup.mem_top _
    have h2 : g * (g⁻¹ * y * g) * g⁻¹ ∈ S := this
    simpa [mul_assoc] using h2

theorem index_eq_nine {P : Subgroup W3} (hP : IsSylowTwoOf P ⊤) : P.index = 9 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP.2.1
  have hodd : ¬ 2 ∣ P.index := by
    have h1 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right (H := P)
    rw [← h1]
    exact hP.2.2
  have h2 := P.index_mul_card
  rw [hk, card_eq] at h2
  have hk7 : k < 7 := by
    by_contra h
    have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpos : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    nlinarith
  interval_cases k <;> omega

theorem mem_N0_of_pow_three : ∀ w : W3, w ^ 3 = 1 → w ∈ N0 := by
  decide +kernel

theorem no_normal_of_three_dvd {N : Subgroup W3} (hN : N.Normal) (h3 : 3 ∣ Nat.card N)
    (h9 : ¬ 9 ∣ Nat.card N) : False := by
  have hinv : ∀ p ∈ P0, ∀ c ∈ N ⊓ N0, p * c * p⁻¹ ∈ N ⊓ N0 := fun p _ c hc =>
    ⟨hN.conj_mem c hc.1 p, N0_normal.conj_mem c hc.2 p⟩
  rcases N0_irred inf_le_right hinv with h | h
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
    have hx3 : (x : W3) ^ 3 = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      simpa using congrArg Subtype.val this
    have hxm : (x : W3) ∈ N ⊓ N0 := ⟨x.2, mem_N0_of_pow_three _ hx3⟩
    rw [h] at hxm
    have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hxm)
    rw [hx1, orderOf_one] at hx
    omega
  · have hle : N0 ≤ N := fun x hx => by
      have : x ∈ N ⊓ N0 := by rw [h]; exact hx
      exact this.1
    exact h9 (card_N0 ▸ Subgroup.card_dvd_of_le hle)

theorem no_normal_order_twelve {N : Subgroup W3} (hN : N.Normal) : Nat.card N ≠ 12 := by
  intro h12
  exact no_normal_of_three_dvd hN (by rw [h12]; norm_num) (by rw [h12]; norm_num)

theorem no_normal_order_six {N : Subgroup W3} (hN : N.Normal) : Nat.card N ≠ 6 := by
  intro h6
  exact no_normal_of_three_dvd hN (by rw [h6]; norm_num) (by rw [h6]; norm_num)

end W3

end S152N

end CFSG.Quasithin
