module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin

namespace S153EN8

theorem odd_orderOf_of_cube {H : Type*} [Group H] {d : H} (h3 : d ^ 3 = 1) : Odd (orderOf d) := by
  have : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h <;> rw [h] <;> decide

section Generic

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem eq_pow_of_commute (hN : ActsAsNaturalL2 L U) {x l : MulAut W} (hx : x ∈ L) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hl : l ∈ L) (hc : l * x = x * l) : ∃ j : ℕ, l = x ^ j := by
  obtain ⟨e, -, -⟩ := hN
  have hex3 : (e ⟨x, hx⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hx⟩ : L) ^ 3 = 1 := Subtype.ext hx3
    rw [this, map_one]
  have hex1 : e ⟨x, hx⟩ ≠ 1 := by
    intro h
    apply hx1
    have h' : (⟨x, hx⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  have hcomm : e ⟨l, hl⟩ * e ⟨x, hx⟩ = e ⟨x, hx⟩ * e ⟨l, hl⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  rcases S1417.SL2_cent_three _ _ hex3 hex1 hcomm with h | h | h
  · refine ⟨0, ?_⟩
    have h' : (⟨l, hl⟩ : L) = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h'
  · refine ⟨1, ?_⟩
    have h' : (⟨l, hl⟩ : L) = ⟨x, hx⟩ := e.injective h
    simpa using congrArg Subtype.val h'
  · refine ⟨2, ?_⟩
    have h' : (⟨l, hl⟩ : L) = ⟨x, hx⟩⁻¹ := by
      apply e.injective
      rw [h, map_inv]
    have h3 : (⟨x, hx⟩ : L)⁻¹ = ⟨x, hx⟩ ^ 2 := by
      have : (⟨x, hx⟩ : L) ^ 3 = 1 := Subtype.ext hx3
      calc (⟨x, hx⟩ : L)⁻¹ = (⟨x, hx⟩ : L)⁻¹ * (⟨x, hx⟩ ^ 3) := by rw [this, mul_one]
        _ = ⟨x, hx⟩ ^ 2 := by group
    rw [h3] at h'
    simpa using congrArg Subtype.val h'

end Generic

section NormalTwo

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem sl2_no_normal_two : ∀ a c : S1417.SL2, a ^ 2 = 1 → a ≠ 1 → c ^ 3 = 1 → c ≠ 1 →
    (a * (c * a * c⁻¹)) ^ 2 = 1 → False := by
  decide

theorem eq_bot_of_normal_pgroup (hN : ActsAsNaturalL2 L U) {S : Subgroup (MulAut W)} (hSL : S ≤ L)
    (hSn : ∀ l ∈ L, ∀ x ∈ S, l * x * l⁻¹ ∈ S) (hS2 : IsPGroup 2 S) : S = ⊥ := by
  have hcard : Nat.card L = 6 := (S1417.card_of_actsAsNaturalL2 hN).1
  have hsq : ∀ y ∈ S, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hS2 ⟨y, hy⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf y ∣ 6 := by
      have := orderOf_dvd_natCard (⟨y, hSL hy⟩ : L)
      rw [Subgroup.orderOf_mk, hcard] at this
      exact this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    have hj1 : j ≤ 1 := by
      by_contra hj'
      have h4 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      rw [← hj] at h4
      have := h4.trans h1
      omega
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hj]
    exact (pow_dvd_pow 2 hj1).trans (by simp)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨c, hcL, hc3, hc1⟩ := S1417.exists_orderThree hN
  obtain ⟨e, -, -⟩ := hN
  have hz : x * (c * x * c⁻¹) ∈ S := S.mul_mem hx (hSn c hcL x hx)
  have hz2 := hsq _ hz
  have hLz : (⟨x, hSL hx⟩ * (⟨c, hcL⟩ * ⟨x, hSL hx⟩ * ⟨c, hcL⟩⁻¹) : L) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hz2
  have h1 := congrArg e hLz
  rw [map_pow, map_one, map_mul, map_mul, map_mul, map_inv] at h1
  refine sl2_no_normal_two (e ⟨x, hSL hx⟩) (e ⟨c, hcL⟩) ?_ ?_ ?_ ?_ h1
  · rw [← map_pow]
    have : (⟨x, hSL hx⟩ : L) ^ 2 = 1 := Subtype.ext (hsq x hx)
    rw [this, map_one]
  · intro h
    apply hx1'
    have h' : (⟨x, hSL hx⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'
  · rw [← map_pow]
    have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext hc3
    rw [this, map_one]
  · intro h
    apply hc1
    have h' : (⟨c, hcL⟩ : L) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val h'

end NormalTwo

section Bar

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}
  (h : OfourStruct X L₁ L₂ t)
include h

theorem fix_iff_mem_commV₁ {d : MulAut W} (hd : d ∈ L₂) (hodd : Odd (orderOf d)) (hd1 : d ≠ 1)
    (w : W) : d w = w ↔ w ∈ commV L₁ := by
  constructor
  · intro hw
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
    have e1 : d u₁ = u₁ := h.L₂_fix₁ hd hu₁
    have e2 : d u₂ = u₂ := by
      rw [map_mul, e1] at hw
      exact mul_left_cancel hw
    have : u₂ = 1 := by
      by_contra hne
      exact hd1 (S1417.eq_one_of_odd_of_fixed h.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hd
        hodd hu₂ hne e2)
    rw [this, mul_one]
    exact hu₁
  · intro hw
    exact h.L₂_fix₁ hd hw

theorem mem_sup_of_commute {x d : MulAut W} (hx : x ∈ X) (hd : d ∈ L₂) (hodd : Odd (orderOf d))
    (hd1 : d ≠ 1) (hc : x * d = d * x) : x ∈ L₁ ⊔ L₂ := by
  rw [h.mem_sup_iff hx]
  intro u hu
  rw [← fix_iff_mem_commV₁ h hd hodd hd1]
  have e : d (x u) = x (d u) := by
    have := congrArg (fun φ : MulAut W => φ u) hc.symm
    simpa using this
  rw [e, (fix_iff_mem_commV₁ h hd hodd hd1 u).2 hu]

theorem cent_decomp {x d : MulAut W} (hx : x ∈ X) (hd : d ∈ L₂) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hc : x * d = d * x) : ∃ l ∈ L₁, ∃ j : ℕ, x = l * d ^ j := by
  have hodd := odd_orderOf_of_cube hd3
  have hxN := mem_sup_of_commute h hx hd hodd hd1 hc
  obtain ⟨a, ha, b, hb, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute h.comm hxN
  have hbd : b * d = d * b := by
    have h1 : a * (b * d) = a * (d * b) := by
      calc a * (b * d) = (a * b) * d := by group
        _ = d * (a * b) := hc
        _ = (d * a) * b := by group
        _ = (a * d) * b := by rw [h.comm a ha d hd]
        _ = a * (d * b) := by group
    exact mul_left_cancel h1
  obtain ⟨j, hj⟩ := eq_pow_of_commute h.nat₂ hd hd3 hd1 hb hbd
  exact ⟨a, ha, j, by rw [hj]⟩

theorem mem_L₂_of_fix {y : MulAut W} (hy : y ∈ X) (hodd : Odd (orderOf y)) {w : W}
    (hw : w ∈ commV L₁) (hw1 : w ≠ 1) (hfix : y w = w) : y ∈ L₂ := by
  have hyN := h.odd_mem_sup hy hodd
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁3, -⟩ := h.odd_decomp hyN hodd
  have e2 : l₂ w = w := h.L₂_fix₁ hl₂ hw
  have e1 : l₁ w = w := by
    rw [MulAut.mul_apply, e2] at hfix
    exact hfix
  have hl1 : l₁ = 1 := S1417.eq_one_of_odd_of_fixed h.nat₁ (fun l hl u hu => commV_stable L₁ hl hu)
    hl₁ (odd_orderOf_of_cube hl₁3) hw hw1 e1
  rw [hl1, one_mul]
  exact hl₂

theorem card_commV_involution [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {s : MulAut W} (hs : s ∈ L₁)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) : Nat.card (commV (Subgroup.zpowers s)) = 2 := by
  obtain ⟨a, ha, ha1, hfa⟩ := S1417.exists_fixed_vector h.nat₁
    (fun l hl u hu => commV_stable L₁ hl hu) hs hs2 hs1
  have ha2 : a ^ 2 = 1 := hW a
  have hcard : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have hss : ∀ u : W, s (s u) = u := fun u => by
    have := congrArg (fun φ : MulAut W => φ u) hs2
    simpa [pow_two] using this
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hW w)
  have hle : commV (Subgroup.zpowers s) ≤ Subgroup.zpowers a := by
    rw [commV_zpowers_eq_map]
    rintro _ ⟨w, -, rfl⟩
    rw [commHom_apply]
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
    have e2 : s u₂ = u₂ := h.L₁_fix₂ hs hu₂
    have e : s (u₁ * u₂) * (u₁ * u₂)⁻¹ = s u₁ * u₁⁻¹ := by
      rw [map_mul, e2, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [e]
    have hy₁ : s u₁ * u₁⁻¹ ∈ commV L₁ :=
      (commV L₁).mul_mem (commV_stable L₁ hs hu₁) ((commV L₁).inv_mem hu₁)
    have hfix : s (s u₁ * u₁⁻¹) = s u₁ * u₁⁻¹ := by
      rw [map_mul, map_inv, hss, hinv (s u₁), hinv u₁, mul_comm]
    rcases (hfa _ hy₁).1 hfix with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers a
  have hne : ∃ w : W, s w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hs1 (MulEquiv.ext fun w => by simpa using hcon w)
  obtain ⟨w, hw⟩ := hne
  have hymem : s w * w⁻¹ ∈ commV (Subgroup.zpowers s) := by
    rw [commV_zpowers_eq_map]
    exact ⟨w, Subgroup.mem_top _, rfl⟩
  have hy1 : s w * w⁻¹ ≠ 1 := fun h' => hw (mul_inv_eq_one.mp h')
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exfalso
    have : commV (Subgroup.zpowers s) = ⊥ := Subgroup.card_eq_one.1 h1
    rw [this] at hymem
    exact hy1 (Subgroup.mem_bot.1 hymem)
  · exact h1

end Bar

end S153EN8

end CFSG.Quasithin
