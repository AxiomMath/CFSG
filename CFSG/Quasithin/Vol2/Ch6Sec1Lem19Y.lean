module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace L619

section Lines

variable {Q : Type*} [Group Q] {q₁ q₂ : Q}

theorem exists_pow_mul_pow (hc : q₁ * q₂ = q₂ * q₁) (h1 : q₁ ^ 3 = 1) (h2 : q₂ ^ 3 = 1)
    {x : Q} (hx : x ∈ Subgroup.closure ({q₁, q₂} : Set Q)) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = q₁ ^ i * q₂ ^ j := by
  have hcomm : Commute q₁ q₂ := hc
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, by norm_num, by norm_num, by simp⟩
  | one => exact ⟨0, 0, by norm_num, by norm_num, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, hi, hj, rfl⟩ := hx
    obtain ⟨k, l, hk, hl, rfl⟩ := hy
    refine ⟨(i + k) % 3, (j + l) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    have e1 : q₁ ^ ((i + k) % 3) = q₁ ^ i * q₁ ^ k := by
      rw [← pow_add, pow_eq_pow_mod (i + k) h1]
    have e2 : q₂ ^ ((j + l) % 3) = q₂ ^ j * q₂ ^ l := by
      rw [← pow_add, pow_eq_pow_mod (j + l) h2]
    rw [e1, e2]
    have : Commute (q₂ ^ j) (q₁ ^ k) := (hcomm.pow_pow k j).symm
    calc q₁ ^ i * q₂ ^ j * (q₁ ^ k * q₂ ^ l) = q₁ ^ i * (q₂ ^ j * q₁ ^ k) * q₂ ^ l := by group
      _ = q₁ ^ i * (q₁ ^ k * q₂ ^ j) * q₂ ^ l := by rw [this.eq]
      _ = q₁ ^ i * q₁ ^ k * (q₂ ^ j * q₂ ^ l) := by group
  | inv x _ hx =>
    obtain ⟨i, j, hi, hj, rfl⟩ := hx
    refine ⟨(3 - i) % 3, (3 - j) % 3, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
    have e1 : q₁ ^ ((3 - i) % 3) = (q₁ ^ i)⁻¹ := by
      rw [← pow_eq_pow_mod _ h1, eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hi.le, h1]
    have e2 : q₂ ^ ((3 - j) % 3) = (q₂ ^ j)⁻¹ := by
      rw [← pow_eq_pow_mod _ h2, eq_inv_iff_mul_eq_one, ← pow_add, Nat.sub_add_cancel hj.le, h2]
    rw [e1, e2, mul_inv_rev, (hcomm.pow_pow i j).inv_inv.eq]

theorem zpowers_sq_eq {x : Q} (hx : x ^ 3 = 1) : Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2
  · rw [Subgroup.zpowers_le]
    have h4 : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx, one_mul, pow_one]
    have := Subgroup.pow_mem (Subgroup.zpowers (x ^ 2)) (Subgroup.mem_zpowers (x ^ 2)) 2
    rwa [h4] at this

theorem eq_zpowers_of_card_three {N : Subgroup Q} (hcard : Nat.card N = 3) {n : Q} (hn : n ∈ N)
    (hn1 : n ≠ 1) : N = Subgroup.zpowers n := by
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have hle : Subgroup.zpowers n ≤ N := Subgroup.zpowers_le.mpr hn
  have hdvd : orderOf n ∣ 3 := by
    rw [← hcard, ← Subgroup.orderOf_mk n hn]
    exact orderOf_dvd_natCard _
  have ho : orderOf n = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hn1
    · exact h
  have : Finite (Subgroup.zpowers n) := Finite.Set.subset _ hle
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, Nat.card_zpowers, ho]

theorem eq_line_of_card (hc : q₁ * q₂ = q₂ * q₁) (h1 : q₁ ^ 3 = 1) (h2 : q₂ ^ 3 = 1)
    {N : Subgroup Q} (hN : N ≤ Subgroup.closure ({q₁, q₂} : Set Q)) (hcard : Nat.card N = 3) :
    N = Subgroup.zpowers q₁ ∨ N = Subgroup.zpowers q₂ ∨ N = Subgroup.zpowers (q₁ * q₂) ∨
      N = Subgroup.zpowers (q₁ * q₂ ^ 2) := by
  have hcomm : Commute q₁ q₂ := hc
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨n, hn⟩ : ∃ n : N, n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton N := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    rw [Nat.card_unique] at hcard
    omega
  have hn' : (n : Q) ≠ 1 := fun h => hn (Subtype.ext h)
  rw [eq_zpowers_of_card_three hcard n.2 hn']
  obtain ⟨i, j, hi, hj, hij⟩ := exists_pow_mul_pow hc h1 h2 (hN n.2)
  rw [hij]
  rw [hij] at hn'
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) hn'
  · right; left; simp
  · right; left; simp only [pow_zero, one_mul]; exact zpowers_sq_eq h2
  · left; simp
  · right; right; left; simp
  · right; right; right; simp
  · left; simp only [pow_zero, mul_one]; exact zpowers_sq_eq h1
  · right; right; right
    have e : q₁ ^ 2 * q₂ ^ 1 = (q₁ * q₂ ^ 2) ^ 2 := by
      rw [(hcomm.pow_right 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h2,
        one_mul]
    rw [e]
    exact zpowers_sq_eq (by rw [(hcomm.pow_right 2).mul_pow, h1, one_mul, ← pow_mul,
      show 2 * 3 = 3 * 2 by norm_num, pow_mul, h2, one_pow])
  · right; right; left
    rw [← (hcomm.mul_pow 2)]
    exact zpowers_sq_eq (by rw [hcomm.mul_pow, h1, h2, one_mul])

theorem exists_pow_of_mem_zpowers [Finite Q] {x y : Q} (hy : y ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers y) : ∃ k : ℕ, k < 3 ∧ x = y ^ k := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk)
    (orderOf_le_of_pow_eq_one (by norm_num) hy), rfl⟩

theorem exists_pow_of_zpowers_eq [Finite Q] {a b : Q} (hb : b ^ 3 = 1)
    (h : Subgroup.zpowers a = Subgroup.zpowers b) : ∃ k : ℕ, k < 3 ∧ a = b ^ k :=
  exists_pow_of_mem_zpowers hb (h ▸ Subgroup.mem_zpowers a)

@[expose] def mapA (α : MulAut Q) (L : Subgroup Q) : Subgroup Q := L.map α.toMonoidHom

theorem mapA_mul (α β : MulAut Q) (L : Subgroup Q) : mapA (α * β) L = mapA α (mapA β L) := by
  ext x
  simp only [mapA, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨β y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem mapA_one (L : Subgroup Q) : mapA (1 : MulAut Q) L = L := by
  ext x
  simp [mapA]

theorem mapA_injective (α : MulAut Q) : Function.Injective (mapA α) :=
  Subgroup.map_injective α.injective

theorem mapA_zpowers (α : MulAut Q) (x : Q) :
    mapA α (Subgroup.zpowers x) = Subgroup.zpowers (α x) :=
  MonoidHom.map_zpowers _ _

theorem card_mapA (α : MulAut Q) (L : Subgroup Q) : Nat.card (mapA α L) = Nat.card L :=
  Subgroup.card_map_of_injective α.injective

variable [Finite Q]

theorem coords_of_zpowers_eq (hc : q₁ * q₂ = q₂ * q₁) (h1 : q₁ ^ 3 = 1) (h2 : q₂ ^ 3 = 1)
    (hinj : ∀ a b c d : ℕ, a < 3 → b < 3 → c < 3 → d < 3 →
      q₁ ^ a * q₂ ^ b = q₁ ^ c * q₂ ^ d → a = c ∧ b = d)
    {a b c d : ℕ} (ha : a < 3) (hb : b < 3)
    (h : Subgroup.zpowers (q₁ ^ a * q₂ ^ b) = Subgroup.zpowers (q₁ ^ c * q₂ ^ d)) :
    ∃ k : ℕ, k < 3 ∧ a = c * k % 3 ∧ b = d * k % 3 := by
  have hcomm : Commute q₁ q₂ := hc
  have h3 : (q₁ ^ c * q₂ ^ d) ^ 3 = 1 := by
    rw [(hcomm.pow_pow c d).mul_pow, ← pow_mul, ← pow_mul, mul_comm c 3, mul_comm d 3, pow_mul,
      pow_mul, h1, h2, one_pow, one_pow, one_mul]
  obtain ⟨k, hk, e⟩ := exists_pow_of_zpowers_eq h3 h
  refine ⟨k, hk, hinj a b _ _ ha hb (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ?_⟩
  rw [e, (hcomm.pow_pow c d).mul_pow, ← pow_mul, ← pow_mul, ← pow_eq_pow_mod (c * k) h1,
    ← pow_eq_pow_mod (d * k) h2]

theorem mapA_eq_of_cube (hc : q₁ * q₂ = q₂ * q₁) (h1 : q₁ ^ 3 = 1) (h2 : q₂ ^ 3 = 1)
    (hgen : Subgroup.closure ({q₁, q₂} : Set Q) = ⊤)
    (hinj : ∀ a b c d : ℕ, a < 3 → b < 3 → c < 3 → d < 3 →
      q₁ ^ a * q₂ ^ b = q₁ ^ c * q₂ ^ d → a = c ∧ b = d) (𝒮 : Set (MulAut Q))
    (h𝒮 : ∀ s ∈ 𝒮, ∀ L, (L = Subgroup.zpowers q₁ ∨ L = Subgroup.zpowers q₂) →
      (mapA s L = Subgroup.zpowers q₁ ∨ mapA s L = Subgroup.zpowers q₂))
    {s₁ : MulAut Q} (hs₁ : s₁ ∈ 𝒮) (hs₁q₁ : s₁ q₁ = q₁⁻¹) (hs₁q₂ : s₁ q₂ = q₂)
    {σ : MulAut Q} (hσ : σ ∈ 𝒮) (hσq₁ : mapA σ (Subgroup.zpowers q₁) = Subgroup.zpowers q₂)
    {α : MulAut Q} (hα3 : α ^ 3 = 1) (hα𝒮 : ∀ s ∈ 𝒮, ∃ s' ∈ 𝒮, α * s' = s * α) :
    mapA α (Subgroup.zpowers q₁) = Subgroup.zpowers q₁ := by
  have hcomm : Commute q₁ q₂ := hc
  have cf := fun {a b c d : ℕ} (ha : a < 3) (hb : b < 3) h =>
    coords_of_zpowers_eq (q₁ := q₁) (q₂ := q₂) hc h1 h2 hinj (c := c) (d := d) ha hb h
  have nL₁ : Subgroup.zpowers q₁ = Subgroup.zpowers (q₁ ^ 1 * q₂ ^ 0) := by simp
  have nL₂ : Subgroup.zpowers q₂ = Subgroup.zpowers (q₁ ^ 0 * q₂ ^ 1) := by simp
  have nΔ : Subgroup.zpowers (q₁ * q₂) = Subgroup.zpowers (q₁ ^ 1 * q₂ ^ 1) := by simp
  have nΔ' : Subgroup.zpowers (q₁ * q₂ ^ 2) = Subgroup.zpowers (q₁ ^ 1 * q₂ ^ 2) := by simp
  have h12 : Subgroup.zpowers q₁ ≠ Subgroup.zpowers q₂ := fun h => by
    rw [nL₁, nL₂] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ1 : Subgroup.zpowers (q₁ * q₂) ≠ Subgroup.zpowers q₁ := fun h => by
    rw [nΔ, nL₁] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ2 : Subgroup.zpowers (q₁ * q₂) ≠ Subgroup.zpowers q₂ := fun h => by
    rw [nΔ, nL₂] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ'1 : Subgroup.zpowers (q₁ * q₂ ^ 2) ≠ Subgroup.zpowers q₁ := fun h => by
    rw [nΔ', nL₁] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ'2 : Subgroup.zpowers (q₁ * q₂ ^ 2) ≠ Subgroup.zpowers q₂ := fun h => by
    rw [nΔ', nL₂] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔΔ' : Subgroup.zpowers (q₁ * q₂) ≠ Subgroup.zpowers (q₁ * q₂ ^ 2) := fun h => by
    rw [nΔ, nΔ'] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hq1 : q₁⁻¹ = q₁ ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', h1]
  have h12c : (q₁ * q₂) ^ 3 = 1 := by rw [hcomm.mul_pow, h1, h2, one_mul]
  have h122c : (q₁ * q₂ ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow, h1, one_mul, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num,
      pow_mul, h2, one_pow]
  have hcard3 : ∀ x : Q, x ^ 3 = 1 → x ≠ 1 → Nat.card (Subgroup.zpowers x) = 3 := fun x hx hx1 =>
    by rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]
  have hne1 : ∀ x : Q, Subgroup.zpowers x ≠ Subgroup.zpowers 1 → x ≠ 1 := fun x h hx =>
    h (by rw [hx])
  have hz1 : Subgroup.zpowers (1 : Q) = Subgroup.zpowers (q₁ ^ 0 * q₂ ^ 0) := by simp
  have hq₁1 : q₁ ≠ 1 := hne1 _ fun h => by
    rw [nL₁, hz1] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hq₂1 : q₂ ≠ 1 := hne1 _ fun h => by
    rw [nL₂, hz1] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ1' : q₁ * q₂ ≠ 1 := hne1 _ fun h => by
    rw [nΔ, hz1] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hΔ'1' : q₁ * q₂ ^ 2 ≠ 1 := hne1 _ fun h => by
    rw [nΔ', hz1] at h
    obtain ⟨k, hk, e1, e2⟩ := cf (by norm_num) (by norm_num) h
    interval_cases k <;> simp at e1 e2
  have hs₁Δ : mapA s₁ (Subgroup.zpowers (q₁ * q₂)) = Subgroup.zpowers (q₁ * q₂ ^ 2) := by
    rw [mapA_zpowers, map_mul, hs₁q₁, hs₁q₂]
    have e : q₁⁻¹ * q₂ = (q₁ * q₂ ^ 2) ^ 2 := by
      rw [hq1, (hcomm.pow_right 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h2,
        one_mul, pow_one]
    rw [e, zpowers_sq_eq h122c]
  have hs₁Δ' : mapA s₁ (Subgroup.zpowers (q₁ * q₂ ^ 2)) = Subgroup.zpowers (q₁ * q₂) := by
    rw [mapA_zpowers, map_mul, map_pow, hs₁q₁, hs₁q₂, hq1, ← hcomm.mul_pow]
    exact zpowers_sq_eq h12c
  have hlines : ∀ N : Subgroup Q, Nat.card N = 3 → N = Subgroup.zpowers q₁ ∨
      N = Subgroup.zpowers q₂ ∨ N = Subgroup.zpowers (q₁ * q₂) ∨
      N = Subgroup.zpowers (q₁ * q₂ ^ 2) := fun N hN =>
    eq_line_of_card hc h1 h2 (hgen ▸ le_top) hN
  have hstep : ∀ s ∈ 𝒮, mapA s (mapA α (Subgroup.zpowers q₁)) = mapA α (Subgroup.zpowers q₁) ∨
      mapA s (mapA α (Subgroup.zpowers q₁)) = mapA α (Subgroup.zpowers q₂) := by
    intro s hs
    obtain ⟨s', hs', hss'⟩ := hα𝒮 s hs
    have h := h𝒮 _ hs' (Subgroup.zpowers q₁) (Or.inl rfl)
    have e : mapA s (mapA α (Subgroup.zpowers q₁)) =
        mapA α (mapA s' (Subgroup.zpowers q₁)) := by
      rw [← mapA_mul, ← mapA_mul, hss']
    rw [e]
    rcases h with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hα3' : ∀ L, mapA α (mapA α (mapA α L)) = L := fun L => by
    rw [← mapA_mul, ← mapA_mul, ← pow_three', hα3, mapA_one]
  have hσL₂ : mapA σ (Subgroup.zpowers q₂) = Subgroup.zpowers q₁ := by
    rcases h𝒮 σ hσ _ (Or.inr rfl) with h | h
    · exact h
    · exact absurd (mapA_injective σ (hσq₁.trans h.symm)) h12
  rcases hlines (mapA α (Subgroup.zpowers q₁)) (by rw [card_mapA]; exact hcard3 _ h1 hq₁1)
    with h | h | h | h
  · exact h
  ·
    exfalso
    have hN₂ : mapA α (Subgroup.zpowers q₂) = Subgroup.zpowers q₁ := by
      rcases hstep σ hσ with h' | h'
      · rw [h, hσL₂] at h'
        exact absurd h' h12
      · rw [h, hσL₂] at h'
        exact h'.symm
    have := hα3' (Subgroup.zpowers q₁)
    rw [h, hN₂, h] at this
    exact h12 this.symm
  ·
    exfalso
    have hN₂ : mapA α (Subgroup.zpowers q₂) = Subgroup.zpowers (q₁ * q₂ ^ 2) := by
      rcases hstep s₁ hs₁ with h' | h'
      · rw [h, hs₁Δ] at h'
        exact absurd h'.symm hΔΔ'
      · rw [h, hs₁Δ] at h'
        exact h'.symm
    have hαΔ : mapA α (Subgroup.zpowers (q₁ * q₂)) = Subgroup.zpowers q₁ ∨
        mapA α (Subgroup.zpowers (q₁ * q₂)) = Subgroup.zpowers q₂ := by
      rcases hlines (mapA α (Subgroup.zpowers (q₁ * q₂)))
        (by rw [card_mapA]; exact hcard3 _ h12c hΔ1') with h'' | h'' | h'' | h''
      · exact Or.inl h''
      · exact Or.inr h''
      · exact absurd (mapA_injective α (h''.trans h.symm)) hΔ1
      · exact absurd (mapA_injective α (h''.trans hN₂.symm)) hΔ2
    have := hα3' (Subgroup.zpowers q₁)
    rw [h] at this
    rcases hαΔ with h'' | h'' <;> rw [h''] at this
    · rw [h] at this
      exact hΔ1 this
    · rw [hN₂] at this
      exact hΔ'1 this
  ·
    exfalso
    have hN₂ : mapA α (Subgroup.zpowers q₂) = Subgroup.zpowers (q₁ * q₂) := by
      rcases hstep s₁ hs₁ with h' | h'
      · rw [h, hs₁Δ'] at h'
        exact absurd h' hΔΔ'
      · rw [h, hs₁Δ'] at h'
        exact h'.symm
    have hαΔ : mapA α (Subgroup.zpowers (q₁ * q₂ ^ 2)) = Subgroup.zpowers q₁ ∨
        mapA α (Subgroup.zpowers (q₁ * q₂ ^ 2)) = Subgroup.zpowers q₂ := by
      rcases hlines (mapA α (Subgroup.zpowers (q₁ * q₂ ^ 2)))
        (by rw [card_mapA]; exact hcard3 _ h122c hΔ'1') with h'' | h'' | h'' | h''
      · exact Or.inl h''
      · exact Or.inr h''
      · exact absurd (mapA_injective α (h''.trans hN₂.symm)) hΔ'2
      · exact absurd (mapA_injective α (h''.trans h.symm)) hΔ'1
    have := hα3' (Subgroup.zpowers q₁)
    rw [h] at this
    rcases hαΔ with h'' | h'' <;> rw [h''] at this
    · rw [h] at this
      exact hΔ'1 this
    · rw [hN₂] at this
      exact hΔ1 this

end Lines

section Generic

variable {G : Type} [Group G]

theorem mem_of_pow_three_eq_one_of_coprime {N O : Subgroup G}
    (hO : ∀ o ∈ O, Nat.Coprime (orderOf o) 3) (hON : O ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ O) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x ∈ N := by
  have hx' : x ∈ ((N ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hON] at hx'
  obtain ⟨n, hn, o, ho, rfl⟩ := hx'
  show n * o ∈ N
  replace hk : (n * o) ^ 3 ^ k = 1 := hk
  obtain ⟨n', hn', he⟩ := exists_pow_mul_eq (hON ho) hn (orderOf o)
  rw [pow_orderOf_eq_one, mul_one] at he
  have hcop : Nat.Coprime (orderOf o) (orderOf (n * o)) := by
    have hdvd : orderOf (n * o) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right _ (hO o ho))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj, he]
  exact N.pow_mem hn' j

theorem perm3_eq_of_cube : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    σ = 1 ∨ σ = cyc3 ∨ σ = cyc3 ^ 2 := by
  unfold cyc3
  decide

theorem perm3_inv_conj : ∀ τ : Equiv.Perm (Fin 3), τ ^ 2 = 1 → τ ≠ 1 →
    τ * cyc3 * τ⁻¹ = cyc3⁻¹ := by
  unfold cyc3
  decide

theorem perm3_cube_of_pow {σ : Equiv.Perm (Fin 3)} {m : ℕ} (h : σ ^ 3 ^ m = 1) : σ ^ 3 = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h)
  have h2 : 3 ^ j ∣ 6 := by
    rw [← hj]
    have := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, Nat.card_fin] at this
  have hj1 : j ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 hc).trans h2
    omega
  rw [orderOf_dvd_iff_pow_eq_one.symm, hj]
  exact pow_dvd_pow 3 hj1 |>.trans (by norm_num)

theorem perm3_facts {X : Type*} [Group X] (θ : X ≃* Equiv.Perm (Fin 3)) :
    θ.symm cyc3 ^ 3 = 1 ∧ θ.symm cyc3 ≠ 1 ∧
      (∀ k : X, (∃ m : ℕ, k ^ 3 ^ m = 1) → k ∈ Subgroup.zpowers (θ.symm cyc3)) ∧
      (∀ t : X, t ^ 2 = 1 → t ≠ 1 → t * θ.symm cyc3 * t⁻¹ = (θ.symm cyc3)⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, show cyc3 ^ 3 = 1 by unfold cyc3; decide, map_one]
  · intro h
    have := congrArg θ h
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd this (by unfold cyc3; decide)
  · rintro k ⟨m, hm⟩
    have hσ : θ k ^ 3 = 1 := perm3_cube_of_pow (m := m) (by rw [← map_pow, hm, map_one])
    have hk : k = θ.symm (θ k) := (θ.symm_apply_apply k).symm
    rcases perm3_eq_of_cube _ hσ with h | h | h <;> rw [hk, h]
    · rw [map_one]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · rw [map_pow]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  · intro t ht2 ht1
    apply θ.injective
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    refine perm3_inv_conj _ (by rw [← map_pow, ht2, map_one]) fun h => ht1 ?_
    exact θ.injective (h.trans (map_one θ).symm)

end Generic

end L619

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem false_of_swap_core3 (hW : IsElemAbelian 2 (ch619W T L V z)) :
    ∀ (_c : Cfg619 T L V H n y),
    let I : Subgroup G := ch619I T L V
    let P : Subgroup G := conjClosure (conjSub y V) (I ⊔ T')
    let N : Subgroup G := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P
    ∀ (Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P))),
    ∀ (hPN : P ≤ N),
    ∀ (hIN : I ≤ N),
    let φ : ↥P →* ↥(L619.img0 hW (ch6ZS T L V) P) := L619.actOn hW (ch6ZS T L V) P hPN fun x =>
        L619.act0_mem_img0 hW (ch6ZS T L V) P x.property
    ∀ (_hkerP : ∀ (x : ↥P), φ x = 1 → ↑x ∈ pCoreOf 2 P),
    ∀ (_hO2P : IsPGroup 2 ↥(pCoreOf 2 P)),
    ∀ (_hPI : P ≤ I),
    ∀ (_hIP : I ≤ Subgroup.normalizer ↑P),
    ∀ (_hc01 : ∀ a ∈ Ks 0, ∀ b ∈ Ks 1, a * b = b * a),
    let J : Subgroup G := L619.oddPart I
    let X₀ : Subgroup G := L619.preimg φ (Ks 0)
    let X₁ : Subgroup G := L619.preimg φ (Ks 1)
    let A₀ : Subgroup G := L619.threePart X₀
    let A₁ : Subgroup G := L619.threePart X₁
    ∀ (_hA₀ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 0)))),
    ∀ (_hA₁ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 1)))),
    ∀ (_hinf : A₀ ⊓ A₁ ≤ pCoreOf 2 A₀),
    ∀ (_hA₀P : A₀ ≤ P),
    ∀ (_hA₁P : A₁ ≤ P),
    ∀ (hθ : ∀ (i : Fin 2), Nonempty (↥(Ks i) ≃* Equiv.Perm (Fin 3))),
    let θ : (i : Fin 2) → ↥(Ks i) ≃* Equiv.Perm (Fin 3) := fun i => (hθ i).some
    let q : Fin 2 → MulAut ↥(L619.V0 hW (ch6ZS T L V) P) := fun i => (((θ i).symm L619.cyc3 : ↥(Ks
        i)) : MulAut _)
    ∀ (_hqK : ∀ (i : Fin 2), q i ∈ Ks i),
    ∀ (_h3el : ∀ (i : Fin 2), ∀ k ∈ Ks i, (∃ m, k ^ 3 ^ m = 1) → k ∈ Subgroup.zpowers (q i)),
    ∀ (_hinvq : ∀ (i : Fin 2), ∀ t ∈ Ks i, t ^ 2 = 1 → t ≠ 1 → t * q i * t⁻¹ = (q i)⁻¹),
    let T₃ : Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) := Subgroup.closure ({q 0, q 1} : Set
        (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)))
    ∀ (hqT : ∀ (i : Fin 2), q i ∈ T₃),
    let B : Subgroup G := L619.threePart P
    ∀ (_hBP : B ≤ P),
    ∀ (hBN : B ≤ N),
    ∀ (hψBmem : ∀ (b : ↥B), (L619.act0 hW (ch6ZS T L V) P) ⟨↑b, hBN b.property⟩ ∈ T₃),
    let ψB : ↥B →* ↥T₃ := ((L619.act0 hW (ch6ZS T L V) P).comp (Subgroup.inclusion
        hBN)).codRestrict T₃ hψBmem
    ∀ (_hψB : ∀ (b : ↥B), ↑(ψB b) = (L619.act0 hW (ch6ZS T L V) P) ⟨↑b, hBN b.property⟩),
    let qt : Fin 2 → ↥T₃ := fun i => ⟨q i, hqT i⟩
    ∀ (_hgenT : Subgroup.closure {qt 0, qt 1} = ⊤),
    ∀ (_hψBs : Function.Surjective ⇑ψB),
    ∀ (_hDB : ∀ d ∈ D', d ∈ Subgroup.normalizer ↑B),
    ∀ (_hT3exp : ∀ (t : ↥T₃), t ^ (3 : ℕ) = (1 : ↥T₃)),
    ∀ (_hperm' : ∀ (g : G) (hg : g ∈ N) (i : Fin 2), ∃ j, ∀ k ∈ Ks i, (L619.act0 hW (ch6ZS T L V) P)
        ⟨g, hg⟩ * k * ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩)⁻¹ ∈ Ks j),
    ∀ (hTnorm : ∀ (g : G) (hg : g ∈ N), (L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩ ∈
        Subgroup.normalizer ↑T₃),
    let cT : (g : G) → g ∈ N → MulAut ↥T₃ := fun g hg => L619.conjAut (hTnorm g hg)
    ∀ (_hcT : ∀ (g : G) (hg : g ∈ N) (t : ↥T₃), ↑((cT g hg) t) = (L619.act0 hW (ch6ZS T L V) P) ⟨g,
        hg⟩ * ↑t * ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩)⁻¹),
    ∀ (_hcTψ : ∀ (g : G) (hg : g ∈ N) (hgB : g ∈ Subgroup.normalizer ↑B) (b : ↥B), (cT g hg) (ψB b)
        = ψB ((L619.conjIn hgB) b)),
    ∀ (_hzq : ∀ (t : ↥T₃) (i : Fin 2), ↑t ∈ Subgroup.zpowers (q i) → t ∈ Subgroup.zpowers (qt i)),
    ∀ (_hqt3 : ∀ (i : Fin 2), qt i ^ (3 : ℕ) = (1 : ↥T₃)),
    ∀ (_hline : ∀ (g : G) (hg : g ∈ N) (i j : Fin 2), (∀ k ∈ Ks i, (L619.act0 hW (ch6ZS T L V) P)
        ⟨g, hg⟩ * k * ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩)⁻¹ ∈ Ks j) → L619.mapA (cT g hg)
        (Subgroup.zpowers (qt i)) = Subgroup.zpowers (qt j)),
    ∀ (_hs₁ : ∀ (i : Fin 2), ∃ s, ∃ (hs : s ∈ T' ⊓ I), (L619.act0 hW (ch6ZS T L V) P) ⟨s, hIN
        hs.right⟩ ∈ Ks i ∧ (L619.act0 hW (ch6ZS T L V) P) ⟨s, hIN hs.right⟩ ^ 2 = 1 ∧ (L619.act0 hW
        (ch6ZS T L V) P) ⟨s, hIN hs.right⟩ ≠ 1),
    ∀ (σ : G),
    ∀ (hσS : σ ∈ T' ⊓ I),
    ∀ (_hσ01 : ∀ k ∈ Ks 0, (L619.act0 hW (ch6ZS T L V) P) ⟨σ, hIN hσS.right⟩ * k * ((L619.act0 hW
        (ch6ZS T L V) P) ⟨σ, hIN hσS.right⟩)⁻¹ ∈ Ks 1),
    ∀ (_hσ10 : ∀ k ∈ Ks 1, (L619.act0 hW (ch6ZS T L V) P) ⟨σ, hIN hσS.right⟩ * k * ((L619.act0 hW
        (ch6ZS T L V) P) ⟨σ, hIN hσS.right⟩)⁻¹ ∈ Ks 0),
    ∀ (_hqt01 : qt 0 * qt 1 = qt 1 * qt 0),
    ∀ (_hinjqt : ∀ (a b c d : ℕ), a < 3 → b < 3 → c < 3 → d < 3 → qt 0 ^ a * qt 1 ^ b = qt 0 ^ c *
        qt 1 ^ d → a = c ∧ b = d),
    ∀ (_hinjqt' : ∀ (a b c d : ℕ), a < 3 → b < 3 → c < 3 → d < 3 → qt 1 ^ a * qt 0 ^ b = qt 1 ^ c *
        qt 0 ^ d → a = c ∧ b = d),
    ∀ (_hgenT' : Subgroup.closure {qt 1, qt 0} = ⊤),
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro _c I P N Ks hPN hIN φ hkerP hO2P hPI hIP hc01 J X₀ X₁ A₀ A₁ hA₀ hA₁ hinf hA₀P hA₁P hθ θ q
      hqK h3el hinvq T₃ hqT B hBP hBN hψBmem ψB hψB qt hgenT hψBs hDB hT3exp hperm' hTnorm cT hcT
      hcTψ hzq hqt3 hline hs₁ σ hσS hσ01 hσ10 hqt01 hinjqt hinjqt' hgenT'
  have hDA : ∀ d ∈ D', ∀ i : Fin 2,
      d ∈ Subgroup.normalizer (L619.threePart (L619.preimg φ (Ks i)) : Set G) := by
    intro d hdD i
    have hdB := hDB d hdD
    have hkerd : ∀ b : ↥B, ψB b = 1 → ψB (L619.conjIn hdB b) = 1 := by
      intro b hb1
      have hb1' := congrArg Subtype.val hb1
      have hbO : (b : G) ∈ pCoreOf 2 P := hkerP ⟨b, hBP b.2⟩ (Subtype.ext hb1')
      obtain ⟨m, hm⟩ := hO2P ⟨b, hbO⟩
      have hm' : (b : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h2 : (ψB (L619.conjIn hdB b)) ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : (L619.conjIn hdB b) ^ 2 ^ m = 1 := by
          apply Subtype.ext
          rw [SubgroupClass.coe_pow, L619.conjIn_coe, conj_pow, hm', mul_one, mul_inv_cancel]
          rfl
        rw [this, map_one]
      exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_left m (by norm_num))).mp
        ⟨h2, hT3exp _⟩
    obtain ⟨α, hα⟩ := L619.exists_induced_aut ψB hψBs hdB hkerd
    have hα3 : α ^ 3 = 1 := by
      refine MulEquiv.ext fun t => ?_
      obtain ⟨b, rfl⟩ := hψBs t
      have hdd : d * (d * d) = 1 := by rw [← pow_three]; exact hd.pow_three_eq_one hdD
      have hc : L619.conjIn hdB (L619.conjIn hdB (L619.conjIn hdB b)) = b := by
        apply Subtype.ext
        simp only [L619.conjIn_coe]
        calc d * (d * (d * (b : G) * d⁻¹) * d⁻¹) * d⁻¹ = d * (d * d) * b * (d * (d * d))⁻¹ := by
              simp only [mul_inv_rev, mul_assoc]
          _ = b := by rw [hdd, one_mul, inv_one, mul_one]
      show α (α (α (ψB b))) = ψB b
      rw [hα, hα, hα, hc]
    let 𝒮 : Set (MulAut ↥T₃) := {τ | ∃ (s : G) (hs : s ∈ T' ⊓ I), τ = cT s (hIN hs.2)}
    have h𝒮 : ∀ τ ∈ 𝒮, ∀ L, (L = Subgroup.zpowers (qt 0) ∨ L = Subgroup.zpowers (qt 1)) →
        (L619.mapA τ L = Subgroup.zpowers (qt 0) ∨ L619.mapA τ L = Subgroup.zpowers (qt 1)) := by
      rintro τ ⟨s, hs, rfl⟩ L (rfl | rfl)
      · obtain ⟨j, hj⟩ := hperm' s (hIN hs.2) 0
        fin_cases j
        · exact Or.inl (hline s _ 0 0 hj)
        · exact Or.inr (hline s _ 0 1 hj)
      · obtain ⟨j, hj⟩ := hperm' s (hIN hs.2) 1
        fin_cases j
        · exact Or.inl (hline s _ 1 0 hj)
        · exact Or.inr (hline s _ 1 1 hj)
    have h𝒮' : ∀ τ ∈ 𝒮, ∀ L, (L = Subgroup.zpowers (qt 1) ∨ L = Subgroup.zpowers (qt 0)) →
        (L619.mapA τ L = Subgroup.zpowers (qt 1) ∨ L619.mapA τ L = Subgroup.zpowers (qt 0)) :=
      fun τ hτ L hL => (h𝒮 τ hτ L hL.symm).symm
    have hα𝒮 : ∀ τ ∈ 𝒮, ∃ τ' ∈ 𝒮, α * τ' = τ * α := by
      rintro τ ⟨s, hs, rfl⟩
      have hs' : d⁻¹ * s * d⁻¹⁻¹ ∈ T' ⊓ I :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hd.D'_le_S' hdD)) s).mp hs
      refine ⟨cT _ (hIN hs'.2), ⟨_, hs', rfl⟩, MulEquiv.ext fun t => ?_⟩
      obtain ⟨b, rfl⟩ := hψBs t
      have hsB : s ∈ Subgroup.normalizer (B : Set G) :=
        L619.normalizer_le_normalizer_threePart P (hIP hs.2)
      have hs'B : d⁻¹ * s * d⁻¹⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
        L619.normalizer_le_normalizer_threePart P (hIP hs'.2)
      show α (cT _ (hIN hs'.2) (ψB b)) = cT s (hIN hs.2) (α (ψB b))
      rw [hcTψ _ _ hs'B, hα, hα, hcTψ _ _ hsB]
      congr 1
      apply Subtype.ext
      simp only [L619.conjIn_coe]
      group
    have hcT_q : ∀ (s : G) (hs : s ∈ T' ⊓ I) (i j : Fin 2), i ≠ j →
        L619.act0 hW _ P ⟨s, hIN hs.2⟩ ∈ Ks i → L619.act0 hW _ P ⟨s, hIN hs.2⟩ ^ 2 = 1 →
        L619.act0 hW _ P ⟨s, hIN hs.2⟩ ≠ 1 →
        cT s (hIN hs.2) (qt i) = (qt i)⁻¹ ∧ cT s (hIN hs.2) (qt j) = qt j := by
      intro s hs i j hij hsK hs2 hs1
      refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
      · rw [hcT]
        exact hinvq i _ hsK hs2 hs1
      · rw [hcT]
        have hc : L619.act0 hW _ P ⟨s, hIN hs.2⟩ * q j = q j * L619.act0 hW _ P ⟨s, hIN hs.2⟩ := by
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact hc01 _ hsK _ (hqK 1)
          · exact (hc01 _ (hqK 0) _ hsK).symm
          · exact absurd rfl hij
        rw [hc, mul_inv_cancel_right]
    have hαL : ∀ i : Fin 2, L619.mapA α (Subgroup.zpowers (qt i)) = Subgroup.zpowers (qt i) := by
      intro i
      obtain ⟨s₁, hs₁S, hs₁K, hs₁2, hs₁1⟩ := hs₁ i
      fin_cases i
      · obtain ⟨hq0', hq1'⟩ := hcT_q s₁ hs₁S 0 1 (by decide) hs₁K hs₁2 hs₁1
        exact L619.mapA_eq_of_cube hqt01 (hqt3 0) (hqt3 1) hgenT hinjqt 𝒮 h𝒮
          ⟨s₁, hs₁S, rfl⟩ hq0' hq1' ⟨σ, hσS, rfl⟩ (hline σ _ 0 1 hσ01) hα3 hα𝒮
      · obtain ⟨hq1', hq0'⟩ := hcT_q s₁ hs₁S 1 0 (by decide) hs₁K hs₁2 hs₁1
        exact L619.mapA_eq_of_cube hqt01.symm (hqt3 1) (hqt3 0) hgenT' hinjqt' 𝒮 h𝒮'
          ⟨s₁, hs₁S, rfl⟩ hq1' hq0' ⟨σ, hσS, rfl⟩ (hline σ _ 1 0 hσ10) hα3 hα𝒮
    refine mem_normalizer_of_conjSub_le' ?_
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, k, hk⟩
    have hxP : x ∈ P := L619.preimg_le φ _ hxX
    have hxB : x ∈ B := L619.mem_threePart hxP hk
    have hψx : ψB ⟨x, hxB⟩ ∈ Subgroup.zpowers (qt i) := by
      refine hzq _ i (h3el i _ ?_ ⟨k, ?_⟩)
      · obtain ⟨hxP'', hxK⟩ := (L619.mem_preimg φ).mp hxX
        exact hxK
      · have h' : (⟨x, hBN hxB⟩ : ↥N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
        calc ((ψB ⟨x, hxB⟩ : ↥T₃) : MulAut _) ^ 3 ^ k
            = (L619.act0 hW _ P ⟨x, hBN hxB⟩) ^ 3 ^ k := by rw [hψB]
          _ = L619.act0 hW _ P (⟨x, hBN hxB⟩ ^ 3 ^ k) := (map_pow _ _ _).symm
          _ = 1 := by rw [h', map_one]
    have hψdx : ψB (L619.conjIn hdB ⟨x, hxB⟩) ∈ Subgroup.zpowers (qt i) := by
      rw [← hα, ← hαL i]
      exact ⟨_, hψx, rfl⟩
    have hdxP : d * x * d⁻¹ ∈ P := hBP (L619.conjIn hdB ⟨x, hxB⟩).2
    show d * x * d⁻¹ ∈ L619.threePart (L619.preimg φ (Ks i))
    refine L619.mem_threePart ((L619.mem_preimg φ).mpr ⟨hdxP, ?_⟩) (k := k) ?_
    · have h1 : ((ψB (L619.conjIn hdB ⟨x, hxB⟩) : ↥T₃) : MulAut _) ∈ Subgroup.zpowers (q i) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hψdx
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← hn]; rfl⟩
      exact Subgroup.zpowers_le.mpr (hqK i) h1
    · rw [conj_pow, hk, mul_one, mul_inv_cancel]
  exact hd.false_of_comps hA₀ hA₁ hinf (sup_le (hA₀P.trans hPI) (hA₁P.trans hPI))
    (fun d hdD => hDA d hdD 0) (fun d hdD => hDA d hdD 1)

theorem false_of_swap_core2 (hW : IsElemAbelian 2 (ch619W T L V z)) :
    ∀ (_c : Cfg619 T L V H n y),
    let I : Subgroup G := ch619I T L V
    let P : Subgroup G := conjClosure (conjSub y V) (I ⊔ T')
    let N : Subgroup G := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P
    let K : Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) := L619.img0 hW (ch6ZS T L V) P
    ∀ (Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P))),
    ∀ (hPN : P ≤ N),
    ∀ (_hIN : I ≤ N),
    let φ : ↥P →* ↥(L619.img0 hW (ch6ZS T L V) P) := L619.actOn hW (ch6ZS T L V) P hPN fun x =>
        L619.act0_mem_img0 hW (ch6ZS T L V) P x.property
    ∀ (_hφs : Function.Surjective ⇑φ),
    ∀ (_hkerP : ∀ (x : ↥P), φ x = 1 → ↑x ∈ pCoreOf 2 P),
    ∀ (_hO2P : IsPGroup 2 ↥(pCoreOf 2 P)),
    ∀ (_hPI : P ≤ I),
    ∀ (_hIP : I ≤ Subgroup.normalizer ↑P),
    ∀ (_hKi : ∀ (i : Fin 2), Ks i ≤ K),
    ∀ (_hc01 : ∀ a ∈ Ks 0, ∀ b ∈ Ks 1, a * b = b * a),
    ∀ (_hne : Ks 0 ≠ Ks 1),
    ∀ (_hact : ∀ (x p : G) (hx : x ∈ N) (hp : p ∈ N), (L619.act0 hW (ch6ZS T L V) P) ⟨x * p * x⁻¹,
        Subgroup.mul_mem N (Subgroup.mul_mem N hx hp) (Subgroup.inv_mem N hx)⟩ = (L619.act0 hW
        (ch6ZS T L V) P) ⟨x, hx⟩ * (L619.act0 hW (ch6ZS T L V) P) ⟨p, hp⟩ * ((L619.act0 hW (ch6ZS T
        L V) P) ⟨x, hx⟩)⁻¹),
    ∀ (_hcase2 : ∀ (g : G) (hg : g ∈ N) (j : Fin 2), conjSubgroup (Ks j) ((L619.act0 hW (ch6ZS T L
        V) P) ⟨g, hg⟩) = Ks 0 ∨ conjSubgroup (Ks j) ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩) = Ks
        1),
    let J : Subgroup G := L619.oddPart I
    let X₀ : Subgroup G := L619.preimg φ (Ks 0)
    let X₁ : Subgroup G := L619.preimg φ (Ks 1)
    let A₀ : Subgroup G := L619.threePart X₀
    let A₁ : Subgroup G := L619.threePart X₁
    ∀ (_hA₀ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 0)))),
    ∀ (_hA₁ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 1)))),
    ∀ (_hinf : A₀ ⊓ A₁ ≤ pCoreOf 2 A₀),
    ∀ (_hA₀P : A₀ ≤ P),
    ∀ (_hA₁P : A₁ ≤ P),
    ∀ (x₀ : G),
    ∀ (hx₀N : x₀ ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V) P),
    ∀ (_hx₀I : x₀ ∈ I),
    ∀ (_hconj_inj : ∀ (g : MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) (A B : Subgroup (MulAut ↥(L619.V0
        hW (ch6ZS T L V) P))), conjSubgroup A g = conjSubgroup B g → A = B),
    ∀ (_hsw : conjSubgroup (Ks 0) ((L619.act0 hW (ch6ZS T L V) P) ⟨x₀, hx₀N⟩) = Ks 1 ∧ conjSubgroup
        (Ks 1) ((L619.act0 hW (ch6ZS T L V) P) ⟨x₀, hx₀N⟩) = Ks 0),
    ∀ (hθ : ∀ (i : Fin 2), Nonempty (↥(Ks i) ≃* Equiv.Perm (Fin 3))),
    let θ : (i : Fin 2) → ↥(Ks i) ≃* Equiv.Perm (Fin 3) := fun i => (hθ i).some
    let q : Fin 2 → MulAut ↥(L619.V0 hW (ch6ZS T L V) P) := fun i => (((θ i).symm L619.cyc3 : ↥(Ks
        i)) : MulAut _)
    ∀ (_hqK : ∀ (i : Fin 2), q i ∈ Ks i),
    ∀ (_hq3 : ∀ (i : Fin 2), q i ^ 3 = 1),
    ∀ (_hq1 : ∀ (i : Fin 2), q i ≠ 1),
    ∀ (_h3el : ∀ (i : Fin 2), ∀ k ∈ Ks i, (∃ m, k ^ 3 ^ m = 1) → k ∈ Subgroup.zpowers (q i)),
    ∀ (_hinvq : ∀ (i : Fin 2), ∀ t ∈ Ks i, t ^ 2 = 1 → t ≠ 1 → t * q i * t⁻¹ = (q i)⁻¹),
    ∀ (_hq01 : q 0 * q 1 = q 1 * q 0),
    ∀ (_hKdec : ∀ k ∈ K, ∃ a ∈ Ks 0, ∃ b ∈ Ks 1, k = a * b),
    let T₃ : Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) := Subgroup.closure ({q 0, q 1} : Set
        (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)))
    ∀ (hqT : ∀ (i : Fin 2), q i ∈ T₃),
    ∀ (_h3T : ∀ k ∈ K, (∃ m, k ^ 3 ^ m = 1) → k ∈ T₃),
    ∀ (_hinjq : ∀ (a b c d : ℕ), a < 3 → b < 3 → c < 3 → d < 3 → q 0 ^ a * q 1 ^ b = q 0 ^ c * q 1 ^
        d → a = c ∧ b = d),
    let B : Subgroup G := L619.threePart P
    ∀ (_hBP : B ≤ P),
    ∀ (hBN : B ≤ N),
    ∀ (hψBmem : ∀ (b : ↥B), (L619.act0 hW (ch6ZS T L V) P) ⟨↑b, hBN b.property⟩ ∈ T₃),
    let ψB : ↥B →* ↥T₃ := ((L619.act0 hW (ch6ZS T L V) P).comp (Subgroup.inclusion
        hBN)).codRestrict T₃ hψBmem
    ∀ (_hψB : ∀ (b : ↥B), ↑(ψB b) = (L619.act0 hW (ch6ZS T L V) P) ⟨↑b, hBN b.property⟩),
    let qt : Fin 2 → ↥T₃ := fun i => ⟨q i, hqT i⟩
    ∀ (_hqt : qt = fun i => ⟨q i, hqT i⟩),
    ∀ (_hgenT : Subgroup.closure {qt 0, qt 1} = ⊤),
    ∀ (_hψBs : Function.Surjective ⇑ψB),
    ∀ (_hDB : ∀ d ∈ D', d ∈ Subgroup.normalizer ↑B),
    ∀ (_hT3exp : ∀ (t : ↥T₃), t ^ (3 : ℕ) = (1 : ↥T₃)),
    ∀ (_hperm' : ∀ (g : G) (hg : g ∈ N) (i : Fin 2), ∃ j, ∀ k ∈ Ks i, (L619.act0 hW (ch6ZS T L V) P)
        ⟨g, hg⟩ * k * ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩)⁻¹ ∈ Ks j),
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro _c I P N K Ks hPN hIN φ hφs hkerP hO2P hPI hIP hKi hc01 hne hact hcase2 J X₀ X₁ A₀ A₁ hA₀
      hA₁ hinf hA₀P hA₁P x₀ hx₀N hx₀I hconj_inj hsw hθ θ q hqK hq3 hq1 h3el hinvq hq01 hKdec T₃ hqT
      h3T hinjq B hBP hBN hψBmem ψB hψB qt hqt hgenT hψBs hDB hT3exp hperm'
  have hTkey : ∀ (g : G) (hg : g ∈ N), ∀ t ∈ T₃,
      L619.act0 hW _ P ⟨g, hg⟩ * t * (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ ∈ T₃ := by
    intro g hg t ht
    have key : T₃ ≤ T₃.comap (MulAut.conj (L619.act0 hW _ P ⟨g, hg⟩)).toMonoidHom := by
      rw [Subgroup.closure_le]
      have hgen : ∀ i, L619.act0 hW _ P ⟨g, hg⟩ * q i * (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ ∈ T₃ :=
        fun i => h3T _ (L619.act0_conj_mem_img0 hW _ P _ (hKi i (hqK i)))
          ⟨1, by rw [pow_one, conj_pow, hq3, mul_one, mul_inv_cancel]⟩
      rintro _ (rfl | rfl)
      · exact hgen 0
      · exact hgen 1
    exact key ht
  have hTnorm : ∀ (g : G) (hg : g ∈ N),
      L619.act0 hW _ P ⟨g, hg⟩ ∈ Subgroup.normalizer (T₃ : Set (MulAut _)) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.mpr fun t => ⟨hTkey g hg t, fun ht => ?_⟩
    have := hTkey g⁻¹ (N.inv_mem hg) _ ht
    have e : L619.act0 hW _ P ⟨g⁻¹, N.inv_mem hg⟩ = (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e] at this
    simpa [mul_assoc] using this
  let cT : ∀ (g : G), g ∈ N → MulAut ↥T₃ := fun g hg => L619.conjAut (hTnorm g hg)
  have hcT : ∀ (g : G) (hg : g ∈ N) (t : ↥T₃), ((cT g hg t : ↥T₃) : MulAut _) =
      L619.act0 hW _ P ⟨g, hg⟩ * (t : MulAut _) * (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ :=
    fun _ _ _ => rfl
  have hcTψ : ∀ (g : G) (hg : g ∈ N) (hgB : g ∈ Subgroup.normalizer (B : Set G)) (b : ↥B),
      cT g hg (ψB b) = ψB (L619.conjIn hgB b) := by
    intro g hg hgB b
    apply Subtype.ext
    rw [hcT, hψB, hψB]
    exact (hact g b hg (hBN b.2)).symm
  have hzq : ∀ (t : ↥T₃) (i : Fin 2), (t : MulAut _) ∈ Subgroup.zpowers (q i) →
      t ∈ Subgroup.zpowers (qt i) := by
    intro t i ht
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa [hqt] using hn)⟩
  have hqt3 : ∀ i, qt i ^ 3 = 1 := fun i => hT3exp _
  have hqt1 : ∀ i, qt i ≠ 1 := fun i h => hq1 i (congrArg Subtype.val h)
  have hcard_qt : ∀ (τ : MulAut ↥T₃) i, Nat.card (Subgroup.zpowers (τ (qt i))) = 3 := by
    intro τ i
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, orderOf_eq_prime (hqt3 i) (hqt1 i)]
  have hline : ∀ (g : G) (hg : g ∈ N) (i j : Fin 2),
      (∀ k ∈ Ks i, L619.act0 hW _ P ⟨g, hg⟩ * k * (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ ∈ Ks j) →
      L619.mapA (cT g hg) (Subgroup.zpowers (qt i)) = Subgroup.zpowers (qt j) := by
    intro g hg i j hij
    rw [L619.mapA_zpowers]
    have hmem : cT g hg (qt i) ∈ Subgroup.zpowers (qt j) := by
      refine hzq _ j (h3el j _ ?_ ⟨1, ?_⟩)
      · rw [hcT]
        exact hij _ (hqK i)
      · rw [pow_one, ← SubgroupClass.coe_pow, hT3exp]
        rfl
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
    rw [hcard_qt, Nat.card_zpowers, orderOf_eq_prime (hqt3 j) (hqt1 j)]
  have hKnorm : ∀ i, ∀ k ∈ K, ∀ t ∈ Ks i, k * t * k⁻¹ ∈ Ks i := by
    intro i k hk t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := hKdec k hk
    fin_cases i
    · have hbt : b * t = t * b := (hc01 t ht b hb).symm
      have e : a * b * t * (a * b)⁻¹ = a * t * a⁻¹ := by
        calc a * b * t * (a * b)⁻¹ = a * (b * t) * b⁻¹ * a⁻¹ := by group
          _ = a * t * a⁻¹ := by rw [hbt]; group
      rw [e]
      exact (Ks 0).mul_mem ((Ks 0).mul_mem ha ht) ((Ks 0).inv_mem ha)
    · have hbt : b * t * b⁻¹ ∈ Ks 1 := (Ks 1).mul_mem ((Ks 1).mul_mem hb ht) ((Ks 1).inv_mem hb)
      have hcom : a * (b * t * b⁻¹) = b * t * b⁻¹ * a := hc01 a ha _ hbt
      have e : a * b * t * (a * b)⁻¹ = b * t * b⁻¹ := by
        calc a * b * t * (a * b)⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by group
          _ = b * t * b⁻¹ := by rw [hcom]; group
      rw [e]
      exact hbt
  have hS'P : IsSylowTwoOf (T' ⊓ I ⊓ P) P := A4.isSylowTwoOf_inf_normal hd.sylow_S' hPI hIP
  have hUsyl := L619.isSylowTwoOf_map_surj hS'P φ hφs
  have hs₁ : ∀ i : Fin 2, ∃ (s : G) (hs : s ∈ T' ⊓ I),
      L619.act0 hW _ P ⟨s, hIN hs.2⟩ ∈ Ks i ∧ L619.act0 hW _ P ⟨s, hIN hs.2⟩ ^ 2 = 1 ∧
        L619.act0 hW _ P ⟨s, hIN hs.2⟩ ≠ 1 := by
    intro i
    let t : ↥K := ⟨(((θ i).symm (Equiv.swap 0 1) : ↥(Ks i)) : MulAut _), hKi i ((θ i).symm _).2⟩
    have ht : t = ⟨(((θ i).symm (Equiv.swap 0 1) : ↥(Ks i)) : MulAut _),
      hKi i ((θ i).symm _).2⟩ := rfl
    have htK : (t : MulAut _) ∈ Ks i := ((θ i).symm _).2
    have ht2 : t ^ 2 = 1 := by
      apply Subtype.ext
      have : ((θ i).symm (Equiv.swap 0 1)) ^ 2 = 1 := by
        rw [← map_pow, show (Equiv.swap (0 : Fin 3) 1) ^ 2 = 1 by decide, map_one]
      simpa [ht] using congrArg Subtype.val this
    have ht1 : t ≠ 1 := by
      intro h
      have h' : ((θ i).symm (Equiv.swap 0 1) : ↥(Ks i)) = 1 :=
        Subtype.ext (by simpa [ht] using congrArg Subtype.val h)
      have := congrArg (θ i) h'
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact absurd this (by decide)
    have hp : IsPGroup 2 (Subgroup.zpowers t) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime ht2 ht1
    obtain ⟨S₀, hS₀⟩ := hp.exists_le_sylow
    have hUidx : ¬ 2 ∣ (((T' ⊓ I ⊓ P).subgroupOf P).map φ).index := by
      have := hUsyl.2.2
      rwa [show ((((T' ⊓ I ⊓ P).subgroupOf P).map φ).subgroupOf ⊤).index =
        (((T' ⊓ I ⊓ P).subgroupOf P).map φ).index from Subgroup.relIndex_top_right _] at this
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥K S₀ (hUsyl.2.1.toSylow hUidx)
    have hkt : k * t * k⁻¹ ∈ ((T' ⊓ I ⊓ P).subgroupOf P).map φ := by
      have hmem : k * t * k⁻¹ ∈ ((k • S₀ : Sylow 2 ↥K) : Subgroup ↥K) :=
        Subgroup.smul_mem_pointwise_smul t (MulAut.conj k) (S₀ : Subgroup ↥K)
          (hS₀ (Subgroup.mem_zpowers t))
      rw [hk] at hmem
      simpa using hmem
    obtain ⟨⟨s, hsP⟩, hs, hsk⟩ := hkt
    have hs' : s ∈ T' ⊓ I ⊓ P := hs
    have hact_s : L619.act0 hW _ P ⟨s, hIN hs'.1.2⟩ = ((k * t * k⁻¹ : ↥K) : MulAut _) :=
      congrArg Subtype.val hsk
    refine ⟨s, hs'.1, ?_, ?_, ?_⟩
    · rw [hact_s]
      exact hKnorm i _ k.2 _ htK
    · rw [hact_s, ← SubgroupClass.coe_pow, conj_pow, ht2, mul_one, mul_inv_cancel]
      rfl
    · rw [hact_s]
      intro h1
      apply ht1
      have h1' : k * t * k⁻¹ = 1 := Subtype.ext h1
      rwa [conj_eq_one_iff] at h1'
  have hσ : ∃ (s : G) (hs : s ∈ T' ⊓ I),
      conjSubgroup (Ks 0) (L619.act0 hW _ P ⟨s, hIN hs.2⟩) = Ks 1 := by
    by_contra hcon
    push Not at hcon
    have hact1 : L619.act0 hW _ P ⟨1, hIN I.one_mem⟩ = 1 := map_one _
    have hactm : ∀ (a b : G) (ha : a ∈ I) (hb : b ∈ I),
        L619.act0 hW _ P ⟨a * b, hIN (I.mul_mem ha hb)⟩ =
          L619.act0 hW _ P ⟨a, hIN ha⟩ * L619.act0 hW _ P ⟨b, hIN hb⟩ := fun a b ha hb => by
      rw [← map_mul]
      rfl
    have hacti : ∀ (a : G) (ha : a ∈ I),
        L619.act0 hW _ P ⟨a⁻¹, hIN (I.inv_mem ha)⟩ = (L619.act0 hW _ P ⟨a, hIN ha⟩)⁻¹ :=
      fun a ha => by
        rw [← map_inv]
        rfl
    let I₀ : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ I, conjSubgroup (Ks 0) (L619.act0 hW _ P ⟨x, hIN hx⟩) = Ks 0}
        one_mem' := ⟨I.one_mem, by rw [hact1, conjSubgroup_one]⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨I.mul_mem ha hb, ?_⟩
          rw [hactm a b ha hb, ← conjSubgroup_conjSubgroup, ha', hb']
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          refine ⟨I.inv_mem ha, ?_⟩
          rw [hacti a ha]
          nth_rewrite 1 [← ha']
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] }
    have hI₀ : ∀ (x : G) (hx : x ∈ I), x ∈ I₀ ↔
        conjSubgroup (Ks 0) (L619.act0 hW _ P ⟨x, hIN hx⟩) = Ks 0 := fun x hx =>
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩
    have hnot0 : ∀ (x : G) (hx : x ∈ I), x ∉ I₀ →
        conjSubgroup (Ks 0) (L619.act0 hW _ P ⟨x, hIN hx⟩) = Ks 1 := fun x hx hxI₀ =>
      (hcase2 x (hIN hx) 0).resolve_left fun h => hxI₀ ((hI₀ x hx).mpr h)
    have hS'I₀ : T' ⊓ I ≤ I₀ := fun s hs =>
      (hI₀ s hs.2).mpr ((hcase2 s (hIN hs.2) 0).resolve_right (hcon s hs))
    have hx₀I₀ : x₀ ∉ I₀ := fun h => hne ((hI₀ x₀ hx₀I).mp h ▸ hsw.1)
    have hidx : (I₀.subgroupOf I).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x₀, hx₀I⟩, fun b => ?_⟩
      have hbI : (b : G) ∈ I := b.2
      by_cases hb : (b : G) ∈ I₀
      · refine Or.inr ⟨hb, fun hbx => ?_⟩
        have h1 := (hI₀ _ (I.mul_mem hbI hx₀I)).mp hbx
        rw [hactm _ _ hbI hx₀I, ← conjSubgroup_conjSubgroup, (hI₀ _ hbI).mp hb, hsw.1] at h1
        exact hne h1.symm
      · refine Or.inl ⟨?_, hb⟩
        show (b : G) * x₀ ∈ I₀
        refine (hI₀ _ (I.mul_mem hbI hx₀I)).mpr ?_
        rw [hactm _ _ hbI hx₀I, ← conjSubgroup_conjSubgroup, hnot0 _ hbI hb, hsw.2]
    have hdvd : (I₀.subgroupOf I).index ∣ ((T' ⊓ I).subgroupOf I).index :=
      Subgroup.index_dvd_of_le fun s hs => hS'I₀ hs
    rw [hidx] at hdvd
    exact hd.sylow_S'.2.2 hdvd
  obtain ⟨σ, hσS, hσ0⟩ := hσ
  have hσ1 : conjSubgroup (Ks 1) (L619.act0 hW _ P ⟨σ, hIN hσS.2⟩) = Ks 0 := by
    rcases hcase2 σ (hIN hσS.2) 1 with h1 | h1
    · exact h1
    · exact absurd (hconj_inj _ _ _ (hσ0.trans h1.symm)) hne
  have hσ01 : ∀ k ∈ Ks 0, L619.act0 hW _ P ⟨σ, hIN hσS.2⟩ * k *
      (L619.act0 hW _ P ⟨σ, hIN hσS.2⟩)⁻¹ ∈ Ks 1 := fun k hk =>
    mem_conjSubgroup_iff.mp (hσ1.symm ▸ hk)
  have hσ10 : ∀ k ∈ Ks 1, L619.act0 hW _ P ⟨σ, hIN hσS.2⟩ * k *
      (L619.act0 hW _ P ⟨σ, hIN hσS.2⟩)⁻¹ ∈ Ks 0 := fun k hk =>
    mem_conjSubgroup_iff.mp (hσ0.symm ▸ hk)
  have hqt01 : qt 0 * qt 1 = qt 1 * qt 0 := Subtype.ext hq01
  have hinjqt : ∀ a b c d : ℕ, a < 3 → b < 3 → c < 3 → d < 3 →
      qt 0 ^ a * qt 1 ^ b = qt 0 ^ c * qt 1 ^ d → a = c ∧ b = d := fun a b c d ha hb hc hd he =>
    hinjq a b c d ha hb hc hd (by simpa [hqt] using congrArg Subtype.val he)
  have hinjqt' : ∀ a b c d : ℕ, a < 3 → b < 3 → c < 3 → d < 3 →
      qt 1 ^ a * qt 0 ^ b = qt 1 ^ c * qt 0 ^ d → a = c ∧ b = d := by
    intro a b c d ha hb hc hd he
    rw [((Commute.pow_pow hqt01.symm a b)).eq, ((Commute.pow_pow hqt01.symm c d)).eq] at he
    exact (hinjqt b a d c hb ha hd hc he).symm
  have hgenT' : Subgroup.closure ({qt 1, qt 0} : Set ↥T₃) = ⊤ := by
    rw [Set.pair_comm]
    exact hgenT
  exact hd.false_of_swap_core3 hW _c Ks hPN hIN hkerP hO2P hPI hIP hc01 hA₀ hA₁ hinf hA₀P hA₁P hθ
      hqK h3el hinvq hqT hBP hBN hψBmem hψB hgenT hψBs hDB hT3exp hperm' hTnorm hcT hcTψ hzq hqt3
      hline hs₁ σ hσS hσ01 hσ10 hqt01 hinjqt hinjqt' hgenT'

theorem false_of_swap_core (hW : IsElemAbelian 2 (ch619W T L V z)) :
    ∀ (_c : Cfg619 T L V H n y),
    let I : Subgroup G := ch619I T L V
    let P : Subgroup G := conjClosure (conjSub y V) (I ⊔ T')
    let N : Subgroup G := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P
    let K : Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) := L619.img0 hW (ch6ZS T L V) P
    ∀ (Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P))),
    ∀ (hPN : P ≤ N),
    ∀ (hIN : I ≤ N),
    let φ : ↥P →* ↥(L619.img0 hW (ch6ZS T L V) P) := L619.actOn hW (ch6ZS T L V) P hPN fun x =>
        L619.act0_mem_img0 hW (ch6ZS T L V) P x.property
    ∀ (_hφs : Function.Surjective ⇑φ),
    ∀ (_hkerP : ∀ (x : ↥P), φ x = 1 → ↑x ∈ pCoreOf 2 P),
    ∀ (_hO2P : IsPGroup 2 ↥(pCoreOf 2 P)),
    ∀ (_hPI : P ≤ I),
    ∀ (_hIP : I ≤ Subgroup.normalizer ↑P),
    ∀ (_hKi : ∀ (i : Fin 2), Ks i ≤ K),
    ∀ (_hc01 : ∀ a ∈ Ks 0, ∀ b ∈ Ks 1, a * b = b * a),
    ∀ (_hne : Ks 0 ≠ Ks 1),
    ∀ (_hact : ∀ (x p : G) (hx : x ∈ N) (hp : p ∈ N), (L619.act0 hW (ch6ZS T L V) P) ⟨x * p * x⁻¹,
        Subgroup.mul_mem N (Subgroup.mul_mem N hx hp) (Subgroup.inv_mem N hx)⟩ = (L619.act0 hW
        (ch6ZS T L V) P) ⟨x, hx⟩ * (L619.act0 hW (ch6ZS T L V) P) ⟨p, hp⟩ * ((L619.act0 hW (ch6ZS T
        L V) P) ⟨x, hx⟩)⁻¹),
    ∀ (_hQ2 : ∀ (g : G) (hg : g ∈ N), (∀ (i : Fin 2), ∃ j, conjSubgroup (Ks i) ((L619.act0 hW (ch6ZS
        T L V) P) ⟨g, hg⟩) = Ks j) ∧ ((∀ (i : Fin 2), conjSubgroup (Ks i) ((L619.act0 hW (ch6ZS T L
        V) P) ⟨g, hg⟩) = Ks i) → (L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩ ∈ K)),
    ∀ (_hcase2 : ∀ (g : G) (hg : g ∈ N) (j : Fin 2), conjSubgroup (Ks j) ((L619.act0 hW (ch6ZS T L
        V) P) ⟨g, hg⟩) = Ks 0 ∨ conjSubgroup (Ks j) ((L619.act0 hW (ch6ZS T L V) P) ⟨g, hg⟩) = Ks
        1),
    ∀ (_hnormX : ∀ (i : Fin 2) (x : G) (hxI : x ∈ I), (∀ k ∈ Ks i, (L619.act0 hW (ch6ZS T L V) P)
        ⟨x, hIN hxI⟩ * k * ((L619.act0 hW (ch6ZS T L V) P) ⟨x, hIN hxI⟩)⁻¹ ∈ Ks i) → x ∈
        Subgroup.normalizer ↑(L619.preimg φ (Ks i))),
    ∀ (_hoddfix : ∀ (x : G) (hxI : x ∈ I), Odd (orderOf x) → ∀ (i : Fin 2), ∀ k ∈ Ks i, (L619.act0
        hW (ch6ZS T L V) P) ⟨x, hIN hxI⟩ * k * ((L619.act0 hW (ch6ZS T L V) P) ⟨x, hIN hxI⟩)⁻¹ ∈ Ks
        i),
    let J : Subgroup G := L619.oddPart I
    let X₀ : Subgroup G := L619.preimg φ (Ks 0)
    let X₁ : Subgroup G := L619.preimg φ (Ks 1)
    let A₀ : Subgroup G := L619.threePart X₀
    let A₁ : Subgroup G := L619.threePart X₁
    ∀ (_hA₀ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 0)))),
    ∀ (_hA₁ : L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks 1)))),
    ∀ (_hinf : A₀ ⊓ A₁ ≤ pCoreOf 2 A₀),
    ∀ (_hA₀P : A₀ ≤ P),
    ∀ (_hA₁P : A₁ ≤ P),
    ∀ (x₀ : G),
    ∀ (hx₀N : x₀ ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V) P),
    ∀ (_hx₀I : x₀ ∈ I),
    ∀ (_hconj_inj : ∀ (g : MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) (A B : Subgroup (MulAut ↥(L619.V0
        hW (ch6ZS T L V) P))), conjSubgroup A g = conjSubgroup B g → A = B),
    ∀ (_hsw : conjSubgroup (Ks 0) ((L619.act0 hW (ch6ZS T L V) P) ⟨x₀, hx₀N⟩) = Ks 1 ∧ conjSubgroup
        (Ks 1) ((L619.act0 hW (ch6ZS T L V) P) ⟨x₀, hx₀N⟩) = Ks 0),
    ∀ (_hcard_conj : ∀ (g : MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) (A : Subgroup (MulAut ↥(L619.V0 hW
        (ch6ZS T L V) P))), Nat.card ↥(conjSubgroup A g) = Nat.card ↥A),
    ∀ (hθ : ∀ (i : Fin 2), Nonempty (↥(Ks i) ≃* Equiv.Perm (Fin 3))),
    let θ : (i : Fin 2) → ↥(Ks i) ≃* Equiv.Perm (Fin 3) := fun i => (hθ i).some
    let q : Fin 2 → MulAut ↥(L619.V0 hW (ch6ZS T L V) P) := fun i => (((θ i).symm L619.cyc3 : ↥(Ks
        i)) : MulAut _)
    ∀ (_hqK : ∀ (i : Fin 2), q i ∈ Ks i),
    ∀ (_hq3 : ∀ (i : Fin 2), q i ^ 3 = 1),
    ∀ (_hq1 : ∀ (i : Fin 2), q i ≠ 1),
    ∀ (_h3el : ∀ (i : Fin 2), ∀ k ∈ Ks i, (∃ m, k ^ 3 ^ m = 1) → k ∈ Subgroup.zpowers (q i)),
    ∀ (_hinvq : ∀ (i : Fin 2), ∀ t ∈ Ks i, t ^ 2 = 1 → t ≠ 1 → t * q i * t⁻¹ = (q i)⁻¹),
    ∀ (_hq01 : q 0 * q 1 = q 1 * q 0),
    ∀ (_hKdec : ∀ k ∈ K, ∃ a ∈ Ks 0, ∃ b ∈ Ks 1, k = a * b),
    let T₃ : Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) := Subgroup.closure ({q 0, q 1} : Set
        (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)))
    ∀ (_hqT : ∀ (i : Fin 2), q i ∈ T₃),
    ∀ (_h3T : ∀ k ∈ K, (∃ m, k ^ 3 ^ m = 1) → k ∈ T₃),
    ∀ (_hinjq : ∀ (a b c d : ℕ), a < 3 → b < 3 → c < 3 → d < 3 → q 0 ^ a * q 1 ^ b = q 0 ^ c * q 1 ^
        d → a = c ∧ b = d),
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro _c I P N K Ks hPN hIN φ hφs hkerP hO2P hPI hIP hKi hc01 hne hact hQ2 hcase2 hnormX hoddfix J
      X₀ X₁ A₀ A₁ hA₀ hA₁ hinf hA₀P hA₁P x₀ hx₀N hx₀I hconj_inj hsw hcard_conj hθ θ q hqK hq3 hq1
      h3el hinvq hq01 hKdec T₃ hqT h3T hinjq
  let B : Subgroup G := L619.threePart P
  have hBP : B ≤ P := L619.threePart_le P
  have hBN : B ≤ N := hBP.trans hPN
  have hBT : B ≤ (T₃.comap (L619.act0 hW _ P)).map N.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxP, k, hk⟩
    refine ⟨⟨x, hPN hxP⟩, ?_, rfl⟩
    refine h3T _ (L619.act0_mem_img0 hW _ P (g := ⟨x, hPN hxP⟩) hxP) ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨x, hPN hxP⟩ : ↥N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hψBmem : ∀ b : ↥B, L619.act0 hW _ P ⟨b, hBN b.2⟩ ∈ T₃ := by
    intro b
    obtain ⟨n, hn, hnb⟩ := hBT b.2
    have : n = ⟨b, hBN b.2⟩ := Subtype.ext hnb
    rw [← this]
    exact hn
  let ψB : ↥B →* ↥T₃ :=
    ((L619.act0 hW _ P).comp (Subgroup.inclusion hBN)).codRestrict T₃ hψBmem
  have hψB : ∀ b : ↥B, ((ψB b : ↥T₃) : MulAut _) = L619.act0 hW _ P ⟨b, hBN b.2⟩ :=
    fun b => rfl
  let qt : Fin 2 → ↥T₃ := fun i => ⟨q i, hqT i⟩
  have hqt : qt = fun i => ⟨q i, hqT i⟩ := rfl
  have hgenT : Subgroup.closure ({qt 0, qt 1} : Set ↥T₃) = ⊤ := by
    have := Subgroup.closure_closure_coe_preimage (k := ({q 0, q 1} : Set (MulAut _)))
    convert this using 2
    ext t
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, hqt]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (h | h)
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
  have hψBs : Function.Surjective ψB := by
    have hqim : ∀ i, qt i ∈ ψB.range := by
      intro i
      obtain ⟨x, hx, hxk, -⟩ := L619.exists_threePart_lift φ hφs (k := ⟨q i, hKi i (hqK i)⟩)
        (j := 1) (Subtype.ext (by simpa using hq3 i))
      have hxk' := congrArg Subtype.val hxk
      exact ⟨⟨x, hx⟩, Subtype.ext hxk'⟩
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgenT, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hqim 0
    · exact hqim 1
  let C : Subgroup G := ((L619.act0 hW _ P).ker.map N.subtype) ⊓ I
  have hCact : ∀ c ∈ C, ∃ hcI : c ∈ I, L619.act0 hW _ P ⟨c, hIN hcI⟩ = 1 := by
    intro c hc
    obtain ⟨hc1, hcI⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.mp hc1
    refine ⟨hcI, ?_⟩
    have : n = ⟨c, hIN hcI⟩ := Subtype.ext hnc
    rw [← this]
    exact hn
  have hCcop : ∀ c ∈ C, Nat.Coprime (orderOf c) 3 := by
    intro c hc
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    intro h3
    have hco : orderOf (c ^ (orderOf c / 3)) = 3 :=
      orderOf_pow_orderOf_div (isOfFinOrder_of_finite c).orderOf_pos.ne' h3
    have hc'C : c ^ (orderOf c / 3) ∈ C := C.pow_mem hc _
    generalize c ^ (orderOf c / 3) = c' at hco hc'C
    obtain ⟨hc'I, hc'1⟩ := hCact c' hc'C
    have hc'P : c' ∉ P := by
      intro hc'P
      have hO := hkerP ⟨c', hc'P⟩ (Subtype.ext hc'1)
      obtain ⟨b, hb⟩ := hO2P ⟨c', hO⟩
      have hb' : c' ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have := orderOf_dvd_of_pow_eq_one hb'
      rw [hco] at this
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    have hfix' : ∀ i, ∀ k ∈ Ks i, L619.act0 hW _ P ⟨c', hIN hc'I⟩ * k *
        (L619.act0 hW _ P ⟨c', hIN hc'I⟩)⁻¹ ∈ Ks i := fun i k hk => by
      rw [hc'1, one_mul, inv_one, mul_one]
      exact hk
    have hDA : ∀ i, Subgroup.zpowers c' ≤
        Subgroup.normalizer (L619.threePart (L619.preimg φ (Ks i)) : Set G) := fun i =>
      Subgroup.zpowers_le.mpr (L619.normalizer_le_normalizer_threePart _
        (hnormX i c' hc'I (hfix' i)))
    have hDinf : Subgroup.zpowers c' ⊓ P = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers c' ⊓ P) ∣ 3 := by
        rw [← hco, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hc'P
        have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
          Subgroup.zpowers c' ⊓ P ≤ Subgroup.zpowers c')
          (by rw [h3', Nat.card_zpowers, hco])
        exact (heq ▸ (inf_le_right : Subgroup.zpowers c' ⊓ P ≤ P)) (Subgroup.mem_zpowers c')
    have h3r : 3 ≤ CFSG.Open.pRank 3 (A₀ ⊔ A₁ ⊔ Subgroup.zpowers c') :=
      L619.three_le_pRank_of_two_comps hA₀ hA₁ hinf (sup_le hA₀P hA₁P)
      (Subgroup.zpowers_le.mpr (hIP hc'I)) hDinf (by rw [Nat.card_zpowers, hco]) (hDA 0)
      (hDA 1)
    have hle : A₀ ⊔ A₁ ⊔ Subgroup.zpowers c' ≤ I :=
      sup_le (sup_le (hA₀P.trans hPI) (hA₁P.trans hPI)) (Subgroup.zpowers_le.mpr hc'I)
    have := (CFSG.SectionRank.pRank_mono (by norm_num) hle).trans hd.rank_I
    omega
  have hIB : L619.threePart I ≤ B := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxI, k, hk⟩
    have hxodd : Odd (orderOf x) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
      rw [hj]
      exact Odd.pow (by decide)
    have hfixx : ∀ i, conjSubgroup (Ks i) (L619.act0 hW _ P ⟨x, hIN hxI⟩) = Ks i := by
      intro i
      have hle : Ks i ≤ conjSubgroup (Ks i) (L619.act0 hW _ P ⟨x, hIN hxI⟩) := fun k hk =>
        mem_conjSubgroup_iff.mpr (hoddfix x hxI hxodd i k hk)
      refine le_antisymm ?_ hle
      have := hcard_conj (L619.act0 hW _ P ⟨x, hIN hxI⟩) (Ks i)
      exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq this)).symm.le
    have hxK : L619.act0 hW _ P ⟨x, hIN hxI⟩ ∈ K := (hQ2 x (hIN hxI)).2 hfixx
    have hxT : L619.act0 hW _ P ⟨x, hIN hxI⟩ ∈ T₃ := h3T _ hxK ⟨k, by
      rw [← map_pow]
      have : (⟨x, hIN hxI⟩ : ↥N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]⟩
    obtain ⟨b, hb⟩ := hψBs ⟨_, hxT⟩
    have hbx : (b : G)⁻¹ * x ∈ C := by
      have hbI : (b : G) ∈ I := hPI (hBP b.2)
      refine ⟨⟨⟨(b : G)⁻¹ * x, N.mul_mem (N.inv_mem (hBN b.2)) (hIN hxI)⟩, ?_, rfl⟩,
        I.mul_mem (I.inv_mem hbI) hxI⟩
      have hb' : L619.act0 hW _ P ⟨b, hBN b.2⟩ = L619.act0 hW _ P ⟨x, hIN hxI⟩ :=
        congrArg Subtype.val hb
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have e : (⟨(b : G)⁻¹ * x, N.mul_mem (N.inv_mem (hBN b.2)) (hIN hxI)⟩ : ↥N) =
          (⟨b, hBN b.2⟩ : ↥N)⁻¹ * ⟨x, hIN hxI⟩ := rfl
      rw [e, map_mul, map_inv, hb', inv_mul_cancel]
    have hBnorm : C ≤ Subgroup.normalizer (B : Set G) := fun c hc =>
      L619.normalizer_le_normalizer_threePart P (hIP hc.2)
    have hxBC : x ∈ B ⊔ C := by
      have e : x = (b : G) * ((b : G)⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left b.2) (Subgroup.mem_sup_right hbx)
    exact L619.mem_of_pow_three_eq_one_of_coprime hCcop hBnorm hxBC hk
  have hBI : B ≤ L619.threePart I := Subgroup.closure_mono fun x ⟨hxP, k, hk⟩ =>
    ⟨hPI hxP, k, hk⟩
  have hBeq : L619.threePart I = B := le_antisymm hIB hBI
  have hDB : ∀ d ∈ D', d ∈ Subgroup.normalizer (B : Set G) := fun d hdD => by
    rw [← hBeq]
    exact L619.normalizer_le_normalizer_threePart I (hd.D'_le_I hdD)
  have hT3exp : ∀ t : ↥T₃, t ^ 3 = 1 := by
    intro t
    obtain ⟨i, j, -, -, hij⟩ := L619.exists_pow_mul_pow hq01 (hq3 0) (hq3 1) t.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hij, ((Commute.pow_pow hq01 i j)).mul_pow, ← pow_mul, ← pow_mul,
      mul_comm i 3, mul_comm j 3, pow_mul, pow_mul, hq3, hq3, one_pow, one_pow, one_mul]
    rfl
  have hperm' : ∀ (g : G) (hg : g ∈ N) (i : Fin 2), ∃ j : Fin 2,
      ∀ k ∈ Ks i, L619.act0 hW _ P ⟨g, hg⟩ * k * (L619.act0 hW _ P ⟨g, hg⟩)⁻¹ ∈ Ks j := by
    intro g hg i
    have key : ∃ j : Fin 2, conjSubgroup (Ks j) (L619.act0 hW _ P ⟨g, hg⟩) = Ks i := by
      rcases hcase2 g hg 0 with h0 | h0 <;> rcases hcase2 g hg 1 with h1 | h1
      · exact absurd (hconj_inj _ _ _ (h0.trans h1.symm)) hne
      · fin_cases i
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · fin_cases i
        · exact ⟨1, h1⟩
        · exact ⟨0, h0⟩
      · exact absurd (hconj_inj _ _ _ (h0.trans h1.symm)) hne
    obtain ⟨j, hj⟩ := key
    exact ⟨j, fun k hk => mem_conjSubgroup_iff.mp (hj.symm ▸ hk)⟩
  exact hd.false_of_swap_core2 hW _c Ks hPN hIN hφs hkerP hO2P hPI hIP hKi hc01 hne hact hcase2 hA₀
      hA₁ hinf hA₀P hA₁P x₀ hx₀N hx₀I hconj_inj hsw hθ hqK hq3 hq1 h3el hinvq hq01 hKdec hqT h3T
      hinjq hBP hBN hψBmem hψB hqt hgenT hψBs hDB hT3exp hperm'

theorem false_of_swap (h : Hyp6116 G T M L V n) (h432 : Stmt4_3_2)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    (hND : L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks)
    (hswap : ∃ (x : G) (hx : x ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V)
          (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))), x ∈ ch619I T L V ∧
        ∃ i, ∃ k ∈ Ks i, L619.act0 hW _ _ ⟨x, hx⟩ * k * (L619.act0 hW _ _ ⟨x, hx⟩)⁻¹ ∉ Ks i)
    (h6 : ∃ i, Nat.card (Ks i) = 6) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P with hN
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  intro Ks hdec hND hswap h6
  have hPN : P ≤ N := c.conjClosure_E_le_normWZX hY
  have hIN : I ≤ N := hY.I_le.trans (Cfg619.Y_le_normWZX hY)
  set φ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hφ
  have hφs : Function.Surjective φ := L619.actOn_surjective hW _ P hPN
  have hφ1 : ∀ x : ↥P, φ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hPK2 := hd.pCoreOf_of_two h h432 hW hdec
  have hkerP : ∀ x : ↥P, φ x = 1 → (x : G) ∈ pCoreOf 2 P := fun x hx =>
    hPK2 ⟨x.2, (hφ1 x).mp hx⟩
  have hO2P : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hKi : ∀ i, Ks i ≤ K := fun i => by rw [← hdec.iSup_eq]; exact le_iSup Ks i
  have hsup : Ks 0 ⊔ Ks 1 = K := by rw [← hdec.iSup_eq, G6.iSup_fin_two]
  have hc01 : ∀ a ∈ Ks 0, ∀ b ∈ Ks 1, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hdec.centralize 0 1 (by decide) ha) b hb).symm
  have hdisj : Ks 0 ⊓ Ks 1 = ⊥ :=
    disjoint_iff.mp (hdec.indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
  have hne : Ks 0 ≠ Ks 1 := by
    intro heq
    apply hdec.ne_bot 0
    rw [← inf_idem (Ks 0)]
    nth_rewrite 2 [heq]
    exact hdisj
  have hact : ∀ (x p : G) (hx : x ∈ N) (hp : p ∈ N),
      L619.act0 hW _ P ⟨x * p * x⁻¹, N.mul_mem (N.mul_mem hx hp) (N.inv_mem hx)⟩ =
        L619.act0 hW _ P ⟨x, hx⟩ * L619.act0 hW _ P ⟨p, hp⟩ * (L619.act0 hW _ P ⟨x, hx⟩)⁻¹ := by
    intro x p hx hp
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hQ2 : ∀ (g : G) (hg : g ∈ N), (∀ i, ∃ j, conjSubgroup (Ks i) (L619.act0 hW _ P ⟨g, hg⟩) =
      Ks j) ∧ ((∀ i, conjSubgroup (Ks i) (L619.act0 hW _ P ⟨g, hg⟩) = Ks i) →
        L619.act0 hW _ P ⟨g, hg⟩ ∈ K) := fun g hg => hND ⟨g, hg⟩
  have hcase2 : ∀ (g : G) (hg : g ∈ N) (j : Fin 2),
      conjSubgroup (Ks j) (L619.act0 hW _ P ⟨g, hg⟩) = Ks 0 ∨
        conjSubgroup (Ks j) (L619.act0 hW _ P ⟨g, hg⟩) = Ks 1 := by
    intro g hg j
    obtain ⟨l, hl⟩ := (hQ2 g hg).1 j
    fin_cases l
    · exact Or.inl hl
    · exact Or.inr hl
  have hnormX : ∀ i (x : G) (hxI : x ∈ I),
      (∀ k ∈ Ks i, L619.act0 hW _ P ⟨x, hIN hxI⟩ * k * (L619.act0 hW _ P ⟨x, hIN hxI⟩)⁻¹ ∈ Ks i) →
      x ∈ Subgroup.normalizer (L619.preimg φ (Ks i) : Set G) := by
    intro i x hxI hfix
    refine H13.mem_normalizer_of_forall_conj_mem_of_le fun p hp => ?_
    obtain ⟨hpP, hpK⟩ := (L619.mem_preimg φ).mp hp
    have hxp : x * p * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hIP hxI) p).mp hpP
    refine (L619.mem_preimg φ).mpr ⟨hxp, ?_⟩
    have e := hact x p (hIN hxI) (hPN hpP)
    show L619.act0 hW _ P ⟨x * p * x⁻¹, hPN hxp⟩ ∈ Ks i
    rw [e]
    exact hfix _ hpK
  have hoddfix : ∀ (x : G) (hxI : x ∈ I), Odd (orderOf x) → ∀ i,
      ∀ k ∈ Ks i, L619.act0 hW _ P ⟨x, hIN hxI⟩ * k * (L619.act0 hW _ P ⟨x, hIN hxI⟩)⁻¹ ∈ Ks i := by
    intro x hxI hodd i k hk
    set g := L619.act0 hW _ P ⟨x, hIN hxI⟩ with hg
    have hgodd : Odd (orderOf g) := Odd.of_dvd_nat hodd (by
      rw [hg, ← Subgroup.orderOf_mk x (hIN hxI)]
      exact orderOf_map_dvd _ _)
    have hfix : conjSubgroup (Ks i) g = Ks i := by
      fin_cases i
      · exact L619.conjSubgroup_eq_of_odd hne hgodd (hcase2 x (hIN hxI) 0)
          (hcase2 x (hIN hxI) 1)
      · exact L619.conjSubgroup_eq_of_odd hne.symm hgodd ((hcase2 x (hIN hxI) 1).symm)
          ((hcase2 x (hIN hxI) 0).symm)
    have : k ∈ conjSubgroup (Ks i) g := by rw [hfix]; exact hk
    exact mem_conjSubgroup_iff.mp this
  set J := L619.oddPart I with hJ
  have hJI : J ≤ I := L619.oddPart_le I
  have hIJ : I ≤ Subgroup.normalizer (J : Set G) := fun x hx =>
    L619.mem_normalizer_oddPart (Subgroup.le_normalizer hx)
  have hcomp : ∀ i : Fin 2, L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks i))) := by
    intro i
    obtain ⟨Kt, _, _, hS, ⟨θ⟩⟩ := L619.exists_smallFacts (hdec.small rfl i)
    set X := L619.preimg φ (Ks i) with hX
    have hXP : X ≤ P := L619.preimg_le φ (Ks i)
    set ψ : ↥X →* Kt := θ.toMonoidHom.comp (L619.preimgHom φ (Ks i) (hKi i)) with hψ
    have hψs : Function.Surjective ψ :=
      θ.surjective.comp (L619.preimgHom_surjective φ hφs (Ks i) (hKi i))
    have hψ1 : ∀ x : ↥X, ψ x = 1 ↔ φ ⟨x, hXP x.2⟩ = 1 := by
      intro x
      rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        L619.preimgHom_eq_one_iff]
    have hker : IsPGroup 2 ψ.ker := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := hO2P ⟨(x : G), hkerP _ ((hψ1 x).mp hx)⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
    have h9 : ¬ 9 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
    have h3 : 3 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
    have hJX : J ≤ Subgroup.normalizer (X : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxI, hodd⟩
      exact hnormX i x hxI (hoddfix x hxI hodd i)
    exact L619.threeComp_of ψ (L619.threePart_le_oddPart (hXP.trans hPI)) hJX hψs hker
      hS.simple h9 h3
  set X₀ := L619.preimg φ (Ks 0) with hX₀
  set X₁ := L619.preimg φ (Ks 1) with hX₁
  set A₀ := L619.threePart X₀ with hA₀def
  set A₁ := L619.threePart X₁ with hA₁def
  have hA₀ := hcomp 0
  have hA₁ := hcomp 1
  have hinf : A₀ ⊓ A₁ ≤ pCoreOf 2 A₀ := by
    have h2 : IsPGroup 2 ↥(A₀ ⊓ A₁) := by
      rintro ⟨x, hx₀, hx₁⟩
      obtain ⟨hxP, hxK₀⟩ := (L619.mem_preimg φ).mp (L619.threePart_le _ hx₀)
      obtain ⟨hxP', hxK₁⟩ := (L619.mem_preimg φ).mp (L619.threePart_le _ hx₁)
      have h1 : ((φ ⟨x, hxP⟩ : ↥K) : MulAut _) ∈ Ks 0 ⊓ Ks 1 := ⟨hxK₀, hxK₁⟩
      rw [hdisj, Subgroup.mem_bot] at h1
      obtain ⟨k, hk⟩ := hO2P ⟨x, hkerP ⟨x, hxP⟩ (Subtype.ext h1)⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ h2
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, hA₁.normal (hA₀.le ha)⟩
  have hX₀P : X₀ ≤ P := L619.preimg_le φ (Ks 0)
  have hX₁P : X₁ ≤ P := L619.preimg_le φ (Ks 1)
  have hA₀P : A₀ ≤ P := (L619.threePart_le X₀).trans hX₀P
  have hA₁P : A₁ ≤ P := (L619.threePart_le X₁).trans hX₁P
  obtain ⟨x₀, hx₀N, hx₀I, i₀, k₀, hk₀, hk₀'⟩ := hswap
  have hconj_inj : ∀ (g : MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) (A B : Subgroup _),
      conjSubgroup A g = conjSubgroup B g → A = B := fun g A B h =>
    Subgroup.map_injective (MulAut.conj g⁻¹).injective h
  have hsw : conjSubgroup (Ks 0) (L619.act0 hW _ P ⟨x₀, hx₀N⟩) = Ks 1 ∧
      conjSubgroup (Ks 1) (L619.act0 hW _ P ⟨x₀, hx₀N⟩) = Ks 0 := by
    have hnot : conjSubgroup (Ks i₀) (L619.act0 hW _ P ⟨x₀, hx₀N⟩) ≠ Ks i₀ := fun he =>
      hk₀' (mem_conjSubgroup_iff.mp (he.symm ▸ hk₀))
    rcases hcase2 x₀ hx₀N 0 with h0 | h0 <;> rcases hcase2 x₀ hx₀N 1 with h1 | h1
    · exact absurd (hconj_inj _ _ _ (h0.trans h1.symm)) hne
    · exfalso
      fin_cases i₀
      · exact hnot h0
      · exact hnot h1
    · exact ⟨h0, h1⟩
    · exact absurd (hconj_inj _ _ _ (h0.trans h1.symm)) hne
  have hcard_conj : ∀ (g : MulAut ↥(L619.V0 hW (ch6ZS T L V) P)) (A : Subgroup _),
      Nat.card (conjSubgroup A g) = Nat.card A := fun g A =>
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have h6' : ∀ i, Nat.card (Ks i) = 6 := by
    have h01 : Nat.card (Ks 0) = Nat.card (Ks 1) := by rw [← hsw.1, hcard_conj]
    obtain ⟨i, hi⟩ := h6
    intro j
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] at hi ⊢ <;> omega
  have hθ : ∀ i, Nonempty (↥(Ks i) ≃* Equiv.Perm (Fin 3)) := by
    intro i
    rcases hdec.small rfl i with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨e₂⟩ := L619.nonempty_gl2_mulEquiv_perm3'
      exact ⟨e.trans e₂⟩
    · exfalso
      have := Nat.card_congr e.toEquiv
      rw [h6' i, L619.card_GL32] at this
      omega
    · exfalso
      have := Nat.card_congr e.toEquiv
      have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by rw [Nat.card_perm, Nat.card_fin]; rfl
      rw [h6' i, h120] at this
      omega
  let θ : ∀ i, ↥(Ks i) ≃* Equiv.Perm (Fin 3) := fun i => (hθ i).some
  set q : Fin 2 → MulAut ↥(L619.V0 hW (ch6ZS T L V) P) :=
    fun i => (((θ i).symm L619.cyc3 : ↥(Ks i)) : MulAut _) with hqdef
  have hqK : ∀ i, q i ∈ Ks i := fun i => ((θ i).symm L619.cyc3).2
  have hq3 : ∀ i, q i ^ 3 = 1 := fun i => by
    have := (L619.perm3_facts (θ i)).1
    simpa [hqdef] using congrArg Subtype.val this
  have hq1 : ∀ i, q i ≠ 1 := fun i h => (L619.perm3_facts (θ i)).2.1 (Subtype.ext h)
  have h3el : ∀ i, ∀ k ∈ Ks i, (∃ m : ℕ, k ^ 3 ^ m = 1) → k ∈ Subgroup.zpowers (q i) := by
    intro i k hk ⟨m, hm⟩
    have := (L619.perm3_facts (θ i)).2.2.1 ⟨k, hk⟩ ⟨m, Subtype.ext (by simpa using hm)⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp this
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa [hqdef] using congrArg Subtype.val hj⟩
  have hinvq : ∀ i, ∀ t ∈ Ks i, t ^ 2 = 1 → t ≠ 1 → t * q i * t⁻¹ = (q i)⁻¹ := by
    intro i t ht ht2 ht1
    have := (L619.perm3_facts (θ i)).2.2.2 ⟨t, ht⟩ (Subtype.ext (by simpa using ht2))
      (fun h => ht1 (by simpa using congrArg Subtype.val h))
    simpa [hqdef] using congrArg Subtype.val this
  have hq01 : q 0 * q 1 = q 1 * q 0 := hc01 _ (hqK 0) _ (hqK 1)
  have hKdec : ∀ k ∈ K, ∃ a ∈ Ks 0, ∃ b ∈ Ks 1, k = a * b := by
    intro k hk
    have h10 : Ks 1 ≤ Subgroup.normalizer (Ks 0 : Set _) := fun b hb =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        hc01 a ha b hb)
    have hk' : k ∈ ((Ks 0 ⊔ Ks 1 : Subgroup _) : Set _) := by rw [hsup]; exact hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (Ks 0) (Ks 1) h10] at hk'
    obtain ⟨a, ha, b, hb, rfl⟩ := hk'
    exact ⟨a, ha, b, hb, rfl⟩
  set T₃ := Subgroup.closure ({q 0, q 1} : Set (MulAut ↥(L619.V0 hW (ch6ZS T L V) P)))
    with hT₃
  have hqT : ∀ i, q i ∈ T₃ := fun i => by
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have h3T : ∀ k ∈ K, (∃ m : ℕ, k ^ 3 ^ m = 1) → k ∈ T₃ := by
    rintro k hk ⟨m, hm⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hKdec k hk
    have hab : Commute a b := hc01 a ha b hb
    rw [hab.mul_pow] at hm
    have ha3 : a ^ 3 ^ m ∈ Ks 0 ⊓ Ks 1 := by
      refine ⟨(Ks 0).pow_mem ha _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hm]
      exact (Ks 1).inv_mem ((Ks 1).pow_mem hb _)
    rw [hdisj, Subgroup.mem_bot] at ha3
    have hb3 : b ^ 3 ^ m = 1 := by rwa [ha3, one_mul] at hm
    exact T₃.mul_mem (Subgroup.zpowers_le.mpr (hqT 0) (h3el 0 a ha ⟨m, ha3⟩))
      (Subgroup.zpowers_le.mpr (hqT 1) (h3el 1 b hb ⟨m, hb3⟩))
  have hT₃K : T₃ ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hKi 0 (hqK 0)
    · exact hKi 1 (hqK 1)
  have hinjq : ∀ a b c d : ℕ, a < 3 → b < 3 → c < 3 → d < 3 →
      q 0 ^ a * q 1 ^ b = q 0 ^ c * q 1 ^ d → a = c ∧ b = d := by
    intro a b c d ha hb hc hd he
    have hmem : (q 0 ^ c)⁻¹ * q 0 ^ a ∈ Ks 0 ⊓ Ks 1 := by
      refine ⟨(Ks 0).mul_mem ((Ks 0).inv_mem ((Ks 0).pow_mem (hqK 0) _))
        ((Ks 0).pow_mem (hqK 0) _), ?_⟩
      have : (q 0 ^ c)⁻¹ * q 0 ^ a = q 1 ^ d * (q 1 ^ b)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, he]
      rw [this]
      exact (Ks 1).mul_mem ((Ks 1).pow_mem (hqK 1) _) ((Ks 1).inv_mem ((Ks 1).pow_mem (hqK 1) _))
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hb' : q 1 ^ b = q 1 ^ d := by rw [hmem] at he; exact mul_left_cancel he
    have ho : ∀ i, orderOf (q i) = 3 := fun i => orderOf_eq_prime (hq3 i) (hq1 i)
    rw [pow_eq_pow_iff_modEq, ho] at hmem hb'
    exact ⟨Nat.ModEq.eq_of_lt_of_lt hmem.symm ha hc, Nat.ModEq.eq_of_lt_of_lt hb' hb hd⟩
  exact hd.false_of_swap_core hW c Ks hPN hIN hφs hkerP hO2P hPI hIP hKi hc01 hne hact hQ2 hcase2
      hnormX hoddfix hA₀ hA₁ hinf hA₀P hA₁P x₀ hx₀N hx₀I hconj_inj hsw hcard_conj hθ hqK hq3 hq1
      h3el hinvq hq01 hKdec hqT h3T hinjq

end Dat619

theorem case619Swap_of (h432 : Stmt4_3_2) : Case619Swap := by
  intro G _ _ T M L V H n y z T' D' h hd hW Ks hdec hND hswap h6
  exact hd.false_of_swap h h432 hW hdec hND hswap h6

end CFSG.Quasithin.H13
