module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin.Background.Harris.R1

variable {G : Type*} [Group G] {V : Subgroup G}

theorem inv_eq_of_sq (h2 : ∀ v ∈ V, v * v = 1) {v : G} (hv : v ∈ V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (h2 v hv)

theorem commute_of_sq (h2 : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ V) (hb : b ∈ V) :
    a * b = b * a :=
  calc a * b = (a * b)⁻¹ := (inv_eq_of_sq h2 (V.mul_mem ha hb)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_sq h2 hb, inv_eq_of_sq h2 ha]

theorem klein_mem_cases [Finite V] (h4 : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1) {a b : G}
    (ha : a ∈ V) (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) {c : G} (hc : c ∈ V) :
    c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have habV : a * b ∈ V := V.mul_mem ha hb
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_sq h2 hb])
  have haba : a * b ≠ a := fun h => hb1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this)
  have habb : a * b ≠ b := fun h => ha1 (by
    have := congrArg (· * b⁻¹) h
    simpa using this)
  set s : Finset V := {⟨1, V.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩, ⟨a * b, habV⟩} with hs
  have hcard : s.card = 4 := by
    rw [hs]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => habb (congrArg Subtype.val h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hab (congrArg Subtype.val h), fun h => haba (congrArg Subtype.val h).symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm, fun h => hb1 (congrArg Subtype.val h).symm,
        fun h => hab1 (congrArg Subtype.val h).symm⟩
  have huniv : s = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, ← Nat.card_eq_fintype_card, h4]
  have hmem : (⟨c, hc⟩ : V) ∈ s := by rw [huniv]; exact Finset.mem_univ _
  rw [hs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

variable [Finite V] (h4 : Nat.card V = 4) (h2 : ∀ v ∈ V, v * v = 1)
include h4 h2

theorem conj_ne_of_cube {g : G} (hg : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (h3 : g * g * g = 1)
    {w : G} (hw : w ∈ V) (hgw : g * w * g⁻¹ ≠ w) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1) :
    g * u * g⁻¹ ≠ u := by
  intro hgu
  have hw1 : w ≠ 1 := fun h => hgw (by rw [h]; group)
  have hwu : u ≠ w := fun h => hgw (h ▸ hgu)
  have hgw1 : g * w * g⁻¹ ≠ 1 := fun h => hw1 (by
    have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [this, h]; group)
  have hgwu : g * w * g⁻¹ ≠ u := fun h => hwu (by
    have h' : g * w * g⁻¹ = g * u * g⁻¹ := h.trans hgu.symm
    have := congrArg (fun x => g⁻¹ * x * g) h'
    simpa [mul_assoc] using this.symm)
  rcases klein_mem_cases h4 h2 hu hw hu1 hw1 hwu (hg w hw) with h | h | h | h
  · exact hgw1 h
  · exact hgwu h
  · exact hgw h
  ·
    have hg2 : g * (g * w * g⁻¹) * g⁻¹ = w := by
      rw [h, show g * (u * w) * g⁻¹ = (g * u * g⁻¹) * (g * w * g⁻¹) by group, hgu, h,
        ← mul_assoc, h2 u hu, one_mul]
    have hg3 : g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = w := by
      rw [show g * (g * (g * w * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * w * (g * g * g)⁻¹ by group, h3]
      group
    rw [hg2] at hg3
    exact hgw hg3

theorem cube_mul_eq_one {g : G} (hg : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (h3 : g * g * g = 1)
    {w : G} (hw : w ∈ V) (hgw : g * w * g⁻¹ ≠ w) {u : G} (hu : u ∈ V) :
    g * u * (g * u) * (g * u) = 1 := by
  by_cases hu1 : u = 1
  · rw [hu1]; simpa using h3
  set u' := g * u * g⁻¹ with hu'
  set u'' := g * u' * g⁻¹ with hu''
  have hu'V : u' ∈ V := hg u hu
  have hu''V : u'' ∈ V := hg u' hu'V
  have hu'1 : u' ≠ 1 := fun h => hu1 (by
    have : u = g⁻¹ * u' * g := by rw [hu']; group
    rw [this, h]; group)
  have hne1 : u' ≠ u := conj_ne_of_cube h4 h2 hg h3 hw hgw hu hu1
  have hne2 : u'' ≠ u' := conj_ne_of_cube h4 h2 hg h3 hw hgw hu'V hu'1
  have hne3 : u'' ≠ u := fun h => hne1 (by
    have h' : g * u'' * g⁻¹ = g * u * g⁻¹ := by rw [h]
    rw [hu'', show g * (g * u' * g⁻¹) * g⁻¹ = g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ by rw [hu'],
      show g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * u * (g * g * g)⁻¹ by group, h3]
      at h'
    simpa using h'.symm)
  have hu''1 : u'' ≠ 1 := fun h => hu'1 (by
    have : u' = g⁻¹ * u'' * g := by rw [hu'']; group
    rw [this, h]; group)
  have hprod : u'' = u * u' := by
    rcases klein_mem_cases h4 h2 hu hu'V hu1 hu'1 hne1.symm hu''V with h | h | h | h
    · exact absurd h hu''1
    · exact absurd h hne3
    · exact absurd h hne2
    · exact h
  calc g * u * (g * u) * (g * u) = u' * u'' * (g * g * g) * u := by rw [hu'', hu']; group
    _ = u' * (u * u') * u := by rw [h3, mul_one, hprod]
    _ = (u' * u) * (u' * u) := by group
    _ = 1 := h2 _ (V.mul_mem hu'V hu)

theorem conj_eq_of_pow_seven {t : G} (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) (h7 : t ^ 7 = 1) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (htz : t * z * t⁻¹ = z) {v : G} (hv : v ∈ V) :
    t * v * t⁻¹ = v := by
  by_cases hv1 : v = 1
  · rw [hv1]; group
  by_cases hvz : v = z
  · rw [hvz, htz]
  have htv1 : t * v * t⁻¹ ≠ 1 := fun h => hv1 (by
    have : v = t⁻¹ * (t * v * t⁻¹) * t := by group
    rw [this, h]; group)
  have htvz : t * v * t⁻¹ ≠ z := fun h => hvz (by
    have h' : t * v * t⁻¹ = t * z * t⁻¹ := h.trans htz.symm
    have := congrArg (fun x => t⁻¹ * x * t) h'
    simpa [mul_assoc] using this)
  have hcase : t * v * t⁻¹ = v ∨ t * v * t⁻¹ = z * v := by
    rcases klein_mem_cases h4 h2 hz hv hz1 hv1 (Ne.symm hvz) (ht v hv) with h | h | h | h
    · exact absurd h htv1
    · exact absurd h htvz
    · exact Or.inl h
    · exact Or.inr h
  rcases hcase with h | h
  · exact h
  · exfalso
    have h2t : t * (t * v * t⁻¹) * t⁻¹ = v := by
      rw [h, show t * (z * v) * t⁻¹ = (t * z * t⁻¹) * (t * v * t⁻¹) by group, htz, h,
        ← mul_assoc, h2 z hz, one_mul]
    have hpow : ∀ n : ℕ, t ^ (2 * n) * v * (t ^ (2 * n))⁻¹ = v := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two]
        calc t ^ (2 * k) * (t * t) * v * (t ^ (2 * k) * (t * t))⁻¹ =
            t ^ (2 * k) * (t * (t * v * t⁻¹) * t⁻¹) * (t ^ (2 * k))⁻¹ := by group
          _ = v := by rw [h2t, ih]
    have h6 := hpow 3
    have h7' : t * v * t⁻¹ = v := by
      calc t * v * t⁻¹ = t * (t ^ (2 * 3) * v * (t ^ (2 * 3))⁻¹) * t⁻¹ := by rw [h6]
        _ = t ^ 7 * v * (t ^ 7)⁻¹ := by group
        _ = v := by rw [h7]; group
    rw [h7'] at h
    have : z = 1 := by
      have := congrArg (· * v⁻¹) h
      simpa using this.symm
    exact hz1 this

theorem exists_mul_conj_eq {h : G} (hh : ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    {w : G} (hw : w ∈ V) (hhw : h * w * h⁻¹ ≠ w)
    {c : G} (hc : c ∈ V) (hhc : h * c * h⁻¹ = c) : ∃ u ∈ V, c = u * (h * u * h⁻¹) := by
  by_cases hc1 : c = 1
  · exact ⟨1, V.one_mem, by rw [hc1]; group⟩
  refine ⟨w, hw, ?_⟩
  have hw1 : w ≠ 1 := fun e => hhw (by rw [e]; group)
  have hwc : c ≠ w := fun e => hhw (e ▸ hhc)
  have hhw1 : h * w * h⁻¹ ≠ 1 := fun e => hw1 (by
    have : w = h⁻¹ * (h * w * h⁻¹) * h := by group
    rw [this, e]; group)
  have hhwc : h * w * h⁻¹ ≠ c := fun e => hwc (by
    have e' : h * w * h⁻¹ = h * c * h⁻¹ := e.trans hhc.symm
    have := congrArg (fun x => h⁻¹ * x * h) e'
    simpa [mul_assoc] using this.symm)
  have hcw : h * w * h⁻¹ = c * w := by
    rcases klein_mem_cases h4 h2 hc hw hc1 hw1 hwc (hh w hw) with e | e | e | e
    · exact absurd e hhw1
    · exact absurd e hhwc
    · exact absurd e hhw
    · exact e
  rw [hcw, commute_of_sq h2 hc hw, ← mul_assoc, h2 w hw, one_mul]

end CFSG.Quasithin.Background.Harris.R1
