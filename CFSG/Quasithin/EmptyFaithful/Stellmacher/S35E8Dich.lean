module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Th
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Fin

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

omit [Finite G] in
theorem th_comm_swap (c : Ch.Chart δ) {Y Vb : Subgroup G} (hYs : Y ≤ stab δ) (hVs : Vb ≤ stab δ)
    (hcomm : ∀ y ∈ Y, ∀ v ∈ Vb, y * v = v * y) {v₀ : G} (hv₀ : v₀ ∈ Vb)
    (ht : th c v₀ = swap 0 1) {y : G} (hy : y ∈ Y) :
    th c y * swap 0 1 = swap 0 1 * th c y := by
  rw [← ht, ← th_mul c (hYs hy) (hVs hv₀), ← th_mul c (hVs hv₀) (hYs hy), hcomm y hy v₀ hv₀]

omit [Finite G] in
theorem dichotomy (c : Ch.Chart δ) {Y Vb : Subgroup G} (hVY : Vb ≤ Y) (hYs : Y ≤ stab δ)
    (hcomm : ∀ y ∈ Y, ∀ v ∈ Vb, y * v = v * y) (h8 : ∀ y ∈ Y, th c y ^ 8 = 1)
    {v₀ : G} (hv₀ : v₀ ∈ Vb) (ht : th c v₀ = swap 0 1) :
    (∀ y ∈ Y, ∃ v ∈ Vb, th c y = th c v) ∨
    ∃ s, DS (swap 0 1) s ∧ (∀ v ∈ Vb, th c v = 1 ∨ th c v = swap 0 1) ∧
      (∀ y ∈ Y, th c y = 1 ∨ th c y = swap 0 1 ∨ th c y = s ∨ th c y = swap 0 1 * s) := by
  have hVs : Vb ≤ stab δ := hVY.trans hYs
  have hc := fun y hy => th_comm_swap c hYs hVs hcomm hv₀ ht (y := y) hy
  by_cases hall : ∀ y ∈ Y, ∃ v ∈ Vb, th c y = th c v
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨y₀, hy₀, hne⟩ := hall
  have h1 : th c y₀ ≠ 1 := fun h => hne 1 Vb.one_mem (by rw [h, th_one])
  have h2 : th c y₀ ≠ swap 0 1 := fun h => hne v₀ hv₀ (by rw [h, ht])
  rcases E8.F1 _ (hc y₀ hy₀) (h8 y₀ hy₀) with h | h | ⟨s, hs, hs'⟩
  · exact absurd h h1
  · exact absurd h h2
  have ht1 : swap 0 1 * swap 0 1 = (1 : Perm (Fin 5)) := swap_mul_self _ _
  have hu : ∃ u, (u = 1 ∨ u = swap 0 1) ∧ th c y₀ = u * s := by
    rcases hs' with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨u, hu1, hu2⟩ := hu
  have ha : ∀ y ∈ Y, th c y = 1 ∨ th c y = swap 0 1 ∨ th c y = s ∨ th c y = swap 0 1 * s := by
    intro y hy
    rcases E8.F1 _ (hc y hy) (h8 y hy) with h | h | ⟨s', hs2, hs3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    by_cases hss : s' = s
    · subst hss
      rcases hs3 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exfalso
      have hy' : y₀⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hy₀) hy
      have h8' := h8 _ hy'
      rw [th_mul c (hYs (Y.inv_mem hy₀)) (hYs hy), th_inv c (hYs hy₀)] at h8'
      have hu' : ∃ u', (u' = 1 ∨ u' = swap 0 1) ∧ th c y = u' * s' := by
        rcases hs3 with h | h
        · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
        · exact ⟨_, Or.inr rfl, h⟩
      obtain ⟨u', hu1', hu2'⟩ := hu'
      rw [hu2, hu2'] at h8'
      exact E8.F2 s s' hs hs2 (Ne.symm hss) u u' hu1 hu1' h8'
  refine ⟨s, hs, fun v hv => ?_, ha⟩
  rcases ha v (hVY hv) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rcases hs' with h' | h'
    · exact hne v hv (by rw [h', h])
    · refine hne (v₀ * v) (Vb.mul_mem hv₀ hv) ?_
      rw [th_mul c (hVs hv₀) (hVs hv), ht, h, h']
  · exfalso
    rcases hs' with h' | h'
    · refine hne (v₀ * v) (Vb.mul_mem hv₀ hv) ?_
      rw [th_mul c (hVs hv₀) (hVs hv), ht, h, h', ← mul_assoc, ht1, one_mul]
    · exact hne v hv (by rw [h', h])

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
