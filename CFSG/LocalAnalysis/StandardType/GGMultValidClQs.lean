module

public import CFSG.LocalAnalysis.StandardType.GGMultTableCl
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[simp] private theorem ggMultOrbit_qs_mk {lab : LargeEvenLabel} {q : Bool} :
    (GGKacOrbit.mk lab q).qs = q := rfl

private theorem ggMultOrd_one_eq_zero {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ggMultOrd p 1 = 0 := by
  unfold ggMultOrd
  have h1 : ¬ p ∣ 2 ^ 1 - 1 := by
    rw [show 2 ^ 1 - 1 = (1 : ℕ) by norm_num]
    exact hp.not_dvd_one
  have h3 : ¬ p ∣ 2 ^ 1 + 1 := by
    rw [show 2 ^ 1 + 1 = (3 : ℕ) by norm_num]
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  rw [if_neg h1, if_neg h3]

private theorem mvq_append {l₁ l₂ : List GGKacOrbit}
    (h₁ : ∀ o ∈ l₁, o.qs = true) (h₂ : ∀ o ∈ l₂, o.qs = true) :
    ∀ o ∈ l₁ ++ l₂, o.qs = true := by
  intro o ho
  rw [List.mem_append] at ho
  exact ho.elim (h₁ o) (h₂ o)

private theorem mvq_map {α : Type} {l : List α} {f : α → GGKacOrbit}
    (h : ∀ x, (f x).qs = true) : ∀ o ∈ l.map f, o.qs = true := by
  intro o ho
  rw [List.mem_map] at ho
  obtain ⟨x, -, rfl⟩ := ho
  exact h x

private theorem mvq_singleton {o : GGKacOrbit} (h : o.qs = true) :
    ∀ x ∈ [o], x.qs = true := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact h

private theorem mvq_map_true {α : Type} {l : List α} {f : α → LargeEvenLabel} :
    ∀ o ∈ l.map (fun x => (⟨f x, true⟩ : GGKacOrbit)), o.qs = true :=
  mvq_map (fun _ => rfl)

private theorem ggMultBlockA_qs {r nf d : ℕ} (hnf : nf ≠ 1) :
    (ggMultBlockA r nf d).qs = true := by
  unfold ggMultBlockA
  split_ifs with h1 h2
  · change decide (¬ (r = 1 ∧ nf = 1)) = true
    rw [decide_eq_true_eq]
    rintro ⟨-, h⟩
    exact hnf h
  · change decide (¬ (r = 2 ∧ nf = 1)) = true
    rw [decide_eq_true_eq]
    rintro ⟨-, h⟩
    exact hnf h
  · change decide (¬ (nf = 1)) = true
    rw [decide_eq_true_eq]
    exact hnf

private theorem ggMultA1_qs {r nf : ℕ} (hnf : nf ≠ 1) :
    (⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩ : GGKacOrbit).qs = true := by
  rw [ggMultOrbit_qs_mk, decide_eq_true_eq]
  rintro ⟨-, h⟩
  exact hnf h

private theorem ggMultA1'_qs {nf : ℕ} (hnf : nf ≠ 1) :
    (⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩ : GGKacOrbit).qs = true := by
  rw [ggMultOrbit_qs_mk, decide_eq_true_eq]
  exact hnf

private theorem ggMultV0_qs {m0 nf : ℕ} {plus : Bool} (hnf : nf ≠ 1) :
    ∀ o ∈ ggMultV0 m0 plus nf, o.qs = true := by
  unfold ggMultV0
  by_cases h1 : m0 ≤ 1
  · simp [h1]
  by_cases h2 : m0 = 2
  · by_cases hp : plus <;> simp [h1, h2, hp, decide_eq_true_eq, hnf]
  by_cases h3 : m0 = 3
  · by_cases hp : plus <;> simp [h1, h2, h3, hp]
  · by_cases hp : plus <;> simp [h1, h2, h3, hp]

private theorem ggMultDatumC_qs {p nf d : ℕ} (m : List ℕ) (hnf : nf ≠ 1) :
    ∀ o ∈ (ggMultDatumC p nf d m).orbits, o.qs = true := by
  unfold ggMultDatumC
  dsimp only
  by_cases h0 : m.headD 0 = 1
  · rw [if_pos h0]
    exact mvq_append (mvq_singleton (ggMultA1'_qs hnf)) (mvq_map (fun _ => ggMultBlockA_qs hnf))
  by_cases h1 : m.headD 0 = 2 ∧ nf = 1
  · rw [if_neg h0, if_pos h1]
    exact mvq_append (mvq_singleton rfl) (mvq_map (fun _ => ggMultBlockA_qs hnf))
  by_cases h2 : 2 ≤ m.headD 0
  · rw [if_neg h0, if_neg h1, if_pos h2]
    exact mvq_append (mvq_singleton rfl) (mvq_map (fun _ => ggMultBlockA_qs hnf))
  · rw [if_neg h0, if_neg h1, if_neg h2]
    exact mvq_append (by simp) (mvq_map (fun _ => ggMultBlockA_qs hnf))

private theorem ggMultDatumD_qs {p nf d : ℕ} (tw : Bool) (m : List ℕ) (hnf : nf ≠ 1) :
    ∀ o ∈ (ggMultDatumD p nf d tw m).orbits, o.qs = true := by
  unfold ggMultDatumD
  dsimp only
  exact mvq_append (ggMultV0_qs hnf) (mvq_map (fun _ => ggMultBlockA_qs hnf))

private theorem ggMultDatumA_qs {p nf d : ℕ} (tw : Bool) (m : List ℕ) (hnf : nf ≠ 1) :
    ∀ o ∈ (ggMultDatumA p nf d tw m).orbits, o.qs = true := by
  unfold ggMultDatumA
  dsimp only
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · rw [if_pos htriv]
    exact mvq_map (fun _ => ggMultBlockA_qs hnf)
  · rw [if_neg htriv]
    by_cases h2 : 2 ≤ m.headD 0
    · by_cases htw : tw = false
      · rw [if_pos h2, if_pos htw]
        exact mvq_append (mvq_singleton (ggMultA1_qs hnf)) mvq_map_true
      · rw [if_pos h2, if_neg htw]
        exact mvq_append (mvq_singleton (ggMultBlockA_qs hnf)) mvq_map_true
    · rw [if_neg h2]
      exact mvq_append (by simp) mvq_map_true

theorem ggMultValidCl_qs_true {lab : LargeEvenLabel} {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {D : GGKacDatum} (hD : GGMultValidCl lab p D) : ∀ o ∈ D.orbits, o.qs = true := by
  obtain ⟨T, tw, m, hT, hDmem⟩ := hD
  have hord : ggMultOrd p m ≠ 0 := by
    intro h0
    cases T with
    | C r =>
        simp only [ggMultTableCl] at hDmem
        rw [if_pos h0] at hDmem
        exact List.not_mem_nil hDmem
    | D r =>
        simp only [ggMultTableCl] at hDmem
        rw [if_pos h0] at hDmem
        exact List.not_mem_nil hDmem
    | A r =>
        simp only [ggMultTableCl] at hDmem
        rw [if_pos h0] at hDmem
        exact List.not_mem_nil hDmem
  have hnf : m ≠ 1 := by
    intro h1
    exact hord (by rw [h1]; exact ggMultOrd_one_eq_zero hp hp3)
  cases T with
  | C r =>
      obtain ⟨mm, -, -, hmD⟩ :=
        (mem_ggMultTableCl_C (r := r) (p := p) (n := m) (D := D) hord).mp hDmem
      rw [hmD]
      exact ggMultDatumC_qs mm hnf
  | D r =>
      obtain ⟨mm, -, -, -, hmD⟩ :=
        (mem_ggMultTableCl_D (r := r) (p := p) (n := m) (tw := tw) (D := D) hord).mp hDmem
      rw [hmD]
      exact ggMultDatumD_qs tw mm hnf
  | A r =>
      obtain ⟨mm, -, -, -, hmD⟩ :=
        (mem_ggMultTableCl_A (r := r) (p := p) (n := m) (tw := tw) (D := D) hord).mp hDmem
      rw [hmD]
      exact ggMultDatumA_qs tw mm hnf

end CFSG.StandardType

end
