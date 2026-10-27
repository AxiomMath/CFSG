module

public import CFSG.Timmesfeld.ARS.ExclNSForm

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.Blueprint.Chevalley

@[expose] def g2e (i j : ℕ) : ℤ := if i = j then 2 else if i = 0 then -1 else -3

@[expose] def f4e : ℕ → ℕ → ℤ
  | 0, 0 => 2 | 0, 1 => -1 | 1, 0 => -1 | 1, 1 => 2 | 1, 2 => -1 | 2, 1 => -2 | 2, 2 => 2
  | 2, 3 => -1 | 3, 2 => -1 | 3, 3 => 2 | _, _ => 0

theorem NSLType.elim {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} {i₀ : Fin r} (h : NSLType r C i₀) :
    (3 ≤ r ∧ i₀.val + 1 < r ∧ C = Symplectic.cartanC r) ∨
    (3 ≤ r ∧ i₀.val + 1 < r ∧ C = Spin.cartanB r) ∨
    (r = 2 ∧ i₀.val = 0 ∧ ∀ i j : Fin r, C i j = g2e i.val j.val) ∨
    (r = 4 ∧ i₀.val < 2 ∧ ∀ i j : Fin r, C i j = f4e i.val j.val) := by
  cases h with
  | symplectic hn i₀ hi₀ => exact Or.inl ⟨hn, hi₀, rfl⟩
  | orthogonal hm i₀ hi₀ => exact Or.inr (Or.inl ⟨hm, hi₀, rfl⟩)
  | g2 i₀ hi₀ =>
    refine Or.inr (Or.inr (Or.inl ⟨rfl, hi₀, fun i j => ?_⟩))
    fin_cases i <;> fin_cases j <;> rfl
  | f4 i₀ hi₀ =>
    refine Or.inr (Or.inr (Or.inr ⟨rfl, hi₀, fun i j => ?_⟩))
    fin_cases i <;> fin_cases j <;> rfl

theorem roots_subset_of_closed {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    (hA : TauCeti.IsFiniteType A) (L : Set (Fin r → ℤ)) (h1 : ∀ i, Pi.single i 1 ∈ L)
    (h2 : ∀ v ∈ L, ∀ k, reflection A k v ∈ L) : roots hA ∅ ⊆ L := by
  rintro γ (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
  · induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
    | one => simpa using h1 i
    | mul_simple_left w k ih =>
      rw [weylAction_mul_apply, weylAction_simple]
      exact h2 _ ih k
  · exact absurd hi (Set.notMem_empty i)

@[expose] def reflF {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin r) (v : Fin r → ℤ) :
    Fin r → ℤ :=
  v - (∑ j, A k j * v j) • Pi.single k 1

theorem reflection_eq_reflF {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (k : Fin r)
    (v : Fin r → ℤ) : reflection A k v = reflF A k v :=
  reflection_apply A k v

@[expose] def symF {r : ℕ} (q : Fin r → ℤ) (A : Matrix (Fin r) (Fin r) ℤ) (x y : Fin r → ℤ) : ℤ :=
  x ⬝ᵥ Matrix.mulVec (Matrix.of fun i j => q i * A i j) y

theorem symForm_eq_symF {r : ℕ} (q : Fin r → ℤ) (A : Matrix (Fin r) (Fin r) ℤ)
    (x y : Fin r → ℤ) : symForm q A x y = symF q A x y :=
  symForm_apply q x y

@[expose] def g2M : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -3, 2]

@[expose] def g2Roots : Finset (Fin 2 → ℤ) :=
  {![-2, -3], ![-1, -3], ![-1, -2], ![-1, -1], ![-1, 0], ![0, -1], ![0, 1], ![1, 0], ![1, 1],
    ![1, 2], ![1, 3], ![2, 3]}

theorem g2_matrix {C : Matrix (Fin 2) (Fin 2) ℤ} (hC : ∀ i j : Fin 2, C i j = g2e i.val j.val) :
    C = g2M := by
  ext i j
  rw [hC]
  fin_cases i <;> fin_cases j <;> rfl

theorem g2Roots_closed : ∀ v ∈ g2Roots, ∀ k : Fin 2, reflF g2M k v ∈ g2Roots := by decide

theorem exists_ht_le_g2 {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} (hA : TauCeti.IsFiniteType C)
    (hr : r = 2) (hC : ∀ i j : Fin r, C i j = g2e i.val j.val) {i₀ : Fin r} (hi₀ : i₀.val = 0) :
    ∃ w : (coxeterMatrix hA).Group,
      ∀ ε ∈ roots hA ∅, ht (weylAction hA w (Pi.single i₀ 1)) ≤ ht ε := by
  subst hr
  obtain rfl := g2_matrix hC
  obtain rfl : i₀ = 0 := Fin.ext hi₀
  set s := (coxeterMatrix hA).toCoxeterSystem.simple
  refine ⟨s 0 * s 1 * s 0, fun ε hε => ?_⟩
  have hw : weylAction hA (s 0 * s 1 * s 0) (Pi.single 0 1) = ![-2, -3] := by
    simp only [s, weylAction_mul_apply, weylAction_simple, reflection_eq_reflF]
    decide
  have hL := roots_subset_of_closed hA (g2Roots : Set (Fin 2 → ℤ)) (by decide)
    (fun v hv k => by rw [reflection_eq_reflF]; exact g2Roots_closed v hv k) hε
  rw [hw]
  exact (by decide : ∀ ε ∈ g2Roots, ht (![-2, -3] : Fin 2 → ℤ) ≤ ht ε) ε hL

theorem false_of_g2 {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} (hr : r = 2)
    (hC : ∀ i j : Fin r, C i j = g2e i.val j.val) {i₀ : Fin r} (hi₀ : i₀.val = 0)
    {q : Fin r → ℤ} (hq : ∀ i, q i = if i.val = 0 then 3 else 1) {S : Set (Fin r → ℤ)}
    (hnorm : ∀ β ∈ S, symForm q C β β = symForm q C (Pi.single i₀ 1) (Pi.single i₀ 1))
    (hex : ∃ s, -Pi.single s 1 ∈ S)
    (hinv : ∀ t, -Pi.single t 1 ∉ S → ∀ β ∈ S, reflection C t β ∈ S)
    (hobt : ∀ β ∈ S, ∀ β' ∈ S, 0 ≤ symForm q C β' β) : False := by
  subst hr
  obtain rfl := g2_matrix hC
  obtain rfl : i₀ = 0 := Fin.ext hi₀
  obtain rfl : q = ![3, 1] := by
    funext i
    rw [hq]
    fin_cases i <;> rfl
  simp only [symForm_eq_symF, reflection_eq_reflF] at hnorm hinv hobt
  have h1 : -Pi.single (1 : Fin 2) 1 ∉ S := fun h => by
    have := hnorm _ h
    revert this
    decide
  obtain ⟨s, hs⟩ := hex
  fin_cases s
  · have h0 : (![-1, 0] : Fin 2 → ℤ) ∈ S := by
      convert hs using 1
      decide
    have h2 : (![-1, -3] : Fin 2 → ℤ) ∈ S := by
      convert hinv 1 h1 _ h0 using 1
      decide
    have := hobt _ h0 _ h2
    revert this
    decide
  · exact h1 hs

@[expose] def f4M : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -2, 2, -1; 0, 0, -1, 2]

@[expose] def f4Roots : Finset (Fin 4 → ℤ) :=
  {![-2, -3, -4, -2], ![-1, -3, -4, -2], ![-1, -2, -4, -2], ![-1, -2, -3, -2],
    ![-1, -2, -3, -1], ![-1, -2, -2, -2], ![-1, -2, -2, -1], ![-1, -2, -2, 0],
    ![-1, -1, -2, -2], ![-1, -1, -2, -1], ![-1, -1, -2, 0], ![-1, -1, -1, -1],
    ![-1, -1, -1, 0], ![-1, -1, 0, 0], ![-1, 0, 0, 0], ![0, -1, -2, -2], ![0, -1, -2, -1],
    ![0, -1, -2, 0], ![0, -1, -1, -1], ![0, -1, -1, 0], ![0, -1, 0, 0], ![0, 0, -1, -1],
    ![0, 0, -1, 0], ![0, 0, 0, -1], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0],
    ![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![1, 0, 0, 0],
    ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 0], ![1, 1, 2, 1], ![1, 1, 2, 2],
    ![1, 2, 2, 0], ![1, 2, 2, 1], ![1, 2, 2, 2], ![1, 2, 3, 1], ![1, 2, 3, 2], ![1, 2, 4, 2],
    ![1, 3, 4, 2], ![2, 3, 4, 2]}

theorem f4_matrix {C : Matrix (Fin 4) (Fin 4) ℤ} (hC : ∀ i j : Fin 4, C i j = f4e i.val j.val) :
    C = f4M := by
  ext i j
  rw [hC]
  fin_cases i <;> fin_cases j <;> rfl

theorem f4Roots_closed : ∀ v ∈ f4Roots, ∀ k : Fin 4, reflF f4M k v ∈ f4Roots := by decide

theorem exists_ht_le_f4 {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} (hA : TauCeti.IsFiniteType C)
    (hr : r = 4) (hC : ∀ i j : Fin r, C i j = f4e i.val j.val) {i₀ : Fin r} (hi₀ : i₀.val < 2) :
    ∃ w : (coxeterMatrix hA).Group,
      ∀ ε ∈ roots hA ∅, ht (weylAction hA w (Pi.single i₀ 1)) ≤ ht ε := by
  subst hr
  obtain rfl := f4_matrix hC
  set s := (coxeterMatrix hA).toCoxeterSystem.simple
  have hlow : ∀ ε ∈ roots hA ∅, ht (![-2, -3, -4, -2] : Fin 4 → ℤ) ≤ ht ε := by
    intro ε hε
    have hL := roots_subset_of_closed hA (f4Roots : Set (Fin 4 → ℤ)) (by decide)
      (fun v hv k => by rw [reflection_eq_reflF]; exact f4Roots_closed v hv k) hε
    exact (by decide : ∀ ε ∈ f4Roots, ht (![-2, -3, -4, -2] : Fin 4 → ℤ) ≤ ht ε) ε hL
  have hi : i₀ = 0 ∨ i₀ = 1 := by
    rcases i₀ with ⟨_ | _ | _, _⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp at hi₀
  rcases hi with rfl | rfl
  · refine ⟨s 0 * s 1 * s 2 * s 3 * s 1 * s 2 * s 1 * s 0, fun ε hε => ?_⟩
    have hw : weylAction hA (s 0 * s 1 * s 2 * s 3 * s 1 * s 2 * s 1 * s 0) (Pi.single 0 1) =
        ![-2, -3, -4, -2] := by
      simp only [s, weylAction_mul_apply, weylAction_simple, reflection_eq_reflF]
      decide
    rw [hw]
    exact hlow ε hε
  · refine ⟨s 0 * s 1 * s 2 * s 3 * s 1 * s 2 * s 0 * s 1, fun ε hε => ?_⟩
    have hw : weylAction hA (s 0 * s 1 * s 2 * s 3 * s 1 * s 2 * s 0 * s 1) (Pi.single 1 1) =
        ![-2, -3, -4, -2] := by
      simp only [s, weylAction_mul_apply, weylAction_simple, reflection_eq_reflF]
      decide
    rw [hw]
    exact hlow ε hε

theorem false_of_f4 {r : ℕ} {C : Matrix (Fin r) (Fin r) ℤ} (hr : r = 4)
    (hC : ∀ i j : Fin r, C i j = f4e i.val j.val) {i₀ : Fin r} (hi₀ : i₀.val < 2)
    {q : Fin r → ℤ} (hq : ∀ i, q i = if i.val < 2 then 2 else 1) {S : Set (Fin r → ℤ)}
    (hnorm : ∀ β ∈ S, symForm q C β β = symForm q C (Pi.single i₀ 1) (Pi.single i₀ 1))
    (hex : ∃ s, -Pi.single s 1 ∈ S)
    (hinv : ∀ t, -Pi.single t 1 ∉ S → ∀ β ∈ S, reflection C t β ∈ S)
    (hobt : ∀ β ∈ S, ∀ β' ∈ S, 0 ≤ symForm q C β' β) : False := by
  subst hr
  obtain rfl := f4_matrix hC
  obtain rfl : q = ![2, 2, 1, 1] := by
    funext i
    rw [hq]
    fin_cases i <;> rfl
  have hN : symF ![2, 2, 1, 1] f4M (Pi.single i₀ 1) (Pi.single i₀ 1) = 4 := by
    have hi : i₀ = 0 ∨ i₀ = 1 := by
      rcases i₀ with ⟨_ | _ | _, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp at hi₀
    rcases hi with rfl | rfl <;> decide
  simp only [symForm_eq_symF, reflection_eq_reflF, hN] at hnorm hinv hobt
  have h2 : -Pi.single (2 : Fin 4) 1 ∉ S := fun h => by
    have := hnorm _ h
    revert this
    decide
  have h3 : -Pi.single (3 : Fin 4) 1 ∉ S := fun h => by
    have := hnorm _ h
    revert this
    decide
  have step : ∀ {t : Fin 4}, -Pi.single t 1 ∉ S → ∀ {β : Fin 4 → ℤ}, β ∈ S →
      ∀ {γ : Fin 4 → ℤ}, reflF f4M t β = γ → γ ∈ S :=
    fun {_} ht {_} hβ {_} hγ => hγ ▸ hinv _ ht _ hβ
  obtain ⟨s, hs⟩ := hex
  by_cases h0 : -Pi.single (0 : Fin 4) 1 ∈ S
  · by_cases h1 : -Pi.single (1 : Fin 4) 1 ∈ S
    · have := hobt _ h0 _ h1
      revert this
      decide
    ·
      have e1 := step h1 h0 (γ := ![-1, -1, 0, 0]) (by decide)
      have e2 := step h2 e1 (γ := ![-1, -1, -2, 0]) (by decide)
      have e3 := step h1 e2 (γ := ![-1, -2, -2, 0]) (by decide)
      have e4 := step h3 e3 (γ := ![-1, -2, -2, -2]) (by decide)
      have e5 := step h2 e4 (γ := ![-1, -2, -4, -2]) (by decide)
      have e6 := step h1 e5 (γ := ![-1, -3, -4, -2]) (by decide)
      have := hobt _ h0 _ e6
      revert this
      decide
  · fin_cases s
    · exact h0 hs
    ·
      have e1 := step h0 hs (γ := ![-1, -1, 0, 0]) (by decide)
      have e2 := step h2 e1 (γ := ![-1, -1, -2, 0]) (by decide)
      have e3 := step h3 e2 (γ := ![-1, -1, -2, -2]) (by decide)
      have e4 := step h2 hs (γ := ![0, -1, -2, 0]) (by decide)
      have := hobt _ e3 _ e4
      revert this
      decide
    · exact h2 hs
    · exact h3 hs

end CFSG.Timmesfeld.ARS.ExclNS
