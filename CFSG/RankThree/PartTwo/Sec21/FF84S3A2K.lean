module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3A2K

open Equiv CFSG.Permutation.FinPack CFSG.RankThree.PartTwo.Sec21.FF84.S3

@[expose] def andB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false y x

@[expose] def orB (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) y true x

@[expose] def notB (x : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false x

theorem andB_eq (x y : Bool) : andB x y = true ↔ x = true ∧ y = true := by
  cases x <;> cases y <;> decide

theorem orB_eq (x y : Bool) : orB x y = true ↔ x = true ∨ y = true := by
  cases x <;> cases y <;> decide

@[expose] def S9 : List ℕ :=
  [1985229328, 1983201313, 1984123138, 1984122913, 1983201538, 1985229058, 1985228833, 1984123408,
    1983201808]

@[expose] def L18 : List P8 :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 2).map fun k => m₁ ^ i * m₂ ^ j * τ₀ ^ k

@[expose] def Z18 : List ℕ :=
  [1985229328, 1733571088, 1984122913, 1732464673, 1983201538, 1731543298, 1983201313, 1731543073,
    1985229058, 1733570818, 1984123408, 1732465168, 1984123138, 1732464898, 1983201808, 1731543568,
    1985228833, 1733570593]

@[expose] noncomputable def f1 (x : ℕ) : Bool :=
  orB (Nat.beq (mulK 8 x 1984122913) (mulK 8 1984122913 x))
    (Nat.beq (mulK 8 x 1984122913) (mulK 8 1983201538 x))

@[expose] noncomputable def f2 (x : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (memK x S9)
    (Nat.beq (mulK 8 x (mulK 8 x x)) 1985229328)

@[expose] noncomputable def g3 (y : ℕ) : Bool :=
  andB (Nat.beq (mulK 8 y (mulK 8 y y)) 1985229328) (notB (Nat.beq y 1985229328))

@[expose] noncomputable def f3 (x : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (g3 (mulK 8 x (mulK 8 (mulK 8 1984122913 x) 1983201538)))
    (andB (Nat.beq (mulK 8 x x) 1985229328)
      (andB (notB (Nat.beq x 1985229328)) (evenK 8 x)))

@[expose] noncomputable def f4 (x : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (memK x Z18)
    (Nat.beq (mulK 8 x 1984122913) (mulK 8 1984122913 x))

@[expose] noncomputable def cenQ (x : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (andB (f1 x) (andB (f2 x) (andB (f3 x) (f4 x))))
    (allLtK (fun i => Nat.beq (rd x (rd 1983201313 i)) (rd 1983201313 (rd x i))) 8)

theorem enc_m₁ : enc m₁ = 1983201313 := by decide +kernel

theorem enc_m₂ : enc m₂ = 1984122913 := by decide +kernel

theorem enc_m₂_inv : enc m₂⁻¹ = 1983201538 := by decide +kernel

theorem enc_one8 : enc (1 : P8) = 1985229328 := by decide +kernel

theorem pin_S9 : ([1, m₁, m₁ ^ 2, m₂, m₂⁻¹, m₁ * m₂, (m₁ * m₂)⁻¹, m₁ * m₂ ^ 2, (m₁ * m₂ ^ 2)⁻¹].map
    enc == S9) = true := by
  decide +kernel

theorem pin_Z18 : (L18.map enc == Z18) = true := by decide +kernel

theorem check : walkK 8 cenQ 8 0 0 0 = true := by decide +kernel

theorem hn8 : (8 : ℕ) ≤ 16 := by norm_num

theorem mul_code (σ τ ρ : P8) :
    Nat.beq (mulK 8 (enc σ) (enc τ)) (mulK 8 (enc ρ) (enc σ)) = true ↔ σ * τ = ρ * σ := by
  rw [← enc_mul hn8, ← enc_mul hn8, beq_enc_iff hn8]

theorem cube_code (σ : P8) :
    Nat.beq (mulK 8 (enc σ) (mulK 8 (enc σ) (enc σ))) 1985229328 = true ↔ σ ^ 3 = 1 := by
  rw [← enc_mul hn8, ← enc_mul hn8, ← pow_three, ← enc_one8, beq_enc_iff hn8]

theorem ne_one_code {σ : P8} (h : σ ≠ 1) : Nat.beq (enc σ) 1985229328 = false := by
  rw [← enc_one8]
  exact beq_enc_false hn8 h

theorem not_ne_one {σ : P8} (h : notB (Nat.beq (enc σ) 1985229328) = true) : σ ≠ 1 := by
  intro hs
  rw [hs, enc_one8, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem facts (σ : P8) (hσ : σ * m₁ = m₁ * σ) :
    (σ * m₂ * σ⁻¹ = m₂ ∨ σ * m₂ * σ⁻¹ = m₂⁻¹) ∧
    (σ ^ 3 = 1 → σ ≠ 1 → σ ≠ m₁ → σ ≠ m₁ ^ 2 →
      (σ = m₂ ∨ σ = m₂⁻¹ ∨ σ = m₁ * m₂ ∨ σ = (m₁ * m₂)⁻¹ ∨ σ = m₁ * m₂ ^ 2 ∨
        σ = (m₁ * m₂ ^ 2)⁻¹)) ∧
    (σ * σ = 1 → σ ≠ 1 → Equiv.Perm.sign σ = 1 →
      (σ * (m₂ * σ * m₂⁻¹)) ^ 3 = 1 ∧ σ * (m₂ * σ * m₂⁻¹) ≠ 1) ∧
    (σ * m₂ = m₂ * σ → ∃ i : ℕ, i < 3 ∧ ∃ j : ℕ, j < 3 ∧ ∃ k : ℕ, k < 2 ∧
      σ = m₁ ^ i * m₂ ^ j * τ₀ ^ k) := by
  have hz := walkK_sound check σ
  have hm : ∀ j : Fin 8, rd 1983201313 j = (m₁ j : ℕ) := fun j => by
    rw [← enc_m₁]
    exact rd_enc hn8 m₁ j
  have e : allLtK (fun i => Nat.beq (rd (enc σ) (rd 1983201313 i))
      (rd 1983201313 (rd (enc σ) i))) 8 = true := by
    refine allLtK_iff.2 fun i hi => ?_
    have h1 : rd (enc σ) i = (σ ⟨i, hi⟩ : ℕ) := rd_enc hn8 σ ⟨i, hi⟩
    have h2 : rd 1983201313 i = (m₁ ⟨i, hi⟩ : ℕ) := hm ⟨i, hi⟩
    rw [Nat.beq_eq, h1, h2, rd_enc hn8 σ, hm]
    exact congrArg Fin.val (Perm.ext_iff.1 hσ ⟨i, hi⟩)
  unfold cenQ at hz
  rw [e] at hz
  have hz' : andB (f1 (enc σ)) (andB (f2 (enc σ)) (andB (f3 (enc σ)) (f4 (enc σ)))) = true := hz
  rw [andB_eq, andB_eq, andB_eq] at hz'
  obtain ⟨h1, h2, h3, h4⟩ := hz'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold f1 at h1
    rw [orB_eq, ← enc_m₂, ← enc_m₂_inv, mul_code, mul_code] at h1
    exact h1.imp mul_inv_eq_iff_eq_mul.2 mul_inv_eq_iff_eq_mul.2
  · intro hc h1' hm1 hm1sq
    unfold f2 at h2
    rw [(cube_code σ).2 hc] at h2
    have hm2 : memK (enc σ) S9 = true := h2
    rw [memK_iff, ← beq_iff_eq.1 pin_S9, ← mem_iff_enc hn8] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with h | h | h | h | h | h | h | h | h
    · exact absurd h h1'
    · exact absurd h hm1
    · exact absurd h hm1sq
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · intro hsq h1' hsg
    have ea : Nat.beq (mulK 8 (enc σ) (enc σ)) 1985229328 = true := by
      rw [← enc_mul hn8, hsq, enc_one8, Nat.beq_refl]
    have ec : evenK 8 (enc σ) = true := (sign_eq_one_iff_evenK hn8 σ).1 hsg
    unfold f3 at h3
    rw [ea, ne_one_code h1', ec] at h3
    have h3' : g3 (mulK 8 (enc σ) (mulK 8 (mulK 8 1984122913 (enc σ)) 1983201538)) = true := h3
    rw [← enc_m₂, ← enc_m₂_inv, ← enc_mul hn8, ← enc_mul hn8, ← enc_mul hn8] at h3'
    unfold g3 at h3'
    rw [andB_eq, cube_code] at h3'
    exact ⟨h3'.1, not_ne_one h3'.2⟩
  · intro hc2
    have e4 : Nat.beq (mulK 8 (enc σ) 1984122913) (mulK 8 1984122913 (enc σ)) = true := by
      rw [← enc_m₂]
      exact (mul_code σ m₂ m₂).2 hc2
    unfold f4 at h4
    rw [e4] at h4
    have hm4 : memK (enc σ) Z18 = true := h4
    rw [memK_iff, ← beq_iff_eq.1 pin_Z18, ← mem_iff_enc hn8] at hm4
    simp only [L18, List.mem_flatMap, List.mem_range, List.mem_map] at hm4
    obtain ⟨i, hi, j, hj, k, hk, hk'⟩ := hm4
    exact ⟨i, hi, j, hj, k, hk, hk'.symm⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3A2K
