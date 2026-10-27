module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3A2K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3A7K

open Equiv CFSG.Permutation.FinPack CFSG.RankThree.PartTwo.Sec21.FF84.S3
  CFSG.RankThree.PartTwo.Sec21.FF84.S3A2K

@[expose] def r₁ : P8 := List.formPerm [3, 4, 5]

@[expose] def r₂ : P8 := List.formPerm [1, 2, 3, 4, 5]

@[expose] def r₃ : P8 := List.formPerm [1, 3, 5, 2, 4]

@[expose] noncomputable def p8K (c : ℕ) : ℕ :=
  (fun c4 => mulK 8 c4 c4) ((fun c2 => mulK 8 c2 c2) ((fun c1 => mulK 8 c1 c1) c))

@[expose] noncomputable def witK (r ri x : ℕ) : Bool :=
  notB (Nat.beq (p8K (mulK 8 x (mulK 8 (mulK 8 r x) ri))) 1985229328)

@[expose] noncomputable def a7C (x : ℕ) : Bool :=
  orB (notB (Nat.beq (p8K x) 1985229328)) (orB (Nat.beq x 1985229328) (orB (Nat.beq x 1733571088)
    (orB (witK 1983201808 1984123408 x) (orB (witK 1981104928 1984110928 x)
      (witK 1981895728 1982993728 x)))))

@[expose] noncomputable def a7Q (x : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true (a7C x)
    (allLtK (fun i => Nat.beq (rd x (rd 1733571088 i)) (rd 1733571088 (rd x i))) 8)

theorem check : walkK 8 a7Q 8 0 0 0 = true := by decide +kernel

theorem enc_τ₀ : enc τ₀ = 1733571088 := by decide +kernel

theorem enc_r₁ : enc r₁ = 1983201808 := by decide +kernel

theorem enc_r₁_inv : enc r₁⁻¹ = 1984123408 := by decide +kernel

theorem enc_r₂ : enc r₂ = 1981104928 := by decide +kernel

theorem enc_r₂_inv : enc r₂⁻¹ = 1984110928 := by decide +kernel

theorem enc_r₃ : enc r₃ = 1981895728 := by decide +kernel

theorem enc_r₃_inv : enc r₃⁻¹ = 1982993728 := by decide +kernel

theorem p8K_enc (σ : P8) : p8K (enc σ) = enc (σ ^ 8) := by
  have e : σ ^ 8 = σ * σ * (σ * σ) * (σ * σ * (σ * σ)) := by
    change σ ^ (2 * 2 * 2) = _
    rw [pow_mul, pow_mul, sq, sq, sq]
  rw [e]
  simp only [enc_mul hn8]
  rfl

theorem orF {b y : Bool} (h : orB b y = true) (hb : b = false) : y = true := by
  subst hb
  exact h

theorem witK_enc {r : P8} {cr cri : ℕ} (hr : enc r = cr) (hri : enc r⁻¹ = cri) (x : P8)
    (h : witK cr cri (enc x) = true) : (x * (r * x * r⁻¹)) ^ 8 ≠ 1 := by
  unfold witK at h
  rw [← hr, ← hri, ← enc_mul hn8, ← enc_mul hn8, ← enc_mul hn8, p8K_enc] at h
  exact not_ne_one h

theorem core (x : P8) (hx : x * τ₀ = τ₀ * x) (h8 : x ^ 8 = 1) (h1 : x ≠ 1) (hτ : x ≠ τ₀) :
    (x * (r₁ * x * r₁⁻¹)) ^ 8 ≠ 1 ∨ (x * (r₂ * x * r₂⁻¹)) ^ 8 ≠ 1 ∨
      (x * (r₃ * x * r₃⁻¹)) ^ 8 ≠ 1 := by
  have hz := walkK_sound check x
  have hm : ∀ j : Fin 8, rd 1733571088 j = (τ₀ j : ℕ) := fun j => by
    rw [← enc_τ₀]
    exact rd_enc hn8 τ₀ j
  have e : allLtK (fun i => Nat.beq (rd (enc x) (rd 1733571088 i))
      (rd 1733571088 (rd (enc x) i))) 8 = true := by
    refine allLtK_iff.2 fun i hi => ?_
    have h1 : rd (enc x) i = (x ⟨i, hi⟩ : ℕ) := rd_enc hn8 x ⟨i, hi⟩
    have h2 : rd 1733571088 i = (τ₀ ⟨i, hi⟩ : ℕ) := hm ⟨i, hi⟩
    rw [Nat.beq_eq, h1, h2, rd_enc hn8 x, hm]
    exact congrArg Fin.val (Perm.ext_iff.1 hx ⟨i, hi⟩)
  unfold a7Q at hz
  rw [e] at hz
  have hz' : a7C (enc x) = true := hz
  unfold a7C at hz'
  have e8 : notB (Nat.beq (p8K (enc x)) 1985229328) = false := by
    rw [p8K_enc, h8, enc_one8, Nat.beq_refl]
    rfl
  have e1 : Nat.beq (enc x) 1985229328 = false := ne_one_code h1
  have eτ : Nat.beq (enc x) 1733571088 = false := by
    rw [← enc_τ₀]
    exact beq_enc_false hn8 hτ
  have hw := orF (orF (orF hz' e8) e1) eτ
  rw [orB_eq, orB_eq] at hw
  rcases hw with h | h | h
  · exact Or.inl (witK_enc enc_r₁ enc_r₁_inv x h)
  · exact Or.inr (Or.inl (witK_enc enc_r₂ enc_r₂_inv x h))
  · exact Or.inr (Or.inr (witK_enc enc_r₃ enc_r₃_inv x h))

end CFSG.RankThree.PartTwo.Sec21.FF84.S3A7K
