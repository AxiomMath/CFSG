module

public import CFSG.Quasithin.EmptyFaithful.ModEAbs2
public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin.ModE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6

theorem comm_of_sq {X : Type*} [Group X] (B : Subgroup X) (hsq : ∀ x ∈ B, x * x = 1) :
    ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  intro x hx y hy
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
  have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hsq (x * y) (B.mul_mem hx hy))
  rw [mul_inv_rev, h1, h2] at h3
  exact h3.symm

theorem fac2 (k b : ℕ) (hb : ¬ 2 ∣ b) (hb0 : b ≠ 0) : (2 ^ k * b).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) hb0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hb]
  simp

theorem card_inf_triple {D : Type*} [Group D] [Finite D] {H₁ H₂ : Subgroup D}
    (h : IsGoldschmidtTriple H₁ H₂) : Nat.card ↥(H₁ ⊓ H₂) = 2 ^ (Nat.card D).factorization 2 := by
  obtain ⟨P, hP⟩ := h.sylow
  rw [← hP, Sylow.card_eq_multiplicity]

theorem tb_small {D : Type*} [Group D] [Finite D] {T : Subgroup D} {X : Type*} [Group X]
    (e : ↥T ≃* X) (hX : Nat.card X ≤ 8) :
    ∀ B : Subgroup D, B ≤ T → IsElemAbelian 2 B → Nat.card B ≤ 8 :=
  fun _ hBT _ => (Subgroup.card_le_of_le hBT).trans ((le_of_eq (Nat.card_congr e.toEquiv)).trans hX)

theorem case_bound {D : Type} [Group D] [Finite D] {H₁ H₂ K A : Subgroup D}
    (hGT : IsGoldschmidtTriple H₁ H₂) (hcase : IsF618CaseOrientedCat H₁ H₂) (hK : K = H₁ ∨ K = H₂)
    (hAK : A ≤ K) (hAel : IsElemAbelian 2 A) (hAn : K ≤ Subgroup.normalizer (A : Set D))
    (h13 : IsAutM12 D → False) : Nat.card A ≤ 8 := by
  have hT := hGT.sylow
  have hcard := card_inf_triple hGT
  rcases hcase with c | c | c | c | c | c | c | c | c | c | c | c | c
  ·
    obtain ⟨⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    have hD : Nat.card D = 36 ∨ Nat.card D = 108 := by
      rcases c with ⟨⟨e⟩⟩ | ⟨φ, hφ, hN⟩
      · left
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
        decide
      · right
        have h1 := Subgroup.card_ker_mul_card_of_surjective hφ
        have h2 : Nat.card ↥φ.ker = 3 ^ 3 := hN.2.1
        have h3 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
          rw [Nat.card_eq_fintype_card]
          decide
        rw [h2, h3] at h1
        omega
    have hT4 : Nat.card ↥(H₁ ⊓ H₂) = 4 := by
      rw [hcard]
      rcases hD with h | h
      · rw [h, show (36 : ℕ) = 2 ^ 2 * 9 by norm_num, fac2 2 9 (by norm_num) (by norm_num)]
        norm_num
      · rw [h, show (108 : ℕ) = 2 ^ 2 * 27 by norm_num, fac2 2 27 (by norm_num) (by norm_num)]
        norm_num
    refine card_le_of_TB hT (fun B hBT _ => ?_) hAel
    have := Subgroup.card_le_of_le hBT
    omega
  ·
    obtain ⟨p, K', Z, -, -, -, -, -, -, -, ⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    refine card_le_of_TB hT (tb_small e ?_) hAel
    rw [Nat.card_eq_fintype_card]
    decide
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    exact card_le_of_TB hT (tb_of_iso e fun B' hsq => z2d8_bound B' (comm_of_sq B' hsq)) hAel
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    exact card_le_of_TB hT (tb_of_iso e fun B' hsq => z2d8_bound B' (comm_of_sq B' hsq)) hAel
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := c
    exact card_le_of_TB hT (tb_of_iso e fun B' hsq => wreath_bound B' hsq) hAel
  ·
    obtain ⟨-, -, hH1, hH2⟩ := c
    rcases hK with rfl | rfl
    · obtain ⟨φ, hφ, hN⟩ := hH1
      exact ori2 hAK hAel hAn φ hφ hN
    · obtain ⟨φ, hφ, ⟨e⟩⟩ := hH2
      exact ori1 hAK hAel hAn φ hφ e
  ·
    obtain ⟨-, -, hH1, hH2⟩ := c
    rcases hK with rfl | rfl
    · obtain ⟨φ, hφ, hN⟩ := hH1
      exact ori2 hAK hAel hAn φ hφ hN
    · obtain ⟨φ, hφ, ⟨e⟩⟩ := hH2
      exact ori1 hAK hAel hAn φ hφ e
  ·
    exact (h13 c.1).elim

end CFSG.Quasithin.ModE
