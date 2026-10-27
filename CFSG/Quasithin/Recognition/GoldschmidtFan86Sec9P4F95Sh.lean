module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9F98Coll
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Sq

public section

namespace CFSG.Quasithin.Fan86

namespace Sec9P4F95Alg

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

theorem Ee_mul_za (a₀ a₁ a₂ a₃ b m : ℕ) :
    Ee z za a₀ a₁ a₂ a₃ b * za ^ m = Ee z za a₀ a₁ a₂ a₃ (b + m) := by
  unfold Ee
  rw [mul_assoc _ (za ^ b) (za ^ m), ← pow_add]

theorem z4_pow (hR : P1Rel x w za y z) (n : ℕ) : z 4 ^ n = Ee z za n n n n 0 := by
  induction n with
  | zero => simp [Ee]
  | succ n ih =>
    rw [pow_succ, ih, z_four' hR, Ee_mul hR]

theorem Ee_third (hR : P1Rel x w za y z) (e₁ e₂ e₃ e₄ : ℕ) :
    z 3 * z 0 ^ e₁ * z 1 ^ e₂ * z 2 ^ e₃ * za ^ e₄ = Ee z za e₁ e₂ e₃ 1 e₄ := by
  unfold Ee
  simp only [pow_one, mul_assoc]
  rw [((z_commute hR 2 3).pow_left e₃).left_comm, ((z_commute hR 1 3).pow_left e₂).left_comm,
    ((z_commute hR 0 3).pow_left e₁).left_comm]

theorem odd_of_pow_eq_self (hR : P1Rel x w za y z) (hza : za ≠ 1) {n : ℕ} (h : za ^ n = za) :
    n % 2 = 1 := by
  rw [pow_eq_pow_mod n hR.za2] at h
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · rw [h0, pow_zero] at h
    exact absurd h.symm hza
  · exact h1

theorem even_of_pow_eq_one (hR : P1Rel x w za y z) (hza : za ≠ 1) {n : ℕ} (h : za ^ n = 1) :
    n % 2 = 0 := by
  rw [pow_eq_pow_mod n hR.za2] at h
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
  · exact h0
  · rw [h1, pow_one] at h
    exact absurd h hza

theorem c_commute_z (hC : P1cRel x za c y z) (j : Fin 5) : Commute c (z j) :=
  commute_of_fcomm_one (hC.zc j)

theorem c_commute_za (hC : P1cRel x za c y z) : Commute c za :=
  (commute_of_fcomm_one hC.cza).symm

theorem absorb (hC : P1cRel x za c y z) (a₀ a₁ a₂ a₃ b m : ℕ) :
    Ee z za a₀ a₁ a₂ a₃ b * (c * za ^ m) = Ee z za a₀ a₁ a₂ a₃ (b + m) * c := by
  rw [((c_commute_za hC).pow_right m).eq, ← mul_assoc, Ee_mul_za]

theorem shape_a (hR : P1Rel x w za y z) (hza : za ≠ 1) {a₀ a₁ a₂ a₃ b : ℕ}
    (h : (y 3 * y 4 * Ee z za a₀ a₁ a₂ a₃ b) * (y 3 * y 4 * Ee z za a₀ a₁ a₂ a₃ b) =
      z 0 * z 2 * za) :
    ∃ e₁ e₂ e₃ e₄ : Fin 2, y 3 * y 4 * Ee z za a₀ a₁ a₂ a₃ b =
      y 3 * y 4 * z 3 * z 0 ^ (e₁ : ℕ) * z 1 ^ (e₂ : ℕ) * z 2 ^ (e₃ : ℕ) * za ^ (e₄ : ℕ) := by
  rw [sq_pair hR (by decide : (3 : Fin 5) ≠ 4)] at h
  have hk : kstar (3 : Fin 5) 4 = 0 ∧ kstar (4 : Fin 5) 3 = 2 := by decide
  rw [hk.1, hk.2] at h
  have hn := odd_of_pow_eq_self hR hza (mul_left_cancel (a := z 0 * z 2) (by
    simpa only [mul_assoc] using h))
  simp only [conjExp, Fin.reduceEq, ite_false, ite_true] at hn
  have h3 : a₃ % 2 = 1 := by omega
  have key : Ee z za a₀ a₁ a₂ a₃ b =
      z 3 * z 0 ^ (a₀ % 2) * z 1 ^ (a₁ % 2) * z 2 ^ (a₂ % 2) * za ^ (b % 2) := by
    rw [Ee_mod hR, h3, ← Ee_third hR]
  refine ⟨⟨a₀ % 2, Nat.mod_lt _ two_pos⟩, ⟨a₁ % 2, Nat.mod_lt _ two_pos⟩,
    ⟨a₂ % 2, Nat.mod_lt _ two_pos⟩, ⟨b % 2, Nat.mod_lt _ two_pos⟩, ?_⟩
  show y 3 * y 4 * Ee z za a₀ a₁ a₂ a₃ b = y 3 * y 4 * z 3 * z 0 ^ (a₀ % 2) * z 1 ^ (a₁ % 2) *
    z 2 ^ (a₂ % 2) * za ^ (b % 2)
  rw [key]
  simp only [mul_assoc]

theorem shape_c (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (hza : za ≠ 1)
    {a₀ a₁ a₂ a₃ b : ℕ}
    (h : (y 4 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c) * (y 4 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c) =
      z 0) :
    ∃ e₁ e₂ e₃ e₄ : Fin 2, y 4 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c =
      y 1 * y 4 * c * z 0 ^ (e₁ : ℕ) * z 2 ^ (e₂ : ℕ) * z 3 ^ (e₃ : ℕ) * za ^ (e₄ : ℕ) := by
  have hK : c * (y 4 * y 1) = (y 4 * y 1) * (z 4 * z 1 * za) * c := by collc0 hR hC
  rw [sq_pair_c hR hC (by decide : (4 : Fin 5) ≠ 1) hK] at h
  have hk : kstar (4 : Fin 5) 1 = 3 ∧ kstar (1 : Fin 5) 4 = 2 := by decide
  rw [hk.1, hk.2] at h
  have h0 : z 3 * z 2 * z 4 * z 1 = z 0 := by coll hR
  rw [h0] at h
  have hn := even_of_pow_eq_one hR hza (mul_left_cancel (a := z 0) (by
    simpa only [mul_one] using h))
  simp only [conjExp, Fin.reduceEq, ite_false, ite_true] at hn
  have h1 : a₁ % 2 = 0 := by omega
  have hyy : y 4 * y 1 = y 1 * y 4 * (z 3 * z 2) := by coll hR
  have hcz : Commute c (z 3 * z 2 * Ee z za a₀ a₁ a₂ a₃ b) :=
    ((c_commute_z hC 3).mul_right (c_commute_z hC 2)).mul_right (c_commute_Ee hC a₀ a₁ a₂ a₃ b)
  have e1 : y 4 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c =
      y 1 * y 4 * c * (z 3 * z 2 * Ee z za a₀ a₁ a₂ a₃ b) := by
    calc y 4 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c
        = y 1 * y 4 * (z 3 * z 2) * Ee z za a₀ a₁ a₂ a₃ b * c := by rw [hyy]
      _ = y 1 * y 4 * ((z 3 * z 2 * Ee z za a₀ a₁ a₂ a₃ b) * c) := by simp only [mul_assoc]
      _ = y 1 * y 4 * (c * (z 3 * z 2 * Ee z za a₀ a₁ a₂ a₃ b)) := by rw [hcz.eq]
      _ = _ := by simp only [mul_assoc]
  have e2 : z 3 * z 2 * Ee z za a₀ a₁ a₂ a₃ b = Ee z za a₀ a₁ (a₂ + 1) (a₃ + 1) b := by
    have z3e : z 3 = Ee z za 0 0 0 1 0 := by simp [Ee]
    have z2e : z 2 = Ee z za 0 0 1 0 0 := by simp [Ee]
    rw [z3e, z2e, Ee_mul hR, Ee_mul hR]
    exact Ee_congr (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨⟨a₀ % 2, Nat.mod_lt _ two_pos⟩, ⟨(a₂ + 1) % 2, Nat.mod_lt _ two_pos⟩,
    ⟨(a₃ + 1) % 2, Nat.mod_lt _ two_pos⟩, ⟨b % 2, Nat.mod_lt _ two_pos⟩, ?_⟩
  show _ = y 1 * y 4 * c * z 0 ^ (a₀ % 2) * z 2 ^ ((a₂ + 1) % 2) * z 3 ^ ((a₃ + 1) % 2) *
    za ^ (b % 2)
  rw [e1, e2, Ee_mod hR, h1]
  simp only [Ee, pow_zero, mul_one, mul_assoc]

theorem shape_b (hR : P1Rel x w za y z) (hC : P1cRel x za c y z) (hza : za ≠ 1)
    {a₀ a₁ a₂ a₃ b : ℕ}
    (h : (y 3 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c) * (y 3 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c) =
      z 2 * za) :
    ∃ d₁ d₂ d₃ d₄ : Fin 2, y 3 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c =
      y 1 * y 3 * z 3 * c * z 0 ^ (d₁ : ℕ) * z 2 ^ (d₂ : ℕ) * z 4 ^ (d₃ : ℕ) *
        za ^ (d₄ : ℕ) := by
  have hK : c * (y 3 * y 1) = (y 3 * y 1) * (z 3 * z 1 * za) * c := by collc0 hR hC
  rw [sq_pair_c hR hC (by decide : (3 : Fin 5) ≠ 1) hK] at h
  have hk : kstar (3 : Fin 5) 1 = 4 ∧ kstar (1 : Fin 5) 3 = 0 := by decide
  rw [hk.1, hk.2] at h
  have h0 : z 4 * z 0 * z 3 * z 1 = z 2 := by coll hR
  rw [h0] at h
  have hn := odd_of_pow_eq_self hR hza (mul_left_cancel (a := z 2) h)
  simp only [conjExp, Fin.reduceEq, ite_false, ite_true] at hn
  have hodd : (a₁ + a₃) % 2 = 1 := by omega
  have hyy : y 3 * y 1 = y 1 * y 3 * (z 4 * z 0) := by coll hR
  have hcz : Commute c (z 4 * z 0 * Ee z za a₀ a₁ a₂ a₃ b) :=
    ((c_commute_z hC 4).mul_right (c_commute_z hC 0)).mul_right
      (c_commute_Ee hC a₀ a₁ a₂ a₃ b)
  have e1 : y 3 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c =
      y 1 * y 3 * c * (z 4 * z 0 * Ee z za a₀ a₁ a₂ a₃ b) := by
    calc y 3 * y 1 * Ee z za a₀ a₁ a₂ a₃ b * c
        = y 1 * y 3 * (z 4 * z 0) * Ee z za a₀ a₁ a₂ a₃ b * c := by rw [hyy]
      _ = y 1 * y 3 * ((z 4 * z 0 * Ee z za a₀ a₁ a₂ a₃ b) * c) := by simp only [mul_assoc]
      _ = y 1 * y 3 * (c * (z 4 * z 0 * Ee z za a₀ a₁ a₂ a₃ b)) := by rw [hcz.eq]
      _ = _ := by simp only [mul_assoc]
  have e2 : z 4 * z 0 * Ee z za a₀ a₁ a₂ a₃ b =
      Ee z za (a₀ + 1 + 1) (a₁ + 1) (a₂ + 1) (a₃ + 1) b := by
    have z0e : z 0 = Ee z za 1 0 0 0 0 := by simp [Ee]
    rw [z_four' hR, z0e, Ee_mul hR, Ee_mul hR]
    exact Ee_congr (by omega) (by omega) (by omega) (by omega) (by omega)
  have hc3 : Commute c (z 3) := c_commute_z hC 3
  obtain ⟨d₃, hd₃⟩ : ∃ d₃ : ℕ, d₃ = (a₁ + 1) % 2 := ⟨_, rfl⟩
  have e3 : ∀ d₁ d₂ d₄ : ℕ, z 3 * z 0 ^ d₁ * z 2 ^ d₂ * z 4 ^ d₃ * za ^ d₄ =
      Ee z za (d₁ + d₃) d₃ (d₂ + d₃) (1 + d₃) d₄ := by
    intro d₁ d₂ d₄
    have z0e : z 0 ^ d₁ = Ee z za d₁ 0 0 0 0 := by simp [Ee]
    have z2e : z 2 ^ d₂ = Ee z za 0 0 d₂ 0 0 := by simp [Ee]
    have z3e : z 3 = Ee z za 0 0 0 1 0 := by simp [Ee]
    have zae : za ^ d₄ = Ee z za 0 0 0 0 d₄ := by simp [Ee]
    rw [z3e, z0e, z2e, z4_pow hR, zae, Ee_mul hR, Ee_mul hR, Ee_mul hR, Ee_mul hR]
    exact Ee_congr (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨⟨(a₀ + d₃) % 2, Nat.mod_lt _ two_pos⟩, ⟨(a₂ + 1 + d₃) % 2, Nat.mod_lt _ two_pos⟩,
    ⟨d₃, by omega⟩, ⟨b % 2, Nat.mod_lt _ two_pos⟩, ?_⟩
  show _ = y 1 * y 3 * z 3 * c * z 0 ^ ((a₀ + d₃) % 2) * z 2 ^ ((a₂ + 1 + d₃) % 2) * z 4 ^ d₃ *
    za ^ (b % 2)
  have e4 : y 1 * y 3 * z 3 * c * z 0 ^ ((a₀ + d₃) % 2) * z 2 ^ ((a₂ + 1 + d₃) % 2) * z 4 ^ d₃ *
      za ^ (b % 2) = y 1 * y 3 * c * (z 3 * z 0 ^ ((a₀ + d₃) % 2) * z 2 ^ ((a₂ + 1 + d₃) % 2) *
        z 4 ^ d₃ * za ^ (b % 2)) := by
    simp only [mul_assoc]
    rw [hc3.symm.left_comm]
  have e5 : Ee z za (a₀ + 1 + 1) (a₁ + 1) (a₂ + 1) (a₃ + 1) b =
      Ee z za ((a₀ + d₃) % 2 + d₃) d₃ ((a₂ + 1 + d₃) % 2 + d₃) (1 + d₃) (b % 2) := by
    rw [Ee_mod hR (a₀ + 1 + 1), Ee_mod hR ((a₀ + d₃) % 2 + d₃)]
    exact Ee_congr (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [e1, e2, e4, e3, e5]

end Sec9P4F95Alg

end CFSG.Quasithin.Fan86
