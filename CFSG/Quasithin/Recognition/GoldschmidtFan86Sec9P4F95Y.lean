module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Alg
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95E

public section

namespace CFSG.Quasithin.Fan86

namespace Sec9P4F95Alg

variable {H : Type*} [Group H] {x w za c : H} {y z : Fin 5 → H}

theorem Ee_congr {a₀ a₁ a₂ a₃ b a₀' a₁' a₂' a₃' b' : ℕ} (h₀ : a₀ = a₀') (h₁ : a₁ = a₁')
    (h₂ : a₂ = a₂') (h₃ : a₃ = a₃') (hb : b = b') :
    Ee z za a₀ a₁ a₂ a₃ b = Ee z za a₀' a₁' a₂' a₃' b' := by
  subst h₀ h₁ h₂ h₃ hb
  rfl

@[expose] def conjExp (i : Fin 5) (a₀ a₁ a₂ a₃ : ℕ) : ℕ :=
  (if i = 0 then 0 else a₀) + (if i = 1 then 0 else a₁) + (if i = 2 then 0 else a₂) +
    (if i = 3 then 0 else a₃)

theorem y_conj_z (hR : P1Rel x w za y z) (i j : Fin 5) :
    (y i)⁻¹ * z j * y i = z j * za ^ (if i = j then 0 else 1) := by
  have h := hR.yz i j
  unfold fcomm at h
  rw [hR.z_inv] at h
  have h2 : (y i)⁻¹ * z j * y i = (if i = j then 1 else za) * z j := by
    calc (y i)⁻¹ * z j * y i = ((y i)⁻¹ * z j * y i * z j) * z j := by
          rw [mul_assoc _ (z j) (z j), ← pow_two, hR.z2, mul_one]
      _ = _ := by rw [h]
  by_cases hij : i = j
  · simp only [hij, ite_true, one_mul, pow_zero, mul_one] at h2 ⊢
    exact h2
  · simp only [hij, ite_false, pow_one] at h2 ⊢
    rw [h2]
    exact (z_commute_za hR j).symm.eq

theorem y_conj_za (hR : P1Rel x w za y z) (i : Fin 5) : (y i)⁻¹ * za * y i = za :=
  conj_eq_of_fcomm_eq_one (hR.cent_y i)

theorem conj_Ee_of (hR : P1Rel x w za y z) {u : H} {k : Fin 5 → ℕ}
    (hz : ∀ j, u⁻¹ * z j * u = z j * za ^ k j) (hza : u⁻¹ * za * u = za)
    (a₀ a₁ a₂ a₃ b : ℕ) :
    u⁻¹ * Ee z za a₀ a₁ a₂ a₃ b * u =
      Ee z za a₀ a₁ a₂ a₃ (b + (k 0 * a₀ + k 1 * a₁ + k 2 * a₂ + k 3 * a₃)) := by
  have hp : ∀ (j : Fin 5) (n : ℕ), u⁻¹ * z j ^ n * u = z j ^ n * za ^ (k j * n) := by
    intro j n
    have h1 : u⁻¹ * z j ^ n * u = (u⁻¹ * z j * u) ^ n := by
      have := conj_pow (a := u⁻¹) (b := z j) (i := n)
      simpa using this.symm
    rw [h1, hz j, ((z_commute_za hR j).pow_right (k j)).mul_pow n, ← pow_mul]
  have hq : u⁻¹ * za ^ b * u = za ^ b := by
    have h1 : u⁻¹ * za ^ b * u = (u⁻¹ * za * u) ^ b := by
      have := conj_pow (a := u⁻¹) (b := za) (i := b)
      simpa using this.symm
    rw [h1, hza]
  unfold Ee
  have e : u⁻¹ * (z 0 ^ a₀ * z 1 ^ a₁ * z 2 ^ a₂ * z 3 ^ a₃ * za ^ b) * u =
      (u⁻¹ * z 0 ^ a₀ * u) * (u⁻¹ * z 1 ^ a₁ * u) * (u⁻¹ * z 2 ^ a₂ * u) *
        (u⁻¹ * z 3 ^ a₃ * u) * (u⁻¹ * za ^ b * u) := by group
  rw [e, hp 0, hp 1, hp 2, hp 3, hq]
  have h0 : z 0 ^ a₀ * za ^ (k 0 * a₀) = Ee z za a₀ 0 0 0 (k 0 * a₀) := by simp [Ee]
  have h1 : z 1 ^ a₁ * za ^ (k 1 * a₁) = Ee z za 0 a₁ 0 0 (k 1 * a₁) := by simp [Ee]
  have h2 : z 2 ^ a₂ * za ^ (k 2 * a₂) = Ee z za 0 0 a₂ 0 (k 2 * a₂) := by simp [Ee]
  have h3 : z 3 ^ a₃ * za ^ (k 3 * a₃) = Ee z za 0 0 0 a₃ (k 3 * a₃) := by simp [Ee]
  have hb : za ^ b = Ee z za 0 0 0 0 b := by simp [Ee]
  rw [h0, h1, h2, h3, hb, Ee_mul hR, Ee_mul hR, Ee_mul hR, Ee_mul hR]
  exact Ee_congr (by omega) (by omega) (by omega) (by omega) (by ring)

theorem y_conj_Ee (hR : P1Rel x w za y z) (i : Fin 5) (a₀ a₁ a₂ a₃ b : ℕ) :
    (y i)⁻¹ * Ee z za a₀ a₁ a₂ a₃ b * y i =
      Ee z za a₀ a₁ a₂ a₃ (b + conjExp i a₀ a₁ a₂ a₃) := by
  rw [conj_Ee_of hR (k := fun j => if i = j then 0 else 1) (y_conj_z hR i) (y_conj_za hR i)]
  refine Ee_congr rfl rfl rfl rfl ?_
  unfold conjExp
  congr 1
  split_ifs <;> simp_all

theorem z_commute_Ee (hR : P1Rel x w za y z) (j : Fin 5) (a₀ a₁ a₂ a₃ b : ℕ) :
    Commute (z j) (Ee z za a₀ a₁ a₂ a₃ b) :=
  ((((((z_commute hR j 0).pow_right a₀).mul_right ((z_commute hR j 1).pow_right a₁)).mul_right
    ((z_commute hR j 2).pow_right a₂)).mul_right ((z_commute hR j 3).pow_right a₃)).mul_right
    ((z_commute_za hR j).pow_right b))

theorem za_commute_Ee (hR : P1Rel x w za y z) (a₀ a₁ a₂ a₃ b : ℕ) :
    Commute za (Ee z za a₀ a₁ a₂ a₃ b) :=
  ((((((z_commute_za hR 0).symm.pow_right a₀).mul_right
    ((z_commute_za hR 1).symm.pow_right a₁)).mul_right
    ((z_commute_za hR 2).symm.pow_right a₂)).mul_right
    ((z_commute_za hR 3).symm.pow_right a₃)).mul_right ((Commute.refl za).pow_right b))

theorem c_commute_Ee (hC : P1cRel x za c y z) (a₀ a₁ a₂ a₃ b : ℕ) :
    Commute c (Ee z za a₀ a₁ a₂ a₃ b) := by
  have hz : ∀ j, Commute c (z j) := fun j => commute_of_fcomm_one (hC.zc j)
  have hza : Commute c za := (commute_of_fcomm_one hC.cza).symm
  exact ((((((hz 0).pow_right a₀).mul_right ((hz 1).pow_right a₁)).mul_right
    ((hz 2).pow_right a₂)).mul_right ((hz 3).pow_right a₃)).mul_right (hza.pow_right b))

end Sec9P4F95Alg

end CFSG.Quasithin.Fan86
