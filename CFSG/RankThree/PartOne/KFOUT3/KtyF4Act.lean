module

public import CFSG.RankThree.PartOne.KFOUT3.KtyG2Act
public import CFSG.RankThree.PartOne.KF.F4Dih

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K] {θ : ℕ}

@[expose] noncomputable def f4Act (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    DihedralGroup 8 →* MulAut (G2V p K) :=
  pairAct f4s1_mul_self f4s2_mul_self (f4_braid hθ)

theorem f4Act_sr_zero (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    f4Act (K := K) hθ (DihedralGroup.sr 0) = f4s1 p K :=
  pairAct_sr_zero _ _ _

theorem f4Act_sr_one (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    f4Act (K := K) hθ (DihedralGroup.sr 1) = f4s2 p K θ :=
  pairAct_sr_one (by decide) _ _ _

theorem f4Act_injective (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) : Function.Injective (f4Act (K := K) hθ) := by
  refine pairAct_injective _ _ _ (orderOf_f4rot hp h5 hζ hθ) ?_
  have hrel : f4s1 p K * (f4s1 p K * f4s2 p K θ) * (f4s1 p K)⁻¹ =
      (f4s1 p K * f4s2 p K θ)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right (f4s1_mul_self (p := p) (K := K))]
    exact pair_conj f4s1_mul_self f4s2_mul_self
  exact not_mem_zpowers_of_conj_eq_inv hrel (f4rot_sq_ne_one hp h5 hζ hθ)

theorem f4Act_refl (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hθ : (p : ℤ) ∣ 2 * (θ : ℤ) ^ 2 - 1) :
    ∀ γ : DihedralGroup 8, γ * γ = 1 → γ ≠ 1 →
      Nat.card (movedV (f4Act (K := K) hθ γ)) = p → ∃ i : ZMod 8, γ = DihedralGroup.sr i := by
  intro γ h2 h1 hc
  rcases dih8_involution_cases γ h2 h1 with rfl | h
  · exfalso
    have hφ : ∀ v : G2V p K, f4Act (K := K) hθ (DihedralGroup.r 4) v = v⁻¹ := fun v =>
      f4_rot_four hθ v
    rw [card_movedV_g2v_neg hp (by omega) hζ _ hφ] at hc
    have h3 : p * 1 = p * p := by rw [mul_one, ← sq]; exact hc.symm
    exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hp.pos h3).symm
  · exact h

theorem row4_not_dvd {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 2 * (q ^ 2 + 1) * (q - 1) ∣ q * (q ^ 2 - 1) := by
  intro hdvd
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 1 ≤ r := by omega
  have e1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  rw [e1, Nat.add_sub_cancel] at hdvd
  have hpos : 0 < (r + 1) * (r * (r + 2)) := by positivity
  have hle := Nat.le_of_dvd hpos hdvd
  have h1 : (r + 1) ^ 2 * ((r + 1) ^ 2 + 1) * r =
      ((r + 1) * r) * ((r + 1) * ((r + 1) ^ 2 + 1)) := by ring
  have h2 : (r + 1) * (r * (r + 2)) = ((r + 1) * r) * (r + 2) := by ring
  rw [h1, h2] at hle
  have hX : 0 < (r + 1) * r := by positivity
  have h3 := Nat.le_of_mul_le_mul_left hle hX
  have h5 : 5 ≤ (r + 1) ^ 2 + 1 := by nlinarith
  have h6 : (r + 1) * 5 ≤ (r + 1) * ((r + 1) ^ 2 + 1) := Nat.mul_le_mul_left _ h5
  omega

end CFSG.RankThree.PartOne.KFOUT3
