module

public import CFSG.RankThree.PartOne.KFOUT3.KtyPairAct
public import CFSG.RankThree.PartOne.KF.G2Dih
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def g2Act (hp : p.Prime) (h5 : 5 ≤ p) :
    DihedralGroup 6 →* MulAut (G2V p K) :=
  pairAct g2s0_mul_self g2s1_mul_self (g2_braid hp h5)

theorem g2Act_sr_zero (hp : p.Prime) (h5 : 5 ≤ p) :
    g2Act (K := K) hp h5 (DihedralGroup.sr 0) = g2s0 p K :=
  pairAct_sr_zero _ _ _

theorem g2Act_sr_one (hp : p.Prime) (h5 : 5 ≤ p) :
    g2Act (K := K) hp h5 (DihedralGroup.sr 1) = g2s1 p K :=
  pairAct_sr_one (by decide) _ _ _

theorem g2Act_injective (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective (g2Act (K := K) hp h5) := by
  refine pairAct_injective _ _ _ (orderOf_g2rot hp h5 hζ) ?_
  have hrel : g2s0 p K * (g2s0 p K * g2s1 p K) * (g2s0 p K)⁻¹ = (g2s0 p K * g2s1 p K)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right (g2s0_mul_self (p := p) (K := K))]
    exact pair_conj g2s0_mul_self g2s1_mul_self
  exact not_mem_zpowers_of_conj_eq_inv hrel (g2rot_sq_ne_one hp hζ)

theorem card_movedV_g2v_neg (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (φ : MulAut (G2V p K)) (hφ : ∀ v, φ v = v⁻¹) : Nat.card (movedV φ) = p ^ 2 := by
  have h1 := card_movedV_mul_card_fixed φ
  have hker : (movedHom φ).ker = ⊥ := by
    ext v
    rw [mem_ker_movedHom, hφ, Subgroup.mem_bot]
    constructor
    · intro h
      funext i
      exact eq_one_of_inv_eq_self (hp.odd_of_ne_two hp2) (congrFun h i)
    · rintro rfl
      simp
  rw [hker, Subgroup.card_bot, mul_one, card_G2V hp.pos hζ] at h1
  exact h1

theorem g2Act_refl (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    ∀ γ : DihedralGroup 6, γ * γ = 1 → γ ≠ 1 →
      Nat.card (movedV (g2Act (K := K) hp h5 γ)) = p → ∃ i : ZMod 6, γ = DihedralGroup.sr i := by
  intro γ h2 h1 hc
  rcases dih6_involution_cases γ h2 h1 with rfl | h
  · exfalso
    have hφ : ∀ v : G2V p K, g2Act (K := K) hp h5 (DihedralGroup.r 3) v = v⁻¹ := fun v =>
      g2rot_cube v
    rw [card_movedV_g2v_neg hp (by omega) hζ _ hφ] at hc
    have h3 : p * 1 = p * p := by rw [mul_one, ← sq]; exact hc.symm
    exact hp.ne_one (Nat.eq_of_mul_eq_mul_left hp.pos h3).symm
  · exact h

theorem row3_not_dvd {q : ℕ} (hq : 2 ≤ q) :
    ¬ (q ^ 3) * (((q ^ 3) ^ 2) - 1) ∣ q * (q ^ 2 - 1) := by
  intro hdvd
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hpos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  have h1 : q * (q ^ 2 - 1) < q ^ 3 := by
    have : q ^ 2 - 1 < q ^ 2 := by omega
    calc q * (q ^ 2 - 1) < q * q ^ 2 := Nat.mul_lt_mul_of_pos_left this (by omega)
      _ = q ^ 3 := by ring
  have h2 : 1 ≤ (q ^ 3) ^ 2 - 1 := by
    have : 4 ≤ (q ^ 3) ^ 2 := by nlinarith [Nat.pow_le_pow_left hq 3]
    omega
  have h3 : q ^ 3 ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := Nat.le_mul_of_pos_right _ h2
  omega

end CFSG.RankThree.PartOne.KFOUT3
