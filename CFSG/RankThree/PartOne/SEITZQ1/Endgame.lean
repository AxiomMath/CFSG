module

public import CFSG.RankThree.PartOne.SEITZ12.SuzukiTwo

public section

namespace CFSG.RankThree.PartOne.SEITZQ1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover

theorem phi2end_cartanPair_check :
    (F4.cartanPair (f4i 0) (stdFourRoot 0) = 0 ∧ F4.cartanPair (f4i 3) (stdFourRoot 0) = -1) ∧
    (F4.cartanPair (f4i 0) (stdFourRoot 1) = -1 ∧ F4.cartanPair (f4i 3) (stdFourRoot 1) = 0) ∧
    (F4.cartanPair (f4i 0) (stdFourRoot 2) = -1 ∧ F4.cartanPair (f4i 3) (stdFourRoot 2) = -1) ∧
    (F4.cartanPair (f4i 0) (stdFourRoot 3) = -1 ∧ F4.cartanPair (f4i 3) (stdFourRoot 3) = -2) := by
  decide +kernel

section Weights

variable {m : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem phi2end_weights (u : Kˣ) :
    ((torusWeight m (stdFourRoot 0) (u, 1) : Kˣ) : K) = ((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K) ∧
    ((torusWeight m (stdFourRoot 1) (u, 1) : Kˣ) : K) = ((u ^ (-1 : ℤ) : Kˣ) : K) ∧
    ((torusWeight m (stdFourRoot 2) (u, 1) : Kˣ) : K) = ((u ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) ∧
    ((torusWeight m (stdFourRoot 3) (u, 1) : Kˣ) : K) =
      ((u ^ ((-1 : ℤ) - 2 * 2 ^ m) : Kˣ) : K) := by
  obtain ⟨⟨h00, h30⟩, ⟨h01, h31⟩, ⟨h02, h32⟩, ⟨h03, h33⟩⟩ := phi2end_cartanPair_check
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [torusWeight_fst] <;>
    simp only [torusExp0, h00, h30, h01, h31, h02, h32, h03, h33] <;>
    exact congrArg (fun e : ℤ => ((u ^ e : Kˣ) : K)) (by ring)

theorem phi2end_sigma_weights (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) :
    largeReeSigma m (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K)) = ((u ^ (-1 : ℤ) : Kˣ) : K) ∧
    largeReeSigma m (((u ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K)) =
      ((u ^ ((-1 : ℤ) - 2 * 2 ^ m) : Kˣ) : K) := by
  have e2 : ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 := by ring
  refine ⟨?_, ?_⟩
  all_goals
    rw [largeReeSigma, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    congr 1
    refine units_zpow_congr hK u (-1) ?_
    push_cast
    rw [e2]
    ring

theorem phi2end_zpow_surj_left (hK : Nat.card K = 2 ^ (2 * m + 1)) (v : Kˣ) :
    (v ^ ((-2 : ℤ) * 2 ^ m)) ^ (-(2 ^ m : ℤ)) = v := by
  rw [← zpow_mul]
  conv_rhs => rw [← zpow_one v]
  refine units_zpow_congr hK v 1 ?_
  rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
  ring

theorem phi2end_zpow_surj_right (hK : Nat.card K = 2 ^ (2 * m + 1)) (v : Kˣ) :
    (v ^ ((2 : ℤ) * 2 ^ m - 2)) ^ ((-1 : ℤ) - 2 ^ m) = v := by
  rw [← zpow_mul]
  conv_rhs => rw [← zpow_one v]
  refine units_zpow_congr hK v (-1) ?_
  rw [show ((2 : ℤ) ^ (2 * m + 1)) = 2 * (2 ^ m) ^ 2 by ring]
  ring

end Weights

section Conj

variable {m : ℕ} {K : Type} [Field K] [Finite K]

theorem phi2end_torus_conj_stdFourG (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) (b c : K) :
    torusPair m (u, 1) * stdFourG m b c * (torusPair m (u, 1))⁻¹ =
      stdFourG m (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K) * b)
        (((u ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c) := by
  obtain ⟨w0, w1, w2, w3⟩ := phi2end_weights (m := m) (K := K) u
  obtain ⟨s1, s2⟩ := phi2end_sigma_weights hK u
  have F3 : ((u ^ ((-1 : ℤ) - 2 * 2 ^ m) : Kˣ) : K) =
      (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K)) ^ 2 * ((u ^ (-1 : ℤ) : Kˣ) : K) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
    push_cast
    ring
  have key : ((u ^ ((-1 : ℤ) - 2 * 2 ^ m) : Kˣ) : K) *
        (largeReeSigma m c + b ^ 2 * largeReeSigma m b) =
      largeReeSigma m (((u ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c) +
        (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K) * b) ^ 2 *
          largeReeSigma m (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K) * b) := by
    rw [largeReeSigma_mul, largeReeSigma_mul, s1, s2, F3]
    ring
  have e : ∀ n A B C D : ModGL F4.tag K, n * (A * B * C * D) * n⁻¹ =
      n * A * n⁻¹ * (n * B * n⁻¹) * (n * C * n⁻¹) * (n * D * n⁻¹) := fun _ _ _ _ _ => by group
  unfold stdFourG
  rw [e, torusPair_conj_pinnedX m (u, 1) (isRoot_stdFourRoot 0),
    torusPair_conj_pinnedX m (u, 1) (isRoot_stdFourRoot 1),
    torusPair_conj_pinnedX m (u, 1) (isRoot_stdFourRoot 2),
    torusPair_conj_pinnedX m (u, 1) (isRoot_stdFourRoot 3), w0, w1, w2, w3, key,
    largeReeSigma_mul _ b, s1]

theorem phi2end_torus_conj_sylowB (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) (b c : K) :
    torusPair m (u, 1) * sylowB m K b c * (torusPair m (u, 1))⁻¹ =
      sylowB m K (((u ^ (-(2 ^ m : ℤ)) : Kˣ) : K) * b)
        (((u ^ ((-1 : ℤ) - 2 ^ m) : Kˣ) : K) * c) := by
  rw [sylowB_eq_largeReeCoord, sylowB_eq_largeReeCoord, ← stdFourG_eq_largeReeCoord,
    ← stdFourG_eq_largeReeCoord]
  exact phi2end_torus_conj_stdFourG hK u b c

end Conj

section Endgame

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem phi2end_torusPair_mem_localBlock (hK : Nat.card K = 2 ^ (2 * m + 1)) (u : Kˣ) :
    torusPair m (u, 1) ∈ F4.reeLocalBlock K m ⟨0, by decide⟩ := by
  have h : torusPair m (u, 1) = largeReeA1Hom K m (HSL u) := by
    rw [torusPair_apply, one_pow, torusElt_one, torusElt_one, one_mul, mul_one,
      largeReeA1Hom_HSL]
    congr 2
  have hr : largeReeA1Hom K m (HSL u) ∈ (largeReeA1Hom K m).range := ⟨HSL u, rfl⟩
  rw [largeReeA1Hom_range hK] at hr
  rw [h]
  exact hr

theorem phi2end_sylowB_mem (hK : Nat.card K = 2 ^ (2 * m + 1)) (D : Subgroup (ModGL F4.tag K))
    (hT : ∀ u : Kˣ, torusPair m (u, 1) ∈ D) (hB : sylowB m K 1 0 ∈ D) (b c : K) :
    sylowB m K b c ∈ D := by
  have hb0 : ∀ b : K, sylowB m K b 0 ∈ D := fun b => by
    by_cases hb : b = 0
    · rw [hb, sylowB_zero_zero]
      exact one_mem D
    · have h := phi2end_torus_conj_sylowB hK (Units.mk0 b hb ^ ((-2 : ℤ) * 2 ^ m)) 1 0
      rw [phi2end_zpow_surj_left hK, Units.val_mk0, mul_one, mul_zero] at h
      rw [← h]
      exact mul_mem (mul_mem (hT _) hB) (inv_mem (hT _))
  have hz : sylowB m K 0 1 ∈ D := by
    have h := SEITZ12.phi4s_sylowB_sq hK (1 : K) 0
    rw [largeReeSigma_one, mul_one] at h
    rw [← h]
    exact mul_mem hB hB
  have hc0 : ∀ c : K, sylowB m K 0 c ∈ D := fun c => by
    by_cases hc : c = 0
    · rw [hc, sylowB_zero_zero]
      exact one_mem D
    · have h := phi2end_torus_conj_sylowB hK (Units.mk0 c hc ^ ((2 : ℤ) * 2 ^ m - 2)) 0 1
      rw [phi2end_zpow_surj_right hK, Units.val_mk0, mul_one, mul_zero] at h
      rw [← h]
      exact mul_mem (mul_mem (hT _) hz) (inv_mem (hT _))
  have h := mul_mem (hb0 b) (hc0 c)
  rwa [SEITZ12.phi4s_sylowB_mul hK, add_zero, zero_add, mul_zero, add_zero] at h

theorem phi2end_U₂_le (hK : Nat.card K = 2 ^ (2 * m + 1)) (D : Subgroup (ModGL F4.tag K))
    (hD : ∀ b c : K, sylowB m K b c ∈ D) :
    F4.reeFixedOrbitUnipotent K m ⟨1, by decide⟩ ≤ D := fun g hg => by
  obtain ⟨b, c, h⟩ := exists_largeReeCoord_eq hK hg
  rw [← h, ← sylowB_eq_largeReeCoord]
  exact hD b c

theorem reeGamma_le_of_localBlock_zero (hK : Nat.card K = 2 ^ (2 * m + 1))
    (D : Subgroup (ModGL F4.tag K)) (h1 : F4.reeLocalBlock K m ⟨0, by decide⟩ ≤ D)
    (hB : sylowB m K 1 0 ∈ D) (hn : weylTwo K ∈ D) : F4.reeGamma K m ≤ D := by
  have hU := phi2end_U₂_le hK D
    (phi2end_sylowB_mem hK D (fun u => h1 (phi2end_torusPair_mem_localBlock hK u)) hB)
  have hM : F4.reeLocalBlock K m ⟨1, by decide⟩ ≤ D := by
    refine sup_le hU fun y hy => ?_
    rw [← map_conj_reeFixedOrbitUnipotent] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact mul_mem (mul_mem hn (hU hx)) (inv_mem hn)
  rw [large_Ree_simple_pair_generation m K hK]
  exact sup_le h1 hM

end Endgame

end CFSG.RankThree.PartOne.SEITZQ1
