module

public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixed

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.QuasithinUnique.Setup.X7 CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem suzukiS_zero_map_mulVec (c : ℕ) (v : K) (u : Fin 4 → K) :
    ((suzukiS a 0 v).map (· ^ 2 ^ c)).mulVec u =
      ![u 0, u 1, v ^ 2 ^ c * u 0 + u 2,
        (v ^ 2 ^ (a + 1)) ^ 2 ^ c * u 0 + v ^ 2 ^ c * u 1 + u 3] := by
  ext i
  fin_cases i <;>
    simp [suzukiS, suzukiN, Matrix.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem suzukiS_zero_map_sub_mulVec (c : ℕ) (v : K) (u : Fin 4 → K) :
    ((suzukiS a 0 v).map (· ^ 2 ^ c)).mulVec u - u =
      ![0, 0, v ^ 2 ^ c * u 0,
        (v ^ 2 ^ (a + 1)) ^ 2 ^ c * u 0 + v ^ 2 ^ c * u 1] := by
  rw [suzukiS_zero_map_mulVec]
  ext i
  fin_cases i <;> simp

private theorem mem_fixedSub_zpowers_iff
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) {c : ℕ} {φ : W ≃+ (Fin 4 → K)}
    (hφ : ∀ g w, φ (ρ g w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec (φ w))
    {z : ↥(suzukiGroup a K)} (hz : z ∈ suzukiZ0 a K) (hz1 : z ≠ 1) {w : W} :
    w ∈ fixedSub ρ (Subgroup.zpowers z) ↔ (φ w) 0 = 0 ∧ (φ w) 1 = 0 := by
  obtain ⟨v, hzv⟩ := (mem_suzukiZ0_iff hK).1 hz
  have hv : v ≠ 0 := by
    intro hv0
    apply hz1
    rw [← hzv, hv0, suzukiSElt_zero_zero hK]
  rw [mem_fixedSub_zpowers]
  constructor
  · intro h1
    have h2 : ((suzukiS a 0 v).map (· ^ 2 ^ c)).mulVec (φ w) = φ w := by
      have hφ' := hφ z w
      rw [← hzv] at hφ'
      rw [← hzv] at h1
      rw [h1, coe_suzukiSElt] at hφ'
      exact hφ'.symm
    rw [suzukiS_zero_map_mulVec] at h2
    have h0 : (φ w) 0 = 0 := by
      have h3 : v ^ 2 ^ c * (φ w) 0 + (φ w) 2 = (φ w) 2 := by
        simpa using congrFun h2 2
      have h4 : v ^ 2 ^ c * (φ w) 0 + (φ w) 2 = 0 + (φ w) 2 := by
        simpa using h3
      exact (mul_eq_zero.mp (add_right_cancel h4)).resolve_left (pow_ne_zero _ hv)
    refine ⟨h0, ?_⟩
    have h3 : (v ^ 2 ^ (a + 1)) ^ 2 ^ c * (φ w) 0 +
        v ^ 2 ^ c * (φ w) 1 + (φ w) 3 = (φ w) 3 := by
      simpa using congrFun h2 3
    rw [h0] at h3
    have h4 : v ^ 2 ^ c * (φ w) 1 + (φ w) 3 = 0 + (φ w) 3 := by
      simpa using h3
    exact (mul_eq_zero.mp (add_right_cancel h4)).resolve_left (pow_ne_zero _ hv)
  · rintro ⟨h0, h1⟩
    apply φ.injective
    rw [hφ]
    rw [show (((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) =
        (suzukiS a 0 v).map (· ^ 2 ^ c) by rw [← hzv]; rfl]
    rw [suzukiS_zero_map_mulVec]
    ext i
    fin_cases i <;> simp [h0, h1]

theorem fixedSub_zpowers_eq_fixedSub_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    {z : ↥(suzukiGroup a K)} (hz : z ∈ suzukiZ0 a K) (hz1 : z ≠ 1) :
    fixedSub ρ (Subgroup.zpowers z) = fixedSub ρ (suzukiZ0 a K) := by
  obtain ⟨c, φ, hφ⟩ := hρ
  ext w
  rw [mem_fixedSub_zpowers_iff hK ρ hφ hz hz1,
    mem_fixedSub_suzukiZ0_iff hK ρ hφ]

theorem range_sub_one_eq_fixedSub_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    {z : ↥(suzukiGroup a K)} (hz : z ∈ suzukiZ0 a K) (hz1 : z ≠ 1) :
    LinearMap.range (ρ z - 1) = fixedSub ρ (suzukiZ0 a K) := by
  obtain ⟨c, φ, hφ⟩ := hρ
  obtain ⟨v, hzv⟩ := (mem_suzukiZ0_iff hK).1 hz
  have hv : v ≠ 0 := by
    intro hv0
    apply hz1
    rw [← hzv, hv0, suzukiSElt_zero_zero hK]
  have hzcoe : (((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =
      suzukiS a 0 v := by rw [← hzv]; rfl
  ext y
  rw [LinearMap.mem_range, mem_fixedSub_suzukiZ0_iff hK ρ hφ]
  change (∃ x, (ρ z - 1) x = y) ↔ (φ y) 0 = 0 ∧ (φ y) 1 = 0
  constructor
  · rintro ⟨x, rfl⟩
    have h : φ ((ρ z - 1) x) =
        (((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec (φ x) -
          φ x := by
      rw [LinearMap.sub_apply, map_sub, hφ, Module.End.one_apply]
    rw [h, hzcoe, suzukiS_zero_map_sub_mulVec]
    simp
  · rintro ⟨h0, h1⟩
    let u : Fin 4 → K :=
      ![((v ^ 2 ^ c)⁻¹) * (φ y) 2,
        ((v ^ 2 ^ c)⁻¹) * ((φ y) 3 + (v ^ 2 ^ (a + 1)) ^ 2 ^ c *
          (((v ^ 2 ^ c)⁻¹) * (φ y) 2)), 0, 0]
    refine ⟨φ.symm u, ?_⟩
    apply φ.injective
    have h : φ ((ρ z - 1) (φ.symm u)) =
        (((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec
          (φ (φ.symm u)) - φ (φ.symm u) := by
      rw [LinearMap.sub_apply, map_sub, hφ, Module.End.one_apply]
    rw [h, hzcoe, suzukiS_zero_map_sub_mulVec, AddEquiv.apply_symm_apply]
    have hv' : v ^ 2 ^ c ≠ 0 := pow_ne_zero _ hv
    ext i
    fin_cases i
    · simp [u, h0, h1]
    · simp [u, h0, h1]
    · simp only [u, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, h0, h1, mul_zero, zero_add, add_zero]
      change v ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) = φ y 2
      rw [mul_inv_cancel_left₀ hv']
    · simp only [u, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three, h0, h1, mul_zero, zero_add, add_zero]
      change (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) +
          v ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * (φ y 3 +
            (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2))) = φ y 3
      rw [mul_inv_cancel_left₀ hv']
      have h2 : (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) +
          (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) = 0 := by
        have h2c : (2 : K) = 0 := CharP.cast_eq_zero K 2
        rw [← two_mul]
        simp [h2c]
      calc (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) +
            (φ y 3 + (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2)) =
          ((v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2) +
            (v ^ 2 ^ (a + 1)) ^ 2 ^ c * ((v ^ 2 ^ c)⁻¹ * φ y 2)) + φ y 3 := by
            abel
        _ = φ y 3 := by rw [h2, zero_add]

private theorem suzukiS_one_zero_map_mulVec (c : ℕ) (u : Fin 4 → K) :
    ((suzukiS a 1 0).map (· ^ 2 ^ c)).mulVec u =
      ![u 0, u 0 + u 1, u 1 + u 2, u 0 + u 1 + u 2 + u 3] := by
  ext i
  fin_cases i <;>
    simp [suzukiS, suzukiN, Matrix.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem mem_fixedSub_suzukiU_iff
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) {c : ℕ} {φ : W ≃+ (Fin 4 → K)}
    (hφ : ∀ g w, φ (ρ g w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec (φ w))
    {w : W} :
    w ∈ fixedSub ρ (suzukiU a K) ↔ (φ w) 0 = 0 ∧ (φ w) 1 = 0 ∧ (φ w) 2 = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    have hZ0 : w ∈ fixedSub ρ (suzukiZ0 a K) :=
      mem_fixedSub.2 fun z hz => hw z (suzukiZ0_le_suzukiU hz)
    obtain ⟨h0, h1⟩ := (mem_fixedSub_suzukiZ0_iff hK ρ hφ).1 hZ0
    refine ⟨h0, h1, ?_⟩
    have h2 : ((suzukiS a 1 0).map (· ^ 2 ^ c)).mulVec (φ w) = φ w := by
      have hφ' := hφ (suzukiSElt a K 1 0) w
      rw [hw _ (suzukiSElt_mem_suzukiU a K 1 0), coe_suzukiSElt] at hφ'
      exact hφ'.symm
    rw [suzukiS_one_zero_map_mulVec] at h2
    have h3 : (φ w) 0 + (φ w) 1 + (φ w) 2 + (φ w) 3 = (φ w) 3 := by
      simpa using congrFun h2 3
    rw [h0, h1] at h3
    simpa using h3
  · rintro ⟨h0, h1, h2⟩ z hz
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hz
    apply φ.injective
    rw [hφ]
    rw [show (((suzukiSElt a K u v : suzukiGroup a K) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = suzukiS a u v from coe_suzukiSElt a K u v]
    ext i
    fin_cases i <;>
      simp [suzukiS, suzukiN, Matrix.map_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_four, h0, h1, h2]

theorem natCard_fixedSub_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ) :
    Nat.card (fixedSub ρ (suzukiU a K)) = Nat.card K := by
  obtain ⟨c, φ, hφ⟩ := hρ
  have e : {u : Fin 4 → K // u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0} ≃ K :=
    { toFun := fun u => u.1 3
      invFun := fun x => ⟨![0, 0, 0, x], by simp⟩
      left_inv := fun u => by
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [u.2.1, u.2.2.1, u.2.2.2]
      right_inv := fun x => by simp }
  have h1 : Nat.card (fixedSub ρ (suzukiU a K)) =
      Nat.card {u : Fin 4 → K // u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0} :=
    Nat.card_congr
      (Equiv.subtypeEquiv φ.toEquiv (fun w => mem_fixedSub_suzukiU_iff hK ρ hφ))
  rw [h1, Nat.card_congr e]

end CFSG.RankThree.GF2n.Tim81.Sec2

end
