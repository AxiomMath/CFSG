module

public import CFSG.Quasithin.Background.HL3WrNPrime

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix
open scoped Matrix

abbrev scenMat (x y : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, x, y; 0, 1, 0; 0, 0, 1]

theorem scenMat_mul (x y x' y' : ZMod 2) :
    scenMat x y * scenMat x' y' = scenMat (x + x') (y + y') := by
  revert x y x' y'
  decide

theorem scenMat_mul_self (x y : ZMod 2) : scenMat x y * scenMat x y = 1 := by
  revert x y
  decide

theorem scenMat_zero : scenMat 0 0 = 1 := by decide

@[expose] def Scen : Subgroup ↥SL32 where
  carrier := {g | ∃ x y : ZMod 2, mat g = scenMat x y}
  mul_mem' := by
    rintro g h ⟨x, y, hg⟩ ⟨x', y', hh⟩
    exact ⟨x + x', y + y', by rw [mat_mul, hg, hh, scenMat_mul]⟩
  one_mem' := ⟨0, 0, by rw [mat_one, scenMat_zero]⟩
  inv_mem' := by
    rintro g ⟨x, y, hg⟩
    refine ⟨x, y, ?_⟩
    calc mat g⁻¹ = mat g⁻¹ * (mat g * mat g) := by rw [hg, scenMat_mul_self, Matrix.mul_one]
      _ = scenMat x y := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul, hg]

@[expose] noncomputable def Shat : Subgroup (MulAut WMod) := (Scen.prod Scen).map rho

theorem rho_mem_Shat {a b : ↥SL32} (ha : a ∈ Scen) (hb : b ∈ Scen) : rho (a, b) ∈ Shat :=
  ⟨(a, b), ⟨ha, hb⟩, rfl⟩

abbrev eW (i j : Fin 3) : WMod := Multiplicative.ofAdd (Matrix.single i j 1)

theorem toAdd_rho_eW {a b : ↥SL32} {x y x' y' : ZMod 2} (ha : mat a = scenMat x y)
    (hb : mat b = scenMat x' y') (i j : Fin 3) :
    Multiplicative.toAdd (rho (a, b) (eW i j)) =
      scenMat x y * Matrix.single i j 1 * (scenMat x' y')ᵀ := by
  change mat a * Matrix.single i j 1 * (mat b)ᵀ = _
  rw [ha, hb]

theorem scenMat_E00 (x y x' y' : ZMod 2) :
    scenMat x y * Matrix.single 0 0 1 * (scenMat x' y')ᵀ = Matrix.single 0 0 1 := by
  revert x y x' y'
  decide

theorem scenMat_E10 (x y x' y' : ZMod 2) :
    scenMat x y * Matrix.single 1 0 1 * (scenMat x' y')ᵀ =
      Matrix.single 1 0 1 + Matrix.single 0 0 x := by
  revert x y x' y'
  decide

theorem scenMat_E20 (x y x' y' : ZMod 2) :
    scenMat x y * Matrix.single 2 0 1 * (scenMat x' y')ᵀ =
      Matrix.single 2 0 1 + Matrix.single 0 0 y := by
  revert x y x' y'
  decide

theorem scenMat_E01 (x y x' y' : ZMod 2) :
    scenMat x y * Matrix.single 0 1 1 * (scenMat x' y')ᵀ =
      Matrix.single 0 1 1 + Matrix.single 0 0 x' := by
  revert x y x' y'
  decide

theorem scenMat_E02 (x y x' y' : ZMod 2) :
    scenMat x y * Matrix.single 0 2 1 * (scenMat x' y')ᵀ =
      Matrix.single 0 2 1 + Matrix.single 0 0 y' := by
  revert x y x' y'
  decide

theorem Shat_fix_E00 {s : MulAut WMod} (hs : s ∈ Shat) : s (eW 0 0) = eW 0 0 := by
  obtain ⟨⟨a, b⟩, ⟨⟨x, y, ha⟩, ⟨x', y', hb⟩⟩, rfl⟩ := hs
  apply Multiplicative.toAdd.injective
  rw [toAdd_rho_eW ha hb, scenMat_E00]
  rfl

theorem eq_or_eq_mul_eW {X D : WMod} {c : ZMod 2}
    (h : Multiplicative.toAdd X = Multiplicative.toAdd D + Matrix.single 0 0 c) :
    X = D ∨ X = D * eW 0 0 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · left
    apply Multiplicative.toAdd.injective
    rw [h, Matrix.single_zero, add_zero]
  · right
    apply Multiplicative.toAdd.injective
    rw [h]
    rfl

theorem aSet_two_eq_empty_of {W : Type*} [CommGroup W] {Y : Subgroup (MulAut W)} {e : W}
    (he1 : e ≠ 1) (he2 : e * e = 1) (he : ∀ y ∈ Y, y e = e)
    (hD : ∀ g ∈ Y, g ≠ 1 → ∃ D : W, g D = D * e ∧ ∀ y ∈ Y, y D = D ∨ y D = D * e) :
    E3.aSet 2 Y = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun A hA => ?_
  obtain ⟨hAY, hA1, -, hfix⟩ := hA
  obtain ⟨⟨g, hgA⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  obtain ⟨D, hgD, hYD⟩ := hD g (hAY hgA) hg1'
  have hDe : D * e ≠ D := fun h => he1 (mul_left_cancel (h.trans (mul_one D).symm))
  have hmem : ∀ c : ↥A, c ∈ (A ⊓ MulAction.stabilizer (MulAut W) D).subgroupOf A ↔
      (c : MulAut W) D = D := fun c => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  have hidx : (A ⊓ MulAction.stabilizer (MulAut W) D).relIndex A = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgA⟩, fun b => ?_⟩
    have hbY : (b : MulAut W) ∈ Y := hAY b.2
    rw [hmem, hmem]
    have hbg : ((b * ⟨g, hgA⟩ : ↥A) : MulAut W) D = (b : MulAut W) D * e := by
      change (b : MulAut W) (g D) = _
      rw [hgD, map_mul, he _ hbY]
    rw [hbg]
    rcases hYD _ hbY with h | h
    · rw [h]
      exact Or.inr ⟨rfl, hDe⟩
    · rw [h, mul_assoc, he2, mul_one]
      exact Or.inl ⟨rfl, hDe⟩
  have hm : E3.mQuot A (A ⊓ MulAction.stabilizer (MulAut W) D) < 2 := by
    rw [E3.mQuot, hidx, padicValNat.self (by norm_num)]
    norm_num
  have hDB : D ∈ fixV (A ⊓ MulAction.stabilizer (MulAut W) D) := fun x hx => hx.2
  rw [hfix _ inf_le_left hm] at hDB
  exact hDe (hgD.symm.trans (hDB g hgA))

theorem aSet_two_Shat_eq_empty : E3.aSet 2 Shat = ∅ := by
  refine aSet_two_eq_empty_of (e := eW 0 0) (by decide) (by decide) (fun y hy => Shat_fix_E00 hy)
    ?_
  rintro _ ⟨⟨a, b⟩, ⟨⟨x, y, ha⟩, ⟨x', y', hb⟩⟩, rfl⟩ hg1
  have key : ∀ (i j : Fin 3) (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2),
      (∀ u v u' v' : ZMod 2, scenMat u v * Matrix.single i j 1 * (scenMat u' v')ᵀ =
        Matrix.single i j 1 + Matrix.single 0 0 (f u v u' v')) → f x y x' y' = 1 →
      ∃ D : WMod, rho (a, b) D = D * eW 0 0 ∧
        ∀ s ∈ Shat, s D = D ∨ s D = D * eW 0 0 := by
    intro i j f hf h1
    refine ⟨eW i j, ?_, ?_⟩
    · apply Multiplicative.toAdd.injective
      rw [toAdd_rho_eW ha hb, hf, h1]
      rfl
    · rintro _ ⟨⟨a', b'⟩, ⟨⟨u, v, ha'⟩, ⟨u', v', hb'⟩⟩, rfl⟩
      exact eq_or_eq_mul_eW (by rw [toAdd_rho_eW ha' hb', hf]; rfl)
  by_cases hx : x = 1
  · exact key 1 0 (fun u _ _ _ => u) scenMat_E10 hx
  by_cases hy : y = 1
  · exact key 2 0 (fun _ v _ _ => v) scenMat_E20 hy
  by_cases hx' : x' = 1
  · exact key 0 1 (fun _ _ u' _ => u') scenMat_E01 hx'
  by_cases hy' : y' = 1
  · exact key 0 2 (fun _ _ _ v' => v') scenMat_E02 hy'
  exfalso
  apply hg1
  have h0 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  rw [h0 x hx, h0 y hy, scenMat_zero] at ha
  rw [h0 x' hx', h0 y' hy', scenMat_zero] at hb
  have ha1 : a = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact ha
  have hb1 : b = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hb
  rw [ha1, hb1]
  exact map_one rho

abbrev blk (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![M 1 1, M 1 2; M 2 1, M 2 2]

theorem blk_mul {M : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h1 : M 1 0 = 0) (h2 : M 2 0 = 0)
    (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : blk (M * N) = blk M * blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

theorem blk_mat_mul {g : ↥SL32} (hg : g ∈ P1) (h : ↥SL32) :
    blk (mat (g * h)) = blk (mat g) * blk (mat h) := by
  obtain ⟨h1, h2, -⟩ := (mulVec_e0_iff (mat g)).1 hg
  rw [mat_mul, blk_mul h1 h2]

theorem blk_mat_pow {g : ↥SL32} (hg : g ∈ P1) (n : ℕ) :
    blk (mat (g ^ n)) = blk (mat g) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, mat_one]
    decide
  | succ n ih => rw [pow_succ', pow_succ', blk_mat_mul hg, ih]

theorem blk_pow_eight (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) : B ^ 8 = B ^ 2 := by
  revert B
  decide

theorem eq_one_of_sq_eq_one (B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h1 : B ^ 2 = 1)
    (h2 : (B * !![0, 1; 1, 1] * B * (!![0, 1; 1, 1] * !![0, 1; 1, 1])) ^ 2 = 1) : B = 1 := by
  revert B
  decide

theorem blk_mat_c3 : blk (mat c3) = !![0, 1; 1, 1] := by
  rw [mat_c3]
  decide

theorem c3_inv : c3⁻¹ = c3 * c3 := by
  have h := pow_orderOf_eq_one c3
  rw [orderOf_c3, pow_three] at h
  exact inv_eq_of_mul_eq_one_right h

theorem pow_eight_of_mem_P1 {a : ↥SL32} (ha : a ∈ P1) {m : ℕ} (h : a ^ 2 ^ m = 1) :
    a ^ 8 = 1 := by
  have h1 : orderOf a ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf a ∣ 24 := by
    have := Subgroup.orderOf_dvd_natCard P1 ha
    rwa [card_P1] at this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rw [hj] at h2
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have := (Nat.pow_dvd_pow 2 (by omega : 4 ≤ j)).trans h2
    exact absurd this (by decide)
  rw [← orderOf_dvd_iff_pow_eq_one, hj]
  exact Nat.pow_dvd_pow 2 hj3

theorem mem_Scen_of_comm {a : ↥SL32} (ha : a ∈ P1) (ha8 : a ^ 8 = 1)
    (hc8 : (a * c3 * a⁻¹ * c3⁻¹) ^ 8 = 1) : a ∈ Scen := by
  have hc : c3 ∈ P1 := c3_mem_P1
  have hB2 : blk (mat a) ^ 2 = 1 := by
    rw [← blk_pow_eight, ← blk_mat_pow ha, ha8, mat_one]
    decide
  have hBi : blk (mat a⁻¹) = blk (mat a) := by
    have h1 : blk (mat a⁻¹) * blk (mat a) = 1 := by
      rw [← blk_mat_mul (P1.inv_mem ha), inv_mul_cancel, mat_one]
      decide
    calc blk (mat a⁻¹) = blk (mat a⁻¹) * (blk (mat a) * blk (mat a)) := by
          rw [← sq, hB2, Matrix.mul_one]
      _ = blk (mat a) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hP : a * c3 * a⁻¹ * c3⁻¹ ∈ P1 :=
    P1.mul_mem (P1.mul_mem (P1.mul_mem ha hc) (P1.inv_mem ha)) (P1.inv_mem hc)
  have hq : blk (mat (a * c3 * a⁻¹ * c3⁻¹)) =
      blk (mat a) * !![0, 1; 1, 1] * blk (mat a) * (!![0, 1; 1, 1] * !![0, 1; 1, 1]) := by
    rw [blk_mat_mul (P1.mul_mem (P1.mul_mem ha hc) (P1.inv_mem ha)),
      blk_mat_mul (P1.mul_mem ha hc), blk_mat_mul ha, hBi, c3_inv, blk_mat_mul hc, blk_mat_c3]
  have hq2 := blk_pow_eight (blk (mat (a * c3 * a⁻¹ * c3⁻¹)))
  rw [← blk_mat_pow hP, hc8, mat_one, hq] at hq2
  have hB1 := eq_one_of_sq_eq_one (blk (mat a)) hB2 (hq2.symm.trans (by decide))
  obtain ⟨h10, h20, h00⟩ := (mulVec_e0_iff (mat a)).1 ha
  have e11 : mat a 1 1 = 1 := by simpa using congrFun (congrFun hB1 0) 0
  have e12 : mat a 1 2 = 0 := by simpa using congrFun (congrFun hB1 0) 1
  have e21 : mat a 2 1 = 0 := by simpa using congrFun (congrFun hB1 1) 0
  have e22 : mat a 2 2 = 1 := by simpa using congrFun (congrFun hB1 1) 1
  refine ⟨mat a 0 1, mat a 0 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h00, e11, e12, e21, e22]

theorem mul_E00_mul_transpose (M N : Matrix (Fin 3) (Fin 3) (ZMod 2)) (i j : Fin 3) :
    (M * (Matrix.single 0 0 1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Nᵀ) i j = M i 0 * N j 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]

theorem mem_P1_of_rho_E00 {a b : ↥SL32} (h : rho (a, b) (eW 0 0) = eW 0 0) :
    a ∈ P1 ∧ b ∈ P1 := by
  have h' : mat a * Matrix.single 0 0 1 * (mat b)ᵀ = Matrix.single 0 0 1 :=
    congrArg Multiplicative.toAdd h
  have e : ∀ i j, mat a i 0 * mat b j 0 = Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ZMod 2) i j :=
    fun i j => by rw [← mul_E00_mul_transpose, h']
  have k1 : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide
  obtain ⟨ha0, hb0⟩ := k1 _ _ ((e 0 0).trans (by decide))
  have e10 : mat a 1 0 * mat b 0 0 = 0 := (e 1 0).trans (by decide)
  have e20 : mat a 2 0 * mat b 0 0 = 0 := (e 2 0).trans (by decide)
  have e01 : mat a 0 0 * mat b 1 0 = 0 := (e 0 1).trans (by decide)
  have e02 : mat a 0 0 * mat b 2 0 = 0 := (e 0 2).trans (by decide)
  rw [hb0, mul_one] at e10 e20
  rw [ha0, one_mul] at e01 e02
  exact ⟨(mulVec_e0_iff _).2 ⟨e10, e20, ha0⟩, (mulVec_e0_iff _).2 ⟨e01, e02, hb0⟩⟩

theorem rho_fix_E00 {a b : ↥SL32} (ha : a ∈ P1) (hb : b ∈ P1) : rho (a, b) (eW 0 0) = eW 0 0 := by
  obtain ⟨a1, a2, a0⟩ := (mulVec_e0_iff _).1 ha
  obtain ⟨b1, b2, b0⟩ := (mulVec_e0_iff _).1 hb
  apply Multiplicative.toAdd.injective
  change mat a * Matrix.single 0 0 1 * (mat b)ᵀ = Matrix.single 0 0 1
  ext i j
  rw [mul_E00_mul_transpose]
  fin_cases i <;> fin_cases j <;> simp [a1, a2, a0, b1, b2, b0]

theorem orderOf_c3_one : orderOf ((c3, 1) : ↥SL32 × ↥SL32) = 3 := by
  rw [Prod.orderOf, orderOf_c3, orderOf_one]
  rfl

theorem orderOf_one_c3 : orderOf ((1, c3) : ↥SL32 × ↥SL32) = 3 := by
  rw [Prod.orderOf, orderOf_c3, orderOf_one]
  rfl

theorem le_Shat_of_normalized {K : Subgroup (MulAut WMod)} (hKN : K ≤ norm) (hK2 : IsPGroup 2 K)
    (hKE : ∀ p ∈ K, p (eW 0 0) = eW 0 0)
    (hc : ∀ p ∈ K, rho (c3, 1) * p * (rho (c3, 1))⁻¹ ∈ K)
    (hc' : ∀ p ∈ K, rho (1, c3) * p * (rho (1, c3))⁻¹ ∈ K) : K ≤ Shat := by
  have h2 : ∀ q ∈ K, ∃ n : ℕ, q ^ 2 ^ n = 1 := fun q hq => by
    obtain ⟨n, hn⟩ := hK2 ⟨q, hq⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hcomm : ∀ p ∈ K, ∀ c : MulAut WMod, (∀ p ∈ K, c * p * c⁻¹ ∈ K) →
      p * c * p⁻¹ * c⁻¹ ∈ K := fun p hp c hcK => by
    have := K.mul_mem hp (K.inv_mem (hcK p hp))
    rwa [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, ← mul_assoc] at this
  intro p hp
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.1 (hKN hp)
  · obtain ⟨a, b⟩ := g
    obtain ⟨ha, hb⟩ := mem_P1_of_rho_E00 (hKE _ hp)
    obtain ⟨m, hm⟩ := h2 _ hp
    rw [← map_pow] at hm
    have hm' := rho_injective (hm.trans (map_one rho).symm)
    have ham : a ^ 2 ^ m = 1 := congrArg Prod.fst hm'
    have hbm : b ^ 2 ^ m = 1 := congrArg Prod.snd hm'
    obtain ⟨n, hn⟩ := h2 _ (hcomm _ hp _ hc)
    obtain ⟨n', hn'⟩ := h2 _ (hcomm _ hp _ hc')
    have heq : rho (a, b) * rho (c3, 1) * (rho (a, b))⁻¹ * (rho (c3, 1))⁻¹ =
        rho (a * c3 * a⁻¹ * c3⁻¹, 1) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    have heq' : rho (a, b) * rho (1, c3) * (rho (a, b))⁻¹ * (rho (1, c3))⁻¹ =
        rho (1, b * c3 * b⁻¹ * c3⁻¹) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    rw [heq, ← map_pow] at hn
    rw [heq', ← map_pow] at hn'
    have hq : (a * c3 * a⁻¹ * c3⁻¹) ^ 2 ^ n = 1 :=
      congrArg Prod.fst (rho_injective (hn.trans (map_one rho).symm))
    have hq' : (b * c3 * b⁻¹ * c3⁻¹) ^ 2 ^ n' = 1 :=
      congrArg Prod.snd (rho_injective (hn'.trans (map_one rho).symm))
    have hc3 : c3 ∈ P1 := c3_mem_P1
    have hPa : a * c3 * a⁻¹ * c3⁻¹ ∈ P1 :=
      P1.mul_mem (P1.mul_mem (P1.mul_mem ha hc3) (P1.inv_mem ha)) (P1.inv_mem hc3)
    have hPb : b * c3 * b⁻¹ * c3⁻¹ ∈ P1 :=
      P1.mul_mem (P1.mul_mem (P1.mul_mem hb hc3) (P1.inv_mem hb)) (P1.inv_mem hc3)
    exact rho_mem_Shat
      (mem_Scen_of_comm ha (pow_eight_of_mem_P1 ha ham) (pow_eight_of_mem_P1 hPa hq))
      (mem_Scen_of_comm hb (pow_eight_of_mem_P1 hb hbm) (pow_eight_of_mem_P1 hPb hq'))
  · exfalso
    obtain ⟨n, hn⟩ := h2 _ (hcomm _ hp _ hc)
    have heq : rho g * tau * rho (c3, 1) * (rho g * tau)⁻¹ * (rho (c3, 1))⁻¹ =
        rho (g * (1, c3) * g⁻¹ * (c3, 1)⁻¹) := by
      have h := tau_conj_rho (c3, 1)
      rw [Prod.swap_prod_mk] at h
      calc rho g * tau * rho (c3, 1) * (rho g * tau)⁻¹ * (rho (c3, 1))⁻¹
          = rho g * (tau * rho (c3, 1) * tau⁻¹) * (rho g)⁻¹ * (rho (c3, 1))⁻¹ := by group
        _ = rho (g * (1, c3) * g⁻¹ * (c3, 1)⁻¹) := by
          rw [h, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [heq, ← map_pow] at hn
    have hq := congrArg Prod.fst (rho_injective (hn.trans (map_one rho).symm))
    have h3 : (g.1 * 1 * g.1⁻¹ * c3⁻¹) ^ 2 ^ n = 1 := hq
    rw [mul_one, mul_inv_cancel, one_mul, inv_pow, inv_eq_one] at h3
    have h4 : orderOf c3 ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h3
    rw [orderOf_c3] at h4
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4) (by norm_num)

end L3Wr

end H

end CFSG.Quasithin
