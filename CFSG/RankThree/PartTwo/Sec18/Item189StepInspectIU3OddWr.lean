module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIU3OddTools
import CFSG.Open.StatedCenterThree
public import CFSG.LieType.Steinberg.CentralExt.UnitaryThreeSylow

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix CFSG.LieType.Steinberg CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ}

theorem entry_of_mul_diagonal_u3odd189 {Y : Matrix (Fin 3) (Fin 3) K} {d d' : Fin 3 → K}
    (h : Y * diagonal d = diagonal d' * Y) (a b : Fin 3) : Y a b * d b = d' a * Y a b := by
  have := congrFun (congrFun h a) b
  rwa [mul_diagonal, diagonal_mul] at this

theorem entry_of_mul_diagonal_swap_u3odd189 {Y : Matrix (Fin 3) (Fin 3) K} {d d' : Fin 3 → K}
    (h : Y * diagonal d = diagonal d' * !![0, 1, 0; 1, 0, 0; 0, 0, -1] * Y) :
    Y 0 0 * d 0 = d' 0 * Y 1 0 ∧ Y 0 1 * d 1 = d' 0 * Y 1 1 ∧
      Y 1 0 * d 0 = d' 1 * Y 0 0 ∧ Y 1 1 * d 1 = d' 1 * Y 0 1 := by
  have e : ∀ a b, (Y * diagonal d) a b =
      (diagonal d' * !![0, 1, 0; 1, 0, 0; 0, 0, -1] * Y : Matrix (Fin 3) (Fin 3) K) a b :=
    fun a b => congrFun (congrFun h a) b
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

theorem eq_one_of_mem_normalizer_wr_u3odd189 (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) {l : Kˣ} (hl4 : 4 ∣ orderOf l)
    {u v τ : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)}
    (hu : (u : GL (Fin 3) K) = diagGL ![l, 1, l⁻¹]) (hv : (v : GL (Fin 3) K) = diagGL ![1, l, l⁻¹])
    (hτ : (τ : GL (Fin 3) K) = swapNegGL)
    (hnf : ∀ w ∈ Subgroup.closure {u, v, τ}, ∃ i j e : ℕ, e < 2 ∧ w = u ^ i * v ^ j * τ ^ e)
    {y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)}
    (hy : y ∈ Subgroup.normalizer (Subgroup.closure ({u, v, τ} :
      Set (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K))) : Set _))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have := hK.finite
  set W := Subgroup.closure ({u, v, τ} : Set (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)))
    with hWdef
  have h2 : (2 : K) ≠ 0 := by
    have : Fact p.Prime := ⟨hK.prime⟩
    have := hK.charP
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).1 h')
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  set s := orderOf l with hs
  have hs0 : 0 < s := orderOf_pos l
  have hs4 : 4 ≤ s := Nat.le_of_dvd hs0 hl4
  obtain ⟨m, hm⟩ : 2 ∣ s := (Nat.dvd_trans (by norm_num) hl4)
  have hl1 : (l : K) ≠ 1 := by
    intro h
    have : l = 1 := Units.ext h
    rw [this, orderOf_one] at hs
    omega
  have hl2 : (l : K) ^ 2 ≠ 1 := by
    intro h
    have : l ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
    omega
  have hlm : (l : K) ^ m = -1 := by
    have hne : l ^ m ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hsq : (l : K) ^ m * (l : K) ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← hm, ← Units.val_pow_eq_pow_val, hs, pow_orderOf_eq_one,
        Units.val_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])) hne
    · exact h
  have hlinv : ((l⁻¹ : Kˣ) : K) = (l : K)⁻¹ := Units.val_inv_eq_inv_val l
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have mat_mul : ∀ g h : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K),
      (((g * h : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((h : GL (Fin 3) K) : Matrix _ _ K) :=
    fun g h => by rw [Subgroup.coe_mul, Units.val_mul]
  have mat_inj : ∀ g h : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((h : GL (Fin 3) K) : Matrix _ _ K) →
        g = h := fun g h e => Subtype.ext (Units.ext e)
  set du : Fin 3 → K := ![(l : K), 1, (l : K)⁻¹] with hdu
  have hU : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal du := by
    rw [hu, coe_diagGL]
    congr 1
    funext k
    fin_cases k <;> simp [hdu, hlinv]
  have hS : ((τ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 1, 0, 0; 0, 0, -1] := by
    rw [hτ, coe_swapNegGL]
  have hdu_inj : Function.Injective du := by
    have hlinv1 : (l : K)⁻¹ ≠ 1 := fun h => hl1 (by rw [← inv_inv (l : K), h, inv_one])
    have hlinvl : (l : K) ≠ (l : K)⁻¹ := by
      intro h
      apply hl2
      calc (l : K) ^ 2 = (l : K) * (l : K)⁻¹ := by rw [sq, ← h]
        _ = 1 := mul_inv_cancel₀ hl0
    exact injective_vec_three_u3odd189 hl1 hlinvl (Ne.symm hlinv1)
  obtain ⟨z, hzdef⟩ : ∃ z, z = u ^ m * v ^ m := ⟨_, rfl⟩
  have hzW : z ∈ W := by
    rw [hzdef]
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)
  have hZ : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
    rw [hzdef, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hu, hv, diagGL_pow_u3odd189,
      diagGL_pow_u3odd189, diagGL_mul_u3odd189, coe_diagGL]
    congr 1
    funext k
    fin_cases k <;> simp [hlm, hlinv, inv_pow]
  have hz_comm : ∀ w ∈ W, z * w = w * z := by
    have hle : W ≤ Subgroup.centralizer {z} := by
      rw [hWdef, Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply mat_inj
      rw [mat_mul, mat_mul, hZ]
      rcases hg with rfl | rfl | rfl
      · rw [hU, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext k
        ring
      · rw [hv, coe_diagGL, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext k
        ring
      · rw [hS]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    exact fun w hw => (Subgroup.mem_centralizer_singleton_iff.1 (hle hw)).symm
  have hyinv : y⁻¹ ∈ Subgroup.normalizer (W : Set _) := inv_mem hy
  have hconj : ∀ w ∈ W, y⁻¹ * w * y ∈ W := fun w hw => by
    have := (Subgroup.mem_normalizer_iff.1 hyinv w).1 hw
    rwa [inv_inv] at this
  have huW : u ∈ W := Subgroup.subset_closure (by simp)
  have hτW : τ ∈ W := Subgroup.subset_closure (by simp)
  have hzz : z * z = 1 := by
    apply mat_inj
    rw [mat_mul, hZ, diagonal_mul_diagonal, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp
  have htz : y * z * y⁻¹ = z := by
    obtain ⟨t, htdef⟩ : ∃ t, t = y * z * y⁻¹ := ⟨_, rfl⟩
    rw [← htdef]
    have ht_comm : ∀ w ∈ W, t * w = w * t := fun w hw => by
      rw [htdef]
      calc y * z * y⁻¹ * w = y * (z * (y⁻¹ * w * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * w * y) * z) * y⁻¹ := by rw [hz_comm _ (hconj w hw)]
        _ = w * (y * z * y⁻¹) := by group
    obtain ⟨T, hTdef⟩ : ∃ T, T = ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
    have hTU : T * diagonal du = diagonal du * T := by
      have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (ht_comm u huW)
      simpa only [mat_mul, hU, ← hTdef] using this
    have hTS : T * !![0, 1, 0; 1, 0, 0; 0, 0, -1] = !![0, 1, 0; 1, 0, 0; 0, 0, -1] * T := by
      have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (ht_comm τ hτW)
      simpa only [mat_mul, hS, ← hTdef] using this
    have hTd := CFSG.Open.StatedCenterThree.eq_diagonal_of_commute hdu_inj hTU
    have hoff : ∀ a b : Fin 3, a ≠ b → T a b = 0 := fun a b hab => by
      rw [hTd, diagonal_apply_ne _ hab]
    have hT01' := hoff 0 1 (by decide)
    have hT02' := hoff 0 2 (by decide)
    have hT10' := hoff 1 0 (by decide)
    have hT12' := hoff 1 2 (by decide)
    have hT20' := hoff 2 0 (by decide)
    have hT21' := hoff 2 1 (by decide)
    have hT01 : T 0 0 = T 1 1 := by
      have h01 := congrFun (congrFun hTS 0) 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three] using h01
    have htt : T * T = 1 := by
      have : t * t = 1 := by
        rw [htdef]
        calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
          _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
      have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) this
      simpa only [mat_mul, ← hTdef, Subgroup.coe_one, Units.val_one] using this
    have hdet : T.det = 1 := by
      rw [hTdef]
      exact det_eq_one_of_mem_SUgram t.2
    have ha : T 0 0 * T 0 0 = 1 := by
      have := congrFun (congrFun htt 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_three, hT01', hT02', hT10', hT20'] using this
    have hc : T 2 2 = 1 := by
      rw [det_fin_three, hT01', hT02', hT10', hT12', hT20', hT21', ← hT01] at hdet
      linear_combination hdet - T 2 2 * ha
    have ha1 : T 0 0 = -1 := by
      rcases mul_self_eq_one_iff.1 ha with h | h
      · exfalso
        have h1 : T = 1 := by
          ext a b
          fin_cases a <;> fin_cases b <;>
            simp [hT01', hT02', hT10', hT12', hT20', hT21', h, ← hT01, hc]
        have ht1 : t = 1 := mat_inj _ _ (by rw [← hTdef, h1, Subgroup.coe_one, Units.val_one])
        have hz1 : z = 1 := by
          have : z = y⁻¹ * t * y := by rw [htdef]; group
          rw [this, ht1, mul_one, inv_mul_cancel]
        have := congrFun (congrFun hZ 0) 0
        rw [hz1, Subgroup.coe_one, Units.val_one] at this
        simp at this
        exact hneg this.symm
      · exact h
    apply mat_inj
    rw [← hTdef, hZ]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hT01', hT02', hT10', hT12', hT20', hT21', ha1, ← hT01, hc]
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hYZ : Y * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * Y := by
    have hyz : y * z = z * y := by
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [htz]
    have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hyz
    simpa only [mat_mul, hZ, ← hYdef] using this
  have hzero : ∀ a b : Fin 3, ![(-1 : K), -1, 1] a ≠ ![(-1 : K), -1, 1] b → Y a b = 0 := by
    intro a b hab
    have := entry_of_mul_diagonal_u3odd189 hYZ a b
    have h0 : Y a b * (![(-1 : K), -1, 1] b - ![(-1 : K), -1, 1] a) = 0 := by
      rw [mul_sub, this]
      ring
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 (Ne.symm hab))
  have hY02 : Y 0 2 = 0 := hzero 0 2 (by simpa using hneg)
  have hY12 : Y 1 2 = 0 := hzero 1 2 (by simpa using hneg)
  have hY20 : Y 2 0 = 0 := hzero 2 0 (by simpa using fun h => hneg h.symm)
  have hY21 : Y 2 1 = 0 := hzero 2 1 (by simpa using fun h => hneg h.symm)
  have hdetY : Y 2 2 * (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) = 1 := by
    have := det_eq_one_of_mem_SUgram y.2
    rw [← hYdef, det_fin_three, hY02, hY12, hY20, hY21] at this
    linear_combination this
  have hY3 : Y * Y * Y = 1 := by
    have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hy3
    simp only [pow_three, mat_mul, Subgroup.coe_one, Units.val_one, ← hYdef] at this
    rw [← this, Matrix.mul_assoc]
  obtain ⟨i, j, e, he, hw⟩ := hnf (y * u * y⁻¹)
    ((Subgroup.mem_normalizer_iff.1 hy u).1 huW)
  set d' : Fin 3 → K := fun k => (((![l, 1, l⁻¹] ^ i * ![1, l, l⁻¹] ^ j) k : Kˣ) : K) with hd'
  have huv : (((u ^ i * v ^ j : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal d' := by
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, hu, hv, diagGL_pow_u3odd189,
      diagGL_pow_u3odd189, diagGL_mul_u3odd189, coe_diagGL]
  have hyu : Y * diagonal du = diagonal d' *
      (((τ ^ e : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * Y := by
    have h1 : y * u = u ^ i * v ^ j * τ ^ e * y := by rw [← hw]; group
    have := congrArg (fun g : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K) =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    rw [mat_mul y u, mat_mul (u ^ i * v ^ j * τ ^ e) y, mat_mul (u ^ i * v ^ j) (τ ^ e), huv, hU,
      ← hYdef] at this
    exact this
  have hYdiag : Y 0 1 = 0 ∧ Y 1 0 = 0 := by
    interval_cases e
    ·
      rw [pow_zero, Subgroup.coe_one, Units.val_one, Matrix.mul_one] at hyu
      have e00 := entry_of_mul_diagonal_u3odd189 hyu 0 0
      have e01 := entry_of_mul_diagonal_u3odd189 hyu 0 1
      have e10 := entry_of_mul_diagonal_u3odd189 hyu 1 0
      have e11 := entry_of_mul_diagonal_u3odd189 hyu 1 1
      simp only [hdu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_one] at e00 e01 e10 e11
      have hl1' : (l : K) - 1 ≠ 0 := sub_ne_zero.2 hl1
      have h0 : Y 0 0 * Y 0 1 = 0 := by
        have : Y 0 0 * Y 0 1 * ((l : K) - 1) = 0 := by
          linear_combination Y 0 1 * e00 - Y 0 0 * e01
        exact (mul_eq_zero.1 this).resolve_right hl1'
      have h1 : Y 1 0 * Y 1 1 = 0 := by
        have : Y 1 0 * Y 1 1 * ((l : K) - 1) = 0 := by
          linear_combination Y 1 1 * e10 - Y 1 0 * e11
        exact (mul_eq_zero.1 this).resolve_right hl1'
      rcases mul_eq_zero.1 h0 with h00 | h01
      ·
        exfalso
        have h11 : Y 1 1 = 0 := by
          rcases mul_eq_zero.1 h1 with h | h
          · rw [h00, h] at hdetY
            simp at hdetY
          · exact h
        have hprod : Y 0 1 * Y 1 0 ≠ 0 := by
          intro h
          rw [h00, h11, h] at hdetY
          simp at hdetY
        have h3 : Y 0 1 * Y 1 0 * Y 0 1 = 0 := by
          have := congrFun (congrFun hY3 0) 1
          simp only [Matrix.mul_apply, Fin.sum_univ_three, h00, h11, hY02, hY12, hY20, hY21,
            mul_zero, zero_mul, add_zero, zero_add] at this
          rw [this, Matrix.one_apply_ne (by decide)]
        exact mul_ne_zero hprod (left_ne_zero_of_mul hprod) h3
      · refine ⟨h01, ?_⟩
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · rw [h01, h] at hdetY
          simp at hdetY
    ·
      exfalso
      rw [pow_one, hS] at hyu
      obtain ⟨e00, e01, e10, e11⟩ := entry_of_mul_diagonal_swap_u3odd189 hyu
      simp only [hdu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        mul_one] at e00 e01 e10 e11
      have hA : Y 0 0 * ((l : K) ^ 2 - d' 0 * d' 1) = 0 := by
        linear_combination (l : K) * e00 + d' 0 * e10
      have hB : Y 0 1 * (1 - d' 0 * d' 1) = 0 := by
        linear_combination e01 + d' 0 * e11
      by_cases h00 : Y 0 0 = 0
      · have h10 : Y 1 0 = 0 := by
          rw [h00, mul_zero] at e10
          exact (mul_eq_zero.1 e10).resolve_right hl0
        rw [h00, h10] at hdetY
        simp at hdetY
      · by_cases h01 : Y 0 1 = 0
        · have h11 : Y 1 1 = 0 := by
            rw [h01, mul_zero] at e11
            exact e11
          rw [h01, h11] at hdetY
          simp at hdetY
        · have hA' := (mul_eq_zero.1 hA).resolve_left h00
          have hB' := (mul_eq_zero.1 hB).resolve_left h01
          exact hl2 (by linear_combination hA' - hB')
  obtain ⟨hY01, hY10⟩ := hYdiag
  have hYd : Y = diagonal fun k => Y k k := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hY01, hY10, hY02, hY12, hY20, hY21]
  have hunit : ∀ k, hK.bar (Y k k) * Y k k = 1 := by
    intro k
    have h := y.2.2
    rw [Matrix.mul_one, ← hYdef, hYd, ctr_diagonal, diagonal_mul_diagonal] at h
    have := congrFun (congrFun h k) k
    simpa using this
  have hcube : ∀ k, Y k k ^ 3 = 1 := by
    intro k
    have := congrFun (congrFun hY3 k) k
    rw [hYd, diagonal_mul_diagonal, diagonal_mul_diagonal] at this
    simpa [pow_three, mul_assoc] using this
  have hone : ∀ k, Y k k = 1 := fun k =>
    eq_one_of_pow_three_u3odd189 hq3 (hcube k) (by rw [← hK.bar_apply]; exact hunit k)
  apply mat_inj
  rw [← hYdef, hYd, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext k
  exact hone k

theorem eq_one_of_mem_normalizer_sylow_wr_u3odd189 (hK : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) (hq4 : p ^ f % 4 = 3)
    (T : Sylow 2 (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)))
    {y : SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K)}
    (hy : y ∈ Subgroup.normalizer
      ((T : Subgroup (SUgram hK.bar (1 : Matrix (Fin 3) (Fin 3) K))) : Set _))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have := hK.finite
  have hG : ∀ i j, hK.bar ((1 : Matrix (Fin 3) (Fin 3) K) j i) =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), map_zero]
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by simp
  obtain ⟨-, -, -, -, h5, -⟩ :=
    odd_unitary_three_exact_coordinate_and_Sylow_models hK hp2 hG hdet ⊥ bot_le
  obtain ⟨⟨l, hl, hlo⟩, hm⟩ := h5 hq4
  have hP : ctr hK.bar ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * 1 *
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    simp [ctr_one]
  obtain ⟨u, v, τ, hu, hv, hτ, -, -, -, -, -, -, -, -, hnf, -, hWcard, -⟩ := hm 1 hP l hl hlo
  rw [one_mul, inv_one, mul_one] at hu hv hτ
  have hl4 : 4 ∣ orderOf l := by
    rw [hlo]
    have h4 : 2 ^ 2 ∣ p ^ f + 1 := by omega
    exact pow_dvd_pow 2 ((Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).1 h4)
  refine eq_one_of_sylow_u3odd189 hWcard (fun y hy hy3 => ?_) T hy hy3
  exact eq_one_of_mem_normalizer_wr_u3odd189 hK hp2 hq3 hl4 hu hv hτ
    (fun w hw => by
      obtain ⟨i, j, e, -, -, he, h⟩ := hnf w hw
      exact ⟨i, j, e, he, h⟩) hy hy3

end CFSG.RankThree.PartTwo.Sec18
