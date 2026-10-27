module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.BigOperators.ZPow
public import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo
public import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import CFSG.LinearAlgebra.IntegralTwoFiniteOrder
import CFSG.LinearAlgebra.IntegralCongruenceTorsionFree
import CFSG.LinearAlgebra.SquareZeroPowers

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open Matrix

variable {r : ℕ}

private def lc {H : Type*} [AddCommGroup H] (v : Fin r → H) : (Fin r → ℤ) →ₗ[ℤ] H where
  toFun y := ∑ j, y j • v j
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.smul_sum, mul_smul]

private theorem lc_single {H : Type*} [AddCommGroup H] (v : Fin r → H) (j : Fin r) :
    lc v (Pi.single j 1) = v j := by
  simp [lc, Pi.single_apply]

private theorem lc_row {H : Type*} [AddCommGroup H] (M : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → H)
    (i : Fin r) : lc v (Mᵀ.mulVecLin (Pi.single i 1)) = ∑ j, M i j • v j := by
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  rfl

private abbrev rowLattice (M : Matrix (Fin r) (Fin r) ℤ) : Submodule ℤ (Fin r → ℤ) :=
  LinearMap.range Mᵀ.mulVecLin

private noncomputable def solEquiv (H : Type*) [AddCommGroup H] (M : Matrix (Fin r) (Fin r) ℤ) :
    {v : Fin r → H // ∀ i, ∑ j, M i j • v j = 0} ≃ ((Fin r → ℤ) ⧸ rowLattice M →ₗ[ℤ] H) where
  toFun v := (rowLattice M).liftQ (lc v.1) (by
    rw [LinearMap.range_le_ker_iff]
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_apply]
    rw [lc_row]; exact v.2 i)
  invFun f := ⟨fun j => f ((rowLattice M).mkQ (Pi.single j 1)), fun i => by
    have h : (rowLattice M).mkQ (Mᵀ.mulVecLin (Pi.single i 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ _)
    have hlc : lc (fun j => f ((rowLattice M).mkQ (Pi.single j 1))) = f ∘ₗ (rowLattice M).mkQ := by
      refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single]
      exact lc_single _ j
    rw [← lc_row, hlc, LinearMap.comp_apply, h, map_zero]⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply]
    exact lc_single _ j
  right_inv f := by
    apply Submodule.linearMap_qext
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, Submodule.liftQ_mkQ]
    exact lc_single _ j

private theorem natCard_quotient_rowLattice {M : Matrix (Fin r) (Fin r) ℤ} (hM : M.det ≠ 0) :
    Nat.card ((Fin r → ℤ) ⧸ rowLattice M) = M.det.natAbs := by
  have hfun : Mᵀ.mulVec = M.vecMul := funext fun x => Matrix.mulVec_transpose (A := M) x
  have hinj : Function.Injective Mᵀ.mulVecLin := by
    simpa [Matrix.coe_vecMulLinear, hfun] using
      (Matrix.mulVec_injective_of_det_ne_zero (R := ℤ) (M := Mᵀ)
        (by rwa [Matrix.det_transpose]))
  rw [← Submodule.natAbs_det_equiv (rowLattice M)
    (LinearEquiv.ofInjective Mᵀ.mulVecLin hinj)]
  have : (rowLattice M).subtype ∘ₗ AddMonoidHom.toIntLinearMap
      ((LinearEquiv.ofInjective Mᵀ.mulVecLin hinj :
        (Fin r → ℤ) →+ rowLattice M)) = Matrix.toLin' Mᵀ := by
    ext x : 1
    rfl
  rw [this, LinearMap.det_toLin', Matrix.det_transpose]

private theorem natCard_powMat_ker (L : Type*) [Field L] [IsAlgClosed L] [CharP L 2]
    (M : Matrix (Fin r) (Fin r) ℤ) (hM : Odd M.det) :
    Nat.card {v : Fin r → Lˣ // ∀ i, ∏ j, v j ^ M i j = 1} = M.det.natAbs := by
  have hM0 : M.det ≠ 0 := fun h => by simp [h] at hM
  set A := (Fin r → ℤ) ⧸ rowLattice M
  have hA : Nat.card A = M.det.natAbs := natCard_quotient_rowLattice hM0
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; exact Int.natAbs_ne_zero.2 hM0)
  have hexp : Odd (Monoid.exponent (Multiplicative A)) := by
    have hd : Monoid.exponent (Multiplicative A) ∣ M.det.natAbs := by
      rw [← hA]; exact Group.exponent_dvd_nat_card
    exact Odd.of_dvd_nat (Int.natAbs_odd.2 hM) hd
  have : NeZero ((Monoid.exponent (Multiplicative A) : ℕ) : L) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    exact fun h => (Nat.not_even_iff_odd.2 hexp) (even_iff_two_dvd.2 h)⟩
  have e1 : {v : Fin r → Lˣ // ∀ i, ∏ j, v j ^ M i j = 1} ≃
      {v : Fin r → Additive Lˣ // ∀ i, ∑ j, M i j • v j = 0} :=
    { toFun v := ⟨fun j => Additive.ofMul (v.1 j), fun i => by
        have := congrArg Additive.ofMul (v.2 i)
        simpa [ofMul_prod, ofMul_zpow] using this⟩
      invFun v := ⟨fun j => Additive.toMul (v.1 j), fun i => by
        have := congrArg Additive.toMul (v.2 i)
        simpa [toMul_sum, toMul_zsmul] using this⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr (e1.trans ((solEquiv (Additive Lˣ) M).trans
    ((addMonoidHomLequivInt (B := Additive Lˣ) ℤ).symm.toEquiv.trans
      AddMonoidHom.toMultiplicativeLeft))),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_congr Multiplicative.toAdd, hA]

private theorem det_smul_sub_one_bound {N : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ} (hk : 0 < k)
    (hN : N ^ k = 1) {a : ℤ} (ha : 1 ≤ |a|) :
    (|a| - 1) ^ 2 ≤ |(a • N - 1).det| := by
  rw [show (a • N - 1 : Matrix (Fin 2) (Fin 2) ℤ) = a • N - (1 : ℤ) • 1 by simp,
    TauCeti.Matrix.det_smul_sub_smul_one_fin_two]
  simp only [mul_one, one_pow]
  rcases CFSG.LinearAlgebra.IntegralTwo.det_trace_of_pow_eq_one hk hN with ⟨hd, ht⟩ | ⟨hd, ht⟩
  · rw [hd]
    have h1 : |a * N.trace| ≤ 2 * |a| := by rw [abs_mul]; nlinarith [abs_nonneg a]
    have h2 : (|a| - 1) ^ 2 ≤ 1 * a ^ 2 - N.trace * a + 1 := by
      have := neg_abs_le (a * N.trace)
      nlinarith [sq_abs a, le_abs_self (a * N.trace)]
    exact h2.trans (le_abs_self _)
  · rw [hd, ht]
    have h : (-1 : ℤ) * a ^ 2 - 0 * a + 1 = -(a ^ 2 - 1) := by ring
    rw [h, abs_neg, ← sq_abs a]
    have : (0 : ℤ) ≤ |a| ^ 2 - 1 := by nlinarith
    rw [abs_of_nonneg this]
    nlinarith

private theorem odd_det_smul_sub_one (N : Matrix (Fin 2) (Fin 2) ℤ) {a : ℤ} (ha : Even a) :
    Odd (a • N - 1).det := by
  rw [show (a • N - 1 : Matrix (Fin 2) (Fin 2) ℤ) = a • N - (1 : ℤ) • 1 by simp,
    TauCeti.Matrix.det_smul_sub_smul_one_fin_two]
  obtain ⟨b, rfl⟩ := ha
  exact ⟨2 * b ^ 2 * N.det - b * N.trace, by ring⟩

private theorem natCard_powMat_ker_two (L : Type*) [Field L] [IsAlgClosed L] [CharP L 2]
    {N : Matrix (Fin 2) (Fin 2) ℤ} {k : ℕ} (hk : 0 < k) (hN : N ^ k = 1) {a : ℤ} (ha : Even a)
    (ha1 : 1 ≤ |a|) :
    Odd (Nat.card {v : Fin 2 → Lˣ // ∀ i, ∏ j, v j ^ (a • N - 1) i j = 1}) ∧
      (|a| - 1) ^ 2 ≤ (Nat.card {v : Fin 2 → Lˣ // ∀ i, ∏ j, v j ^ (a • N - 1) i j = 1} : ℤ) := by
  rw [natCard_powMat_ker L _ (odd_det_smul_sub_one N ha)]
  refine ⟨Int.natAbs_odd.2 (odd_det_smul_sub_one N ha), ?_⟩
  rw [Int.natCast_natAbs]
  exact det_smul_sub_one_bound hk hN ha1

@[expose] def powM {n : ℕ} {G : Type*} [CommGroup G]
    (W : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) : Fin n → G :=
  fun i => ∏ j, a j ^ W i j

section powM

variable {n : ℕ} {G : Type*} [CommGroup G]

theorem powM_mul (W : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n → G) :
    powM W (a * b) = powM W a * powM W b := by
  funext i; simp [powM, mul_zpow, Finset.prod_mul_distrib]

theorem powM_inv (W : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) :
    powM W a⁻¹ = (powM W a)⁻¹ := by
  funext i; simp [powM, Finset.prod_inv_distrib]

private theorem powM_add (A B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) :
    powM (A + B) a = powM A a * powM B a := by
  funext i; simp [powM, zpow_add, Finset.prod_mul_distrib]

private theorem powM_smul (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) (e : ℤ) :
    powM (e • B) a = powM B (a ^ e) := by
  funext i; simp only [powM, Matrix.smul_apply, smul_eq_mul, Pi.pow_apply, ← zpow_mul]

private theorem powM_one (a : Fin n → G) : powM (1 : Matrix (Fin n) (Fin n) ℤ) a = a := by
  funext i
  simp only [powM, Matrix.one_apply]
  rw [Finset.prod_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zpow_zero])
    (by simp)]
  simp

private theorem powM_neg (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) :
    powM (-B) a = (powM B a)⁻¹ := by
  funext i; simp [powM, zpow_neg, Finset.prod_inv_distrib]

private theorem powM_sub_one (B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) :
    powM (B - 1) a = powM B a * a⁻¹ := by
  rw [sub_eq_add_neg, powM_add, powM_neg, powM_one]

private theorem powM_mulMat (A B : Matrix (Fin n) (Fin n) ℤ) (a : Fin n → G) :
    powM B (powM A a) = powM (B * A) a := by
  funext k
  simp only [powM, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

private theorem powM_pow (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (a : Fin n → G) :
    (powM A)^[m] a = powM (A ^ m) a := by
  induction m generalizing a with
  | zero => simp [powM_one]
  | succ m ih => rw [Function.iterate_succ_apply', ih, powM_mulMat, ← pow_succ']

end powM

abbrev rho6 : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 2 4

private def par {G : Type*} [CommGroup G] (v : Fin 2 → G) : Fin 6 → G :=
  ![v 0, 1, v 1, 1, (v 1)⁻¹, (v 0)⁻¹]

private def blk (W : Matrix (Fin 6) (Fin 6) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![W 0 0 - W 0 5, W 0 2 - W 0 4; W 2 0 - W 2 5, W 2 2 - W 2 4]

section Torus

variable {G : Type*} [CommGroup G]

private theorem par_injective : Function.Injective (par : (Fin 2 → G) → Fin 6 → G) := by
  intro v w h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 2

private theorem par_zpow (v : Fin 2 → G) (e : ℤ) : par v ^ e = par (v ^ e) := by
  funext i; fin_cases i <;> simp [par]

private theorem par_anti (v : Fin 2 → G) : (fun i => par v (rho6 i)) = (par v)⁻¹ := by
  funext i
  fin_cases i <;> simp [par, Equiv.swap_apply_of_ne_of_ne]

private theorem anti_iff (h2 : ∀ g : G, g ^ 2 = 1 → g = 1) (a : Fin 6 → G) :
    (fun i => a (rho6 i)) = a⁻¹ ↔ a = par ![a 0, a 2] := by
  constructor
  · intro h
    have h1 := congrFun h 1
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 0
    have r1 : rho6 1 = 1 := by decide
    have r3 : rho6 3 = 3 := by decide
    have r4 : rho6 4 = 2 := by decide
    have r0 : rho6 0 = 5 := by decide
    simp only [Pi.inv_apply, r1, r3, r4, r0] at h1 h3 h4 h5
    have e1 : a 1 = 1 := h2 _ (by rw [sq]; nth_rw 1 [h1]; rw [inv_mul_cancel])
    have e3 : a 3 = 1 := h2 _ (by rw [sq]; nth_rw 1 [h3]; rw [inv_mul_cancel])
    have e4 : a 4 = (a 2)⁻¹ := by rw [h4, inv_inv]
    have e5 : a 5 = (a 0)⁻¹ := h5
    funext i
    fin_cases i <;> simp [par, e1, e3, e4, e5]
  · intro h
    rw [h]; exact par_anti _

private theorem powM_par_coord (W : Matrix (Fin 6) (Fin 6) ℤ) (v : Fin 2 → G) :
    powM W (par v) 0 = powM (blk W) v 0 ∧ powM W (par v) 2 = powM (blk W) v 1 := by
  constructor <;>
  · simp only [powM, Fin.prod_univ_six, Fin.prod_univ_two, par, blk]
    simp only [one_zpow, mul_one, inv_zpow', zpow_sub, zpow_neg, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val, Fin.isValue]
    ac_rfl

private theorem powM_par (h2 : ∀ g : G, g ^ 2 = 1 → g = 1) (W : Matrix (Fin 6) (Fin 6) ℤ)
    (hc : ∀ a : Fin 6 → G, powM W (fun i => a (rho6 i)) = fun i => powM W a (rho6 i))
    (v : Fin 2 → G) : powM W (par v) = par (powM (blk W) v) := by
  have hanti : (fun i => powM W (par v) (rho6 i)) = (powM W (par v))⁻¹ := by
    rw [← hc, par_anti, powM_inv]
  rw [(anti_iff h2 _).1 hanti]
  congr 1
  funext i
  fin_cases i
  · exact (powM_par_coord W v).1
  · exact (powM_par_coord W v).2

end Torus

theorem units_sq_eq_one {L : Type*} [Field L] [CharP L 2] (g : Lˣ) (h : g ^ 2 = 1) : g = 1 := by
  apply Units.ext
  rw [Units.val_one, ← CharTwo.sq_inj, ← Units.val_pow_eq_pow_val, h, Units.val_one]
  norm_num

private theorem eq_one_of_powM_eq (L : Type*) [Field L] [IsAlgClosed L] [CharP L 2] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℤ) (hP : ∀ v : Fin n → Lˣ, powM P v = v) : P = 1 := by
  ext i j
  set d := P i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j
  set m := 2 * d.natAbs + 1
  have hm : Odd m := ⟨d.natAbs, rfl⟩
  have : NeZero ((m : ℕ) : L) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    exact fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  have hu := hζ.isUnit (by omega)
  have hζu : IsPrimitiveRoot hu.unit m := IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)
  have hv := congrFun (hP (Pi.mulSingle j hu.unit)) i
  simp only [powM] at hv
  rw [Finset.prod_eq_single j (fun l _ hl => by rw [Pi.mulSingle_eq_of_ne hl, one_zpow])
    (by simp), Pi.mulSingle_eq_same] at hv
  have hd : hu.unit ^ d = 1 := by
    simp only [d, zpow_sub, hv]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.mulSingle_eq_of_ne hij]
  have hdvd := (hζu.zpow_eq_one_iff_dvd d).1 hd
  have : d = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    by_cases h : c = 0
    · simp [hc, h]
    · exfalso
      have h1 : 1 ≤ |c| := Int.one_le_abs h
      have : (m : ℤ) ≤ |d| := by
        rw [hc, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ m)]; nlinarith
      simp only [m] at this
      push_cast at this
      rw [Int.abs_eq_natAbs] at this
      omega
  omega

theorem natCard_antiFixed (L : Type*) [Field L] [IsAlgClosed L] [CharP L 2]
    (W : Matrix (Fin 6) (Fin 6) ℤ)
    (hc : ∀ a : Fin 6 → Lˣ, powM W (fun i => a (rho6 i)) = fun i => powM W a (rho6 i))
    {k : ℕ} (hk : 0 < k) (hW : W ^ k = 1) {e : ℤ} (he : Even e) (he1 : 1 ≤ |e|) :
    Odd (Nat.card {a : Fin 6 → Lˣ // (fun i => a (rho6 i)) = a⁻¹ ∧ powM W (a ^ e) = a}) ∧
      (|e| - 1) ^ 2 ≤
        (Nat.card {a : Fin 6 → Lˣ // (fun i => a (rho6 i)) = a⁻¹ ∧ powM W (a ^ e) = a} : ℤ) := by
  have h2 := units_sq_eq_one (L := L)
  have hblk : blk W ^ k = 1 := by
    apply eq_one_of_powM_eq L
    intro v
    apply par_injective (G := Lˣ)
    have hit : ∀ m : ℕ, par ((powM (blk W))^[m] v) = (powM W)^[m] (par v) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, powM_par h2 W hc]
    rw [← powM_pow, hit, powM_pow, hW, powM_one]
  have e1 : {a : Fin 6 → Lˣ // (fun i => a (rho6 i)) = a⁻¹ ∧ powM W (a ^ e) = a} ≃
      {v : Fin 2 → Lˣ // ∀ i, ∏ j, v j ^ (e • blk W - 1) i j = 1} :=
    { toFun a := ⟨![a.1 0, a.1 2], by
        have ha := (anti_iff h2 a.1).1 a.2.1
        have hf := a.2.2
        rw [ha, par_zpow, powM_par h2 W hc] at hf
        have hf' := par_injective hf
        intro i
        have := congrFun (show powM (e • blk W - 1) ![a.1 0, a.1 2] = 1 by
          rw [powM_sub_one, powM_smul, hf', mul_inv_cancel]) i
        exact this⟩
      invFun v := ⟨par v.1, par_anti _, by
        rw [par_zpow, powM_par h2 W hc]
        congr 1
        have : powM (e • blk W - 1) v.1 = 1 := funext v.2
        rw [powM_sub_one, powM_smul, mul_inv_eq_one] at this
        exact this⟩
      left_inv a := Subtype.ext ((anti_iff h2 a.1).1 a.2.1).symm
      right_inv v := Subtype.ext (by funext i; fin_cases i <;> rfl) }
  rw [Nat.card_congr e1]
  exact natCard_powMat_ker_two L hk hblk he he1

end CFSG.StandardType.E6GraphNoneSteps
