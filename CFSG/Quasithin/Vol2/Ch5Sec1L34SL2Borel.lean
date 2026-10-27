module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Quasithin.Vol2.Ch10SecATorus
public import CFSG.Quasithin.Vol2.Ch10SecABasic

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL lower_left_eq_zero)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField (Gamma gammaToMulAut
  gammaToMulAut_apply even_SL2_full_automorphism_semilinear_model char_two_of_card)

variable {F : Type} [Field F]

theorem exists_eq_pow_two_pow [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n) (σ : RingAut F) :
    ∃ j : ℕ, ∀ c : F, σ c = c ^ 2 ^ j := by
  have : CharP F 2 := char_two_of_card hcard
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) fun c =>
    DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) F))
      (algebraMap (ZMod 2) F)) c
  obtain ⟨⟨j, hjlt⟩, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F).2 σ'
  refine ⟨j, fun c => ?_⟩
  have h1 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ^ j) c = σ' c :=
    DFunLike.congr_fun hj c
  rw [AlgEquiv.coe_pow,
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod 2) F j) c] at h1
  have h2 : σ' c = σ c := rfl
  rw [h2] at h1
  simpa using h1.symm

theorem iter_two_pow_eq_self {M : Type*} [Monoid M] {x : M} {j : ℕ} (hj : x ^ 2 ^ j = x)
    (a : ℕ) : x ^ 2 ^ (j * a) = x := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hj]

theorem sq_eq_self_of_pow_two_pow {M : Type*} [Monoid M] {x : M} {j e : ℕ}
    (hje : Nat.Coprime j e) (hj : x ^ 2 ^ j = x) (he : x ^ 2 ^ e = x) : x ^ 2 = x := by
  rcases Nat.lt_or_ge 1 e with h1 | h1
  · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hje h1
    have h2 := iter_two_pow_eq_self hj a
    have h3 : j * a = e * (j * a / e) + 1 := by
      have := Nat.div_add_mod (j * a) e
      omega
    have h4 : x ^ 2 ^ (j * a) = (x ^ 2 ^ (e * (j * a / e))) ^ 2 := by
      rw [← pow_mul, ← pow_succ, ← h3]
    rw [h4, iter_two_pow_eq_self he] at h2
    exact h2
  · interval_cases e
    · have : j = 1 := (Nat.coprime_zero_right j).mp hje
      subst this
      simpa using hj
    · simpa using he

theorem pow_two_pow_eq_self_of_even {M : Type*} [Monoid M] {ω : M} (hω : ω ^ 3 = 1) {j : ℕ}
    (hj : Even j) : ω ^ 2 ^ j = ω := by
  obtain ⟨i, rfl⟩ := hj
  have h : 2 ^ (i + i) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  rw [← Nat.div_add_mod (2 ^ (i + i)) 3, h, pow_succ ω (3 * (2 ^ (i + i) / 3)),
    pow_mul ω 3, hω, one_pow, one_mul]

theorem pow_two_pow_eq_sq_of_odd {M : Type*} [Monoid M] {ω : M} (hω : ω ^ 3 = 1) {j : ℕ}
    (hj : Odd j) : ω ^ 2 ^ j = ω ^ 2 := by
  obtain ⟨i, rfl⟩ := hj
  have h : 2 ^ (2 * i + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [← Nat.div_add_mod (2 ^ (2 * i + 1)) 3, h, pow_add ω (3 * (2 ^ (2 * i + 1) / 3)) 2,
    pow_mul ω 3, hω, one_pow, one_mul]

theorem exists_pow_add_one_eq [Finite F] {m : ℕ} (hcard : Nat.card F = 2 ^ (2 * m)) {k : F}
    (hk : k ≠ 0) (hkq : k ^ 2 ^ m = k) : ∃ c : F, c ≠ 0 ∧ c ^ (2 ^ m + 1) = k := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := Finite.one_lt_card (α := F)
      rw [hcard] at this
      norm_num at this
    · exact h0
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 2 := ⟨2 ^ m - 2, by omega⟩
  have : NeZero (2 ^ m - 1) := ⟨by omega⟩
  set N : Fˣ →* Fˣ := powMonoidHom (2 ^ m + 1) with hN
  have hcardU : Nat.card Fˣ = (2 ^ m + 1) * (2 ^ m - 1) := by
    rw [Nat.card_units, hcard, two_mul, pow_add, hr]
    have e : (r + 2) * (r + 2) = (r + 2 + 1) * (r + 2 - 1) + 1 := by
      rw [show r + 2 - 1 = r + 1 by omega]
      ring
    rw [e, Nat.add_sub_cancel]
  have hker : Nat.card N.ker ≤ 2 ^ m + 1 := by
    have hle : N.ker ≤ rootsOfUnity (2 ^ m + 1) F := fun u hu => by
      rw [mem_rootsOfUnity]
      exact hu
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity (k := 2 ^ m + 1) (R := F))
  have hrange : N.range ≤ rootsOfUnity (2 ^ m - 1) F := by
    rintro _ ⟨u, rfl⟩
    rw [mem_rootsOfUnity, hN, powMonoidHom_apply, ← pow_mul, ← hcardU]
    exact pow_card_eq_one'
  have hmul := Subgroup.card_ker_mul_card_range N
  rw [hcardU] at hmul
  have hge : 2 ^ m - 1 ≤ Nat.card N.range := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card N.ker * Nat.card N.range < (2 ^ m + 1) * (2 ^ m - 1) :=
      calc Nat.card N.ker * Nat.card N.range ≤ (2 ^ m + 1) * Nat.card N.range :=
            Nat.mul_le_mul_right _ hker
        _ < (2 ^ m + 1) * (2 ^ m - 1) := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    exact absurd hmul (ne_of_lt h1)
  have heq : N.range = rootsOfUnity (2 ^ m - 1) F :=
    Subgroup.eq_of_le_of_card_ge hrange
      ((card_rootsOfUnity (k := 2 ^ m - 1) (R := F)).trans hge)
  have hkmem : Units.mk0 k hk ∈ rootsOfUnity (2 ^ m - 1) F := by
    rw [mem_rootsOfUnity']
    have h1 : k ^ (2 ^ m - 1) * k = k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hkq]
    simpa using mul_right_cancel₀ hk (h1.trans (one_mul k).symm)
  rw [← heq] at hkmem
  obtain ⟨u, hu⟩ := hkmem
  refine ⟨u, u.ne_zero, ?_⟩
  have := congrArg Units.val hu
  simpa [hN] using this

theorem eq_unipSL_of_upper {x : SL(2, F)} (h10 : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h00 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    x = unipSL ((x : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe x
  rw [Matrix.det_fin_two, h10, h00, mul_zero, sub_zero, one_mul] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, h00, h10, hdet]

theorem upper_mul {x y : SL(2, F)} (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hy : (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((x * y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((x * y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (y : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hx, hy]
  constructor <;> ring

theorem upper_inv {x : SL(2, F)} (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hx]

theorem upper_det {x : SL(2, F)} (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe x
  rw [Matrix.det_fin_two, hx, mul_zero, sub_zero] at hdet
  exact hdet

theorem upper_pow {x : SL(2, F)} (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (k : ℕ) :
    ((x ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((x ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      obtain ⟨h1, h2⟩ := upper_mul ih.1 hx
      rw [pow_succ]
      exact ⟨h1, by rw [h2, ih.2, pow_succ]⟩

theorem upper_conj_map {h x : SL(2, F)} (σ : RingAut F)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((h * Matrix.SpecialLinearGroup.map σ.toRingHom x * h⁻¹ : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((h * Matrix.SpecialLinearGroup.map σ.toRingHom x * h⁻¹ : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 0 0 = σ ((x : Matrix (Fin 2) (Fin 2) F) 0 0) := by
  set y := Matrix.SpecialLinearGroup.map σ.toRingHom x with hy
  have hy10 : (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp [hy, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hx]
  have hy00 : (y : Matrix (Fin 2) (Fin 2) F) 0 0 = σ ((x : Matrix (Fin 2) (Fin 2) F) 0 0) := by
    simp [hy, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  obtain ⟨e1, e2⟩ := upper_mul hh hy10
  obtain ⟨e3, e4⟩ := upper_inv hh
  obtain ⟨e5, e6⟩ := upper_mul e1 e3
  refine ⟨e5, ?_⟩
  rw [e6, e2, e4, hy00]
  have := upper_det hh
  linear_combination (σ ((x : Matrix (Fin 2) (Fin 2) F) 0 0)) * this

theorem exists_upper_ringAut [Finite F] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (α : MulAut SL(2, F)) (hα : ∃ b : F, α (unipSL 1) = unipSL b) :
    ∃ (h : SL(2, F)) (σ : RingAut F), (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (∀ x : SL(2, F), α x = h * Matrix.SpecialLinearGroup.map σ.toRingHom x * h⁻¹) ∧
        ∀ N : ℕ, α ^ N = 1 → σ ^ N = 1 := by
  obtain ⟨hbij, -⟩ := even_SL2_full_automorphism_semilinear_model hn hcard
  obtain ⟨a, rfl⟩ := hbij.2 α
  obtain ⟨b, hb⟩ := hα
  have hmap1 : Matrix.SpecialLinearGroup.map a.right.toRingHom (unipSL (1 : F)) =
      unipSL 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipSL, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  rw [gammaToMulAut_apply, hmap1] at hb
  refine ⟨a.left, a.right, lower_left_eq_zero hb, fun x => gammaToMulAut_apply a x,
    fun N hN => ?_⟩
  have h1 : a ^ N = 1 := hbij.1 (by rw [map_pow, hN, map_one])
  have h2 := congrArg SemidirectProduct.rightHom h1
  rw [map_pow, map_one] at h2
  simpa only [SemidirectProduct.rightHom_eq_right] using h2

theorem eq_one_of_mem_center [CharP F 2] {z : SL(2, F)}
    (hz : z ∈ Subgroup.center SL(2, F)) : z = 1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have : (r - 1) * (r - 1) = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  ext i j
  rw [← hrz, hr1]
  simp

theorem eq_one_of_pow_two_pow_eq_one [CharP F 2] {c : F} {f : ℕ} (hc : c ^ 2 ^ f = 1) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (c - 1) ^ 2 ^ f = 0 := by rw [sub_pow_char_pow, hc, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)

end CFSG.Quasithin.H13
