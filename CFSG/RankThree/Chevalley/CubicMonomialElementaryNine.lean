module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG

theorem exists_pow_eq_of_mem_zpowers_of_pow_three {G : Type*} [Group G] {x u : G}
    (hx : x ^ 3 = 1) (hu : u ∈ Subgroup.zpowers x) : ∃ i : ℕ, i < 3 ∧ x ^ i = u := by
  classical
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (hfin.mem_zpowers_iff_mem_range_orderOf.1 hu)
  exact ⟨i, lt_of_lt_of_le (Finset.mem_range.1 hi) (orderOf_le_of_pow_eq_one (by norm_num) hx),
    rfl⟩

theorem exists_isElementaryAbelian_nine_of_pair {G : Type*} [Group G] {x y : G}
    (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hinj : ∀ i j : ℕ, i < 3 → j < 3 → x ^ i * y ^ j = 1 → i = 0 ∧ j = 0) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := fun h => by
    have := (hinj 1 0 (by norm_num) (by norm_num) (by rw [h]; simp)).1
    omega
  have hy1 : y ≠ 1 := fun h => by
    have := (hinj 0 1 (by norm_num) (by norm_num) (by rw [h]; simp)).2
    omega
  have hox : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy hy1
  have hc : Commute x y := hxy
  let X := Subgroup.zpowers x
  let Y := Subgroup.zpowers y
  have hXY : ∀ (u : X) (v : Y), Commute (X.subtype u) (Y.subtype v) := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact hc.zpow_zpow m n
  let f : X × Y →* G := MonoidHom.noncommCoprod X.subtype Y.subtype hXY
  have hf : ∀ p : X × Y, f p = (p.1 : G) * p.2 := fun p => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ h
    rw [hf] at h
    obtain ⟨i, hi, rfl⟩ := exists_pow_eq_of_mem_zpowers_of_pow_three hx hu
    obtain ⟨j, hj, rfl⟩ := exists_pow_eq_of_mem_zpowers_of_pow_three hy hv
    obtain ⟨rfl, rfl⟩ := hinj i j hi hj h
    exact Prod.ext (Subtype.ext (pow_zero x)) (Subtype.ext (pow_zero y))
  have hcommXY : ∀ p q : X × Y, p * q = q * p := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
    obtain ⟨n', rfl⟩ := Subgroup.mem_zpowers_iff.1 hv'
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (Commute.zpow_zpow_self x m m').eq
    · exact (Commute.zpow_zpow_self y n n').eq
  have hpowXY : ∀ p : X × Y, p ^ 3 = 1 := by
    rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨i, -, rfl⟩ := exists_pow_eq_of_mem_zpowers_of_pow_three hx hu
    obtain ⟨j, -, rfl⟩ := exists_pow_eq_of_mem_zpowers_of_pow_three hy hv
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (x ^ i) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
    · change (y ^ j) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  refine ⟨f.range, { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }, ?_⟩
  · obtain ⟨p, hp⟩ := a.2
    obtain ⟨q, hq⟩ := b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hp, ← hq, ← map_mul, ← map_mul, hcommXY]
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_
    obtain ⟨p, hp⟩ := a.2
    rw [Subgroup.coe_pow, ← hp, ← map_pow, hpowXY, map_one, Subgroup.coe_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hox, hoy]

theorem normal_of_forall_scalar {K : Type*} [Field K] {H : Subgroup (GL (Fin 3) K)}
    {C : Subgroup H}
    (hC : ∀ x ∈ C, ∃ r : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) r) : C.Normal :=
  Subgroup.normal_of_le_center fun x hx => Subgroup.mem_center_iff.2 fun g => by
    obtain ⟨r, hr⟩ := hC x hx
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hr]
    exact ((Matrix.scalar_commute r (fun r' => Commute.all r r') _).eq).symm

theorem diag_eq_of_scalar {K : Type*} [Field K] {d : Fin 3 → K} {r : K}
    (h : Matrix.diagonal d = Matrix.scalar (Fin 3) r) : d 0 = d 1 ∧ d 0 = d 2 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 1
  have h2 := congrFun (congrFun h 2) 2
  simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h0 h1 h2
  exact ⟨h0.trans h1.symm, h0.trans h2.symm⟩

theorem cubic_monomial_scalar_quotient_has_elementary_nine {K : Type*} [Field K] {ζ : Kˣ}
    (hζ : orderOf ζ = 3) (H : Subgroup (GL (Fin 3) K)) {a b c : GL (Fin 3) K}
    (ha : (a : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1])
    (hb : (b : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![1, (ζ : K), ((ζ⁻¹ : Kˣ) : K)])
    (hc : (c : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0])
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H) (C : Subgroup H)
    (hC : ∀ x ∈ C, ∃ r : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) r) :
    letI : C.Normal := normal_of_forall_scalar hC
    ∃ E : Subgroup (H ⧸ C), IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  have : C.Normal := normal_of_forall_scalar hC
  set z : K := (ζ : K) with hzdef
  have hoz : orderOf z = 3 := by rw [hzdef, orderOf_units, hζ]
  have hz3 : z ^ 3 = 1 := by rw [← hoz]; exact pow_orderOf_eq_one z
  have hzinv : ((ζ⁻¹ : Kˣ) : K) = z ^ 2 := by
    have h1 : (ζ : K) * ((ζ⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((ζ⁻¹ : Kˣ) : K) = z ^ 3 * ((ζ⁻¹ : Kˣ) : K) := by rw [hz3, one_mul]
      _ = z ^ 2 * (z * ((ζ⁻¹ : Kˣ) : K)) := by ring
      _ = z ^ 2 := by rw [hzdef, h1, mul_one]
  have hmod : ∀ m n : ℕ, z ^ m = z ^ n → m % 3 = n % 3 := fun m n h => by
    have h' : ζ ^ m = ζ ^ n := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact h)
    have := (pow_eq_pow_iff_modEq).1 h'
    rw [hζ] at this
    exact this
  set A : H := ⟨a, haH⟩
  set B : H := ⟨b, hbH⟩
  set Cc : H := ⟨c, hcH⟩
  have hAB : ∀ i j : ℕ, (((A ^ i * B ^ j : H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![z ^ i, z ^ (2 * i + j), z ^ (2 * j)] := by
    intro i j
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, A, B,
      ha, hb, hzinv, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k
    fin_cases k <;> simp [pow_add, pow_mul]
  have hdiag1 : Matrix.diagonal ![(1 : K), 1, 1] = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hz6 : z ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, hz3, one_pow]
  have hA3 : A ^ 3 = 1 := by
    have h := hAB 3 0
    rw [pow_zero, mul_one] at h
    refine Subtype.ext (Units.ext ?_)
    rw [h, Subgroup.coe_one, Units.val_one]
    simpa [hz3, hz6] using hdiag1
  have hB3 : B ^ 3 = 1 := by
    have h := hAB 0 3
    rw [pow_zero, one_mul] at h
    refine Subtype.ext (Units.ext ?_)
    rw [h, Subgroup.coe_one, Units.val_one]
    simpa [hz3, hz6] using hdiag1
  have hABc : A * B = B * A := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, A, B, ha, hb, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  have hscalar : ∀ g : H, g ∈ C → ∀ d : Fin 3 → K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d → d 0 = d 1 ∧ d 0 = d 2 :=
    fun g hg d hd => by
      obtain ⟨r, hr⟩ := hC g hg
      exact diag_eq_of_scalar (hd.symm.trans hr)
  by_cases hA : A * B ^ 2 ∈ C
  ·
    have hz4 : z ^ 4 = z := by rw [pow_succ, hz3, one_mul]
    have hAB2 : (((A * B ^ 2 : H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) z := by
      have h := hAB 1 2
      rw [pow_one] at h
      rw [h, Matrix.scalar_apply]
      congr 1
      funext k
      fin_cases k <;> simp [hz4]
    have hBj : ∀ j : ℕ, (((B ^ j : H) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal ![1, z ^ j, z ^ (2 * j)] := fun j => by
      have h := hAB 0 j
      rw [pow_zero, one_mul] at h
      rw [h]
      congr 1
      funext k
      fin_cases k <;> simp
    have hcc : ((Cc : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
      hc
    let φ : H →* Matrix (Fin 3) (Fin 3) K := (Units.coeHom _).comp H.subtype
    have hφ : ∀ g : H, φ g = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun g => rfl
    have hφinj : ∀ g g' : H, φ g = φ g' → g = g' := fun g g' h =>
      Subtype.ext (Units.ext h)
    have hcb : Cc * B = (A * B ^ 2) ^ 2 * B * Cc := by
      refine hφinj _ _ ?_
      have hB1 := hBj 1
      rw [pow_one] at hB1
      rw [map_mul, map_mul, map_mul, map_pow, hφ, hφ, hφ, hcc, hB1, hAB2]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, sq]
      · linear_combination (-1 : K) * hz3
      · linear_combination (-1 : K) * hz4
    have hc3 : Cc ^ 3 = 1 := by
      refine hφinj _ _ ?_
      rw [map_pow, map_one, hφ, hcc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    refine exists_isElementaryAbelian_nine_of_pair (x := QuotientGroup.mk' C Cc)
      (y := QuotientGroup.mk' C B) ?_ (by rw [← map_pow, hc3, map_one])
      (by rw [← map_pow, hB3, map_one]) fun i j hi hj h => ?_
    · have h1 : QuotientGroup.mk' C ((A * B ^ 2) ^ 2) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (pow_mem hA 2)
      calc QuotientGroup.mk' C Cc * QuotientGroup.mk' C B = QuotientGroup.mk' C (Cc * B) :=
            (map_mul _ _ _).symm
        _ = QuotientGroup.mk' C B * QuotientGroup.mk' C Cc := by
          rw [hcb, map_mul, map_mul, h1, one_mul]
    · rw [← map_pow, ← map_pow, ← map_mul, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at h
      obtain ⟨r, hr⟩ := hC _ h
      rw [← hφ, map_mul, map_pow, hφ, hφ, hBj j, hcc] at hr
      interval_cases i
      · rw [pow_zero, one_mul] at hr
        obtain ⟨h1, -⟩ := diag_eq_of_scalar hr
        have := hmod 0 j (by simpa using h1)
        omega
      · exfalso
        have h10 := congrFun (congrFun hr 1) 0
        rw [pow_one, Matrix.mul_diagonal] at h10
        simp [Matrix.scalar_apply] at h10
      · exfalso
        have h20 := congrFun (congrFun hr 2) 0
        rw [Matrix.mul_diagonal] at h20
        simp [Matrix.scalar_apply, sq, Matrix.mul_apply, Fin.sum_univ_three] at h20
  ·
    refine exists_isElementaryAbelian_nine_of_pair (x := QuotientGroup.mk' C A)
      (y := QuotientGroup.mk' C B) (by rw [← map_mul, ← map_mul, hABc])
      (by rw [← map_pow, hA3, map_one]) (by rw [← map_pow, hB3, map_one]) fun i j hi hj h => ?_
    rw [← map_pow, ← map_pow, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h
    obtain ⟨h1, h2⟩ := hscalar _ h _ (hAB i j)
    have e1 := hmod _ _ h1
    have e2 := hmod _ _ h2
    have hcases : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by omega
    rcases hcases with hc0 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc0
    · exact (hA (by simpa using h)).elim
    · exfalso
      apply hA
      have hsq : (A ^ 2 * B ^ 1) ^ 2 = A * B ^ 2 := by
        have hcomm : Commute (A ^ 2) B := (Commute.pow_left hABc 2)
        rw [pow_one, hcomm.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hA3, one_mul,
          pow_one]
      rw [← hsq]
      exact pow_mem h 2

end CFSG.RankThree.Chevalley
