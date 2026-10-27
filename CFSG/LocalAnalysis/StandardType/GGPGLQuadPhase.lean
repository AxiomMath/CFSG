module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

theorem diagonal_mul_eq_mul_diagonal_of_shift {e : ι → ZMod p} {m : ZMod p} {X : Matrix ι ι K}
    (hX : ∀ i j, X i j ≠ 0 → e i = e j + m) (c : ZMod p → K) :
    diagonal (fun i => c (e i)) * X = X * diagonal (fun j => c (e j + m)) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : X i j = 0
  · simp [h]
  · rw [hX i j h]
    ring

theorem pow_val_add_of_pow_eq_one [NeZero p] {M : Type*} [Monoid M] {ζ : M} (hζ : ζ ^ p = 1)
    (a b : ZMod p) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem exists_zmod_pow_eq [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x : K}
    (hx : x ^ p = 1) : ∃ a : ZMod p, ζ ^ a.val = x := by
  obtain ⟨i, hi, hix⟩ := hζ.eq_pow_of_pow_eq_one hx
  exact ⟨i, by rwa [ZMod.val_natCast_of_lt hi]⟩

theorem shift_of_mul_eq [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {e : ι → ZMod p}
    {m : ZMod p} {X : Matrix ι ι K}
    (hX : diagonal (fun i => ζ ^ (e i).val) * X =
      ζ ^ m.val • (X * diagonal (fun i => ζ ^ (e i).val))) :
    ∀ i j, X i j ≠ 0 → e i = e j + m := by
  intro i j hij
  have h := congrFun (congrFun hX i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at h
  have h' : ζ ^ (e i).val * X i j = (ζ ^ m.val * ζ ^ (e j).val) * X i j := by
    rw [h]
    ring
  have h3 : ζ ^ (e i).val = ζ ^ m.val * ζ ^ (e j).val :=
    mul_right_cancel₀ hij h'
  have h4 : ζ ^ (e i).val = ζ ^ (e j + m).val := by
    rw [h3, add_comm (e j) m, ← pow_val_add_of_pow_eq_one hζ.pow_eq_one m (e j)]
  have h5 : (e i).val = (e j + m).val :=
    hζ.pow_inj (ZMod.val_lt (e i)) (ZMod.val_lt (e j + m)) h4
  exact ZMod.val_injective p h5

theorem sum_add_eq_sum_of_shift [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {e : ι → ZMod p}
    {m : ZMod p} {X : GL ι K} (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m)
    (F : ZMod p → ZMod p) : ∑ i, F (e i + m) = ∑ i, F (e i) := by
  have hprod : ∀ a : ι → ZMod p, ∏ i, ζ ^ (a i).val = ζ ^ (∑ i, a i).val := by
    intro a
    have hgen : ∀ s : Finset ι,
        ∏ i ∈ s, ζ ^ (a i).val = ζ ^ (∑ i ∈ s, a i).val := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
          rw [Finset.prod_insert hi, ih, Finset.sum_insert hi,
            ← pow_val_add_of_pow_eq_one hζ.pow_eq_one]
    simpa using hgen Finset.univ
  have hY := diagonal_mul_eq_mul_diagonal_of_shift (X := (X : Matrix ι ι K)) hX
    (fun a : ZMod p => ζ ^ (F a).val)
  have hdet : (∏ i, ζ ^ (F (e i)).val) = (∏ i, ζ ^ (F (e i + m)).val) := by
    have h := congrArg Matrix.det hY
    simp only [Matrix.det_mul, Matrix.det_diagonal] at h
    exact mul_right_cancel₀ X.det.ne_zero (h.trans (mul_comm _ _))
  have hvaleq : (∑ i, F (e i)).val = (∑ i, F (e i + m)).val := by
    refine hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_
    rw [← hprod (fun i => F (e i)), ← hprod (fun i => F (e i + m))]
    exact hdet
  exact (ZMod.val_injective p hvaleq).symm

theorem sum_eq_zero_of_shift [Fact p.Prime] (hp2 : p ≠ 2) (hpι : p ∣ Fintype.card ι) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {e : ι → ZMod p} {m : ZMod p} (hm : m ≠ 0) {X : GL ι K}
    (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m) : ∑ i, e i = 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hshift := sum_add_eq_sum_of_shift hζ hX (fun a : ZMod p => a ^ 2)
  have hexp : ∑ i, (e i + m) ^ 2 = ∑ i, e i ^ 2 + ∑ i, (2 * m * e i + m ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hzero : ∑ i, (2 * m * e i + m ^ 2) = 0 := by
    have h : ∑ i, e i ^ 2 + ∑ i, (2 * m * e i + m ^ 2) = ∑ i, e i ^ 2 := by
      rw [← hexp]
      exact hshift
    have h' : ∑ i, e i ^ 2 + ∑ i, (2 * m * e i + m ^ 2) = ∑ i, e i ^ 2 + 0 := by
      simpa using h
    exact add_left_cancel h'
  have hsplit : ∑ i, (2 * m * e i + m ^ 2)
      = 2 * m * (∑ i, e i) + (Fintype.card ι : ZMod p) * m ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hcard : (Fintype.card ι : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpι
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hp' : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
    exact hp2 hp'
  have hmain : 2 * m * (∑ i, e i) = 0 := by
    have h := hzero
    rw [hsplit, hcard, zero_mul, add_zero] at h
    exact h
  exact (mul_eq_zero.mp hmain).resolve_left (mul_ne_zero h2 hm)

theorem sum_sq_eq_zero_of_shift [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpι : p ∣ Fintype.card ι) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {e : ι → ZMod p} {m : ZMod p}
    (hm : m ≠ 0) {X : GL ι K} (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m) :
    ∑ i, e i ^ 2 = 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hshift := sum_add_eq_sum_of_shift hζ hX (fun a : ZMod p => a ^ 3)
  have hexp : ∑ i, (e i + m) ^ 3
      = ∑ i, e i ^ 3 + ∑ i, (3 * m * e i ^ 2 + 3 * m ^ 2 * e i + m ^ 3) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hzero : ∑ i, (3 * m * e i ^ 2 + 3 * m ^ 2 * e i + m ^ 3) = 0 := by
    have h : ∑ i, e i ^ 3 + ∑ i, (3 * m * e i ^ 2 + 3 * m ^ 2 * e i + m ^ 3)
        = ∑ i, e i ^ 3 := by
      rw [← hexp]
      exact hshift
    have h' : ∑ i, e i ^ 3 + ∑ i, (3 * m * e i ^ 2 + 3 * m ^ 2 * e i + m ^ 3)
        = ∑ i, e i ^ 3 + 0 := by
      simpa using h
    exact add_left_cancel h'
  have hsum1 : ∑ i, e i = 0 := sum_eq_zero_of_shift hp2 hpι hζ hm hX
  have hsplit : ∑ i, (3 * m * e i ^ 2 + 3 * m ^ 2 * e i + m ^ 3)
      = 3 * m * (∑ i, e i ^ 2) + 3 * m ^ 2 * (∑ i, e i)
        + (Fintype.card ι : ZMod p) * m ^ 3 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card ι : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hpι
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hp' : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hdvd
    exact hp3 hp'
  have hmain : 3 * m * (∑ i, e i ^ 2) = 0 := by
    have h := hzero
    rw [hsplit, hsum1, hcard] at h
    simpa using h
  exact (mul_eq_zero.mp hmain).resolve_left (mul_ne_zero h3 hm)

@[expose] def quadExp (a : ZMod p) : ZMod p := (2 : ZMod p)⁻¹ * (a ^ 2 - a)

theorem quadExp_add [Fact p.Prime] (hp2 : p ≠ 2) (a b : ZMod p) :
    quadExp (a + b) = quadExp a + quadExp b + b * a := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
  simp only [quadExp]
  field_simp [h2]
  ring

theorem exists_conj_diagonal_exponents [NeZero p] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {h : GL ι K} (hh : h ^ p = 1) :
    ∃ (A₀ : GL ι K) (e : ι → ZMod p),
      ((A₀ * h * A₀⁻¹ : GL ι K) : Matrix ι ι K) = diagonal fun i => (ζ : K) ^ (e i).val := by
  classical
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal (ζ := (ζ : K)) hζK ({h} : Set (GL ι K))
    (by
      intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy])
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hh)
  let H : GL ι K := MulAut.conj A₀ h
  have hconjMat : ∀ x : GL ι K,
      ((MulAut.conj A₀ x : GL ι K) : Matrix ι ι K)
        = (A₀ : Matrix ι ι K) * (x : Matrix ι ι K) *
            ((A₀⁻¹ : GL ι K) : Matrix ι ι K) := by
    intro x
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
  let t : ι → K := fun i => (H : Matrix ι ι K) i i
  have hHdiag : (H : Matrix ι ι K) = diagonal t := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [t]
    · rw [diagonal_apply_ne _ hij, hconjMat]
      exact hA₀ h (Set.mem_singleton h) i j hij
  have ht_pow : ∀ i, t i ^ p = 1 := by
    intro i
    have hHp : H ^ p = 1 := by
      change MulAut.conj A₀ h ^ p = 1
      rw [← map_pow, hh, map_one]
    have h1 : (H : Matrix ι ι K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hHp, Units.val_one]
    rw [hHdiag, Matrix.diagonal_pow] at h1
    have := congrFun (congrFun h1 i) i
    simpa [t] using this
  choose e he using fun i => exists_zmod_pow_eq (ζ := (ζ : K)) hζK (ht_pow i)
  have hH_eq : H = A₀ * h * A₀⁻¹ := by
    change MulAut.conj A₀ h = A₀ * h * A₀⁻¹
    rw [MulAut.conj_apply]
  refine ⟨A₀, e, ?_⟩
  rw [← hH_eq, hHdiag]
  congr 1
  funext i
  exact (he i).symm

theorem exists_shift_of_partner [NeZero p] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {h g A₀ : GL ι K} {e : ι → ZMod p}
    (hdiag : ((A₀ * h * A₀⁻¹ : GL ι K) : Matrix ι ι K)
      = diagonal fun i => (ζ : K) ^ (e i).val)
    {u₀ : Kˣ} (hu₀ : u₀ ≠ 1) (hu₀p : u₀ ^ p = 1)
    (hhg : h * g = GeneralLinearGroup.scalar ι u₀ * (g * h)) :
    ∃ m₀ : ZMod p, m₀ ≠ 0 ∧
      ∀ i j, ((A₀ * g * A₀⁻¹ : GL ι K) : Matrix ι ι K) i j ≠ 0 → e i = e j + m₀ := by
  classical
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let H : GL ι K := MulAut.conj A₀ h
  let G : GL ι K := MulAut.conj A₀ g
  have hconjMat : ∀ x : GL ι K,
      ((MulAut.conj A₀ x : GL ι K) : Matrix ι ι K)
        = (A₀ : Matrix ι ι K) * (x : Matrix ι ι K) *
            ((A₀⁻¹ : GL ι K) : Matrix ι ι K) := by
    intro x
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
  have hscalar_conj : ∀ (A : GL ι K) (u : Kˣ),
      MulAut.conj A (GeneralLinearGroup.scalar ι u) = GeneralLinearGroup.scalar ι u := by
    intro A u
    rw [MulAut.conj_apply, ← GeneralLinearGroup.scalar_commute u A, mul_assoc,
      mul_inv_cancel, mul_one]
  have hcondU : H * G = GeneralLinearGroup.scalar ι u₀ * (G * H) := by
    change MulAut.conj A₀ h * MulAut.conj A₀ g = _
    calc MulAut.conj A₀ h * MulAut.conj A₀ g
        = MulAut.conj A₀ (h * g) := (map_mul _ _ _).symm
      _ = MulAut.conj A₀ (GeneralLinearGroup.scalar ι u₀ * (g * h)) := by rw [hhg]
      _ = MulAut.conj A₀ (GeneralLinearGroup.scalar ι u₀) *
            MulAut.conj A₀ (g * h) := map_mul _ _ _
      _ = GeneralLinearGroup.scalar ι u₀ *
            (MulAut.conj A₀ g * MulAut.conj A₀ h) := by
          rw [hscalar_conj A₀, map_mul]
      _ = GeneralLinearGroup.scalar ι u₀ * (G * H) := rfl
  have hcond : (H : Matrix ι ι K) * (G : Matrix ι ι K)
      = (u₀ : K) • ((G : Matrix ι ι K) * (H : Matrix ι ι K)) := by
    have h := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hcondU
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h
    rwa [← smul_eq_diagonal_mul] at h
  have hH_eq : H = A₀ * h * A₀⁻¹ := by
    change MulAut.conj A₀ h = A₀ * h * A₀⁻¹
    rw [MulAut.conj_apply]
  have hHdiag : (H : Matrix ι ι K) = diagonal (fun i => (ζ : K) ^ (e i).val) := by
    rw [hH_eq]
    exact hdiag
  have hu₀val : (u₀ : K) ^ p = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hu₀p
  obtain ⟨m₀, hm₀⟩ := exists_zmod_pow_eq (ζ := (ζ : K)) hζK hu₀val
  have hm₀ne : m₀ ≠ 0 := by
    intro h0
    apply hu₀
    apply Units.ext
    rw [← hm₀, h0, ZMod.val_zero, pow_zero, Units.val_one]
  have hshiftG : diagonal (fun i => (ζ : K) ^ (e i).val) * (G : Matrix ι ι K)
      = (ζ : K) ^ m₀.val •
          ((G : Matrix ι ι K) * diagonal (fun i => (ζ : K) ^ (e i).val)) := by
    rw [hHdiag, ← hm₀] at hcond
    exact hcond
  have hXg : ∀ i j, (G : Matrix ι ι K) i j ≠ 0 → e i = e j + m₀ :=
    shift_of_mul_eq hζK hshiftG
  refine ⟨m₀, hm₀ne, ?_⟩
  intro i j hij
  exact hXg i j (by simpa [G, MulAut.conj_apply] using hij)

theorem quadPhase_spec [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {h A₀ : GL ι K} {e : ι → ZMod p}
    (hdiag : ((A₀ * h * A₀⁻¹ : GL ι K) : Matrix ι ι K)
      = diagonal fun i => (ζ : K) ^ (e i).val) :
    ∃ Δ : GL ι K, (Δ : Matrix ι ι K) = diagonal (fun i => (ζ : K) ^ (quadExp (e i)).val) ∧
      ((A₀⁻¹ * Δ * A₀ : GL ι K) : Matrix ι ι K).det =
        (ζ : K) ^ (∑ i, quadExp (e i)).val ∧
      ∀ (x : GL ι K) (m : ℕ), h * x = GeneralLinearGroup.scalar ι (ζ ^ m) * (x * h) →
        ∃ c : Kˣ, (A₀⁻¹ * Δ * A₀) * x * (A₀⁻¹ * Δ * A₀)⁻¹ =
          GeneralLinearGroup.scalar ι c * (x * h ^ m) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let d : ι → K := fun i => (ζ : K) ^ (quadExp (e i)).val
  have hd_ne : ∀ i, d i ≠ 0 := by
    intro i
    exact pow_ne_zero _ (hζK.ne_zero (Fact.out : p.Prime).ne_zero)
  let Δ : GL ι K :=
    ⟨diagonal d, diagonal (fun i => (d i)⁻¹), by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij], by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]⟩
  have hΔcoe : (Δ : Matrix ι ι K) = diagonal d := rfl
  have hprod_d : ∏ i, d i = (ζ : K) ^ (∑ i, quadExp (e i)).val := by
    have hgen : ∀ s : Finset ι,
        ∏ i ∈ s, (ζ : K) ^ (quadExp (e i)).val
          = (ζ : K) ^ (∑ i ∈ s, quadExp (e i)).val := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
          rw [Finset.prod_insert hi, ih, Finset.sum_insert hi,
            ← pow_val_add_of_pow_eq_one hζK.pow_eq_one]
    simpa [d] using hgen Finset.univ
  have hdetΔ : (Δ : Matrix ι ι K).det = (ζ : K) ^ (∑ i, quadExp (e i)).val := by
    rw [hΔcoe, Matrix.det_diagonal, hprod_d]
  have hscalar_conj : ∀ (A : GL ι K) (u : Kˣ),
      MulAut.conj A (GeneralLinearGroup.scalar ι u) = GeneralLinearGroup.scalar ι u := by
    intro A u
    rw [MulAut.conj_apply, ← GeneralLinearGroup.scalar_commute u A, mul_assoc,
      mul_inv_cancel, mul_one]
  let D : GL ι K := A₀⁻¹ * Δ * A₀
  have hDdet : (D : Matrix ι ι K).det = (ζ : K) ^ (∑ i, quadExp (e i)).val := by
    change (((A₀⁻¹ * Δ * A₀ : GL ι K) : Matrix ι ι K)).det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj' A₀ (Δ : Matrix ι ι K)]
    exact hdetΔ
  refine ⟨Δ, hΔcoe, hDdet, ?_⟩
  intro x m hx
  let X : GL ι K := MulAut.conj A₀ x
  let H : GL ι K := MulAut.conj A₀ h
  let M : ZMod p := (m : ZMod p)
  have hH_eq : H = A₀ * h * A₀⁻¹ := by
    change MulAut.conj A₀ h = A₀ * h * A₀⁻¹
    rw [MulAut.conj_apply]
  have hHdiag : (H : Matrix ι ι K) = diagonal (fun i => (ζ : K) ^ (e i).val) := by
    rw [hH_eq]
    exact hdiag
  have hXu : H * X = GeneralLinearGroup.scalar ι (ζ ^ m) * (X * H) := by
    change MulAut.conj A₀ h * MulAut.conj A₀ x = _
    calc MulAut.conj A₀ h * MulAut.conj A₀ x
        = MulAut.conj A₀ (h * x) := (map_mul _ _ _).symm
      _ = MulAut.conj A₀ (GeneralLinearGroup.scalar ι (ζ ^ m) * (x * h)) := by rw [hx]
      _ = MulAut.conj A₀ (GeneralLinearGroup.scalar ι (ζ ^ m)) *
            MulAut.conj A₀ (x * h) := map_mul _ _ _
      _ = GeneralLinearGroup.scalar ι (ζ ^ m) *
            (MulAut.conj A₀ x * MulAut.conj A₀ h) := by
          rw [hscalar_conj A₀, map_mul]
      _ = GeneralLinearGroup.scalar ι (ζ ^ m) * (X * H) := rfl
  have hXcond : (H : Matrix ι ι K) * (X : Matrix ι ι K)
      = ((ζ : K) ^ m) • ((X : Matrix ι ι K) * (H : Matrix ι ι K)) := by
    have h := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hXu
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_pow_eq_pow_val] at h
    rwa [← smul_eq_diagonal_mul] at h
  have hM_pow : (ζ : K) ^ M.val = (ζ : K) ^ m := by
    change (ζ : K) ^ ((m : ZMod p).val) = (ζ : K) ^ m
    rw [ZMod.val_natCast, ← pow_eq_pow_mod m hζK.pow_eq_one]
  have hXshift : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + M := by
    apply shift_of_mul_eq hζK
    rw [hHdiag, ← hM_pow] at hXcond
    exact hXcond
  have hfM : ∀ j, quadExp (e j + M) = quadExp (e j) + quadExp M + M * e j :=
    fun j => quadExp_add hp2 (e j) M
  let t : ι → K := fun j => (ζ : K) ^ (e j).val
  have ht_pow_m : ∀ j, (t j) ^ m = (ζ : K) ^ (M * e j).val := by
    intro j
    change ((ζ : K) ^ (e j).val) ^ m = (ζ : K) ^ (M * e j).val
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hζK.pow_eq_one
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have hdiag_shift : ∀ j, (ζ : K) ^ (quadExp (e j + M)).val
      = (ζ : K) ^ (quadExp M).val * ((t j) ^ m * (ζ : K) ^ (quadExp (e j)).val) := by
    intro j
    have hf := hfM j
    calc
      (ζ : K) ^ (quadExp (e j + M)).val
          = (ζ : K) ^ (quadExp (e j) + quadExp M + M * e j).val := by rw [hf]
      _ = (ζ : K) ^ (quadExp (e j) + quadExp M).val * (ζ : K) ^ (M * e j).val :=
          pow_val_add_of_pow_eq_one hζK.pow_eq_one _ _
      _ = ((ζ : K) ^ (quadExp (e j)).val * (ζ : K) ^ (quadExp M).val) *
            (ζ : K) ^ (M * e j).val := by
          rw [pow_val_add_of_pow_eq_one hζK.pow_eq_one]
      _ = (ζ : K) ^ (quadExp M).val *
            ((t j) ^ m * (ζ : K) ^ (quadExp (e j)).val) := by
          rw [← ht_pow_m j]
          ring
  have hΔX : (Δ : Matrix ι ι K) * (X : Matrix ι ι K) *
        ((Δ⁻¹ : GL ι K) : Matrix ι ι K)
      = ((GeneralLinearGroup.scalar ι (ζ ^ (quadExp M).val) : GL ι K) : Matrix ι ι K) *
          (((X * H ^ m : GL ι K)) : Matrix ι ι K) := by
    change (diagonal d * (X : Matrix ι ι K) * diagonal (fun i => (d i)⁻¹)) =
      (diagonal (fun _ : ι => (ζ : K) ^ (quadExp M).val) *
        ((X : Matrix ι ι K) * (H : Matrix ι ι K) ^ m))
    ext i j
    rw [hHdiag, Matrix.diagonal_pow]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : (X : Matrix ι ι K) i j = 0
    · simp [hij]
    · have hshift := hXshift i j hij
      have hd : d i = (ζ : K) ^ (quadExp M).val * ((t j) ^ m * d j) := by
        change (ζ : K) ^ (quadExp (e i)).val
          = (ζ : K) ^ (quadExp M).val * ((t j) ^ m * (ζ : K) ^ (quadExp (e j)).val)
        rw [hshift]
        exact hdiag_shift j
      rw [hd]
      field_simp [hd_ne j]
      simp only [Pi.pow_apply]
      ring
  have hΔX_unit : Δ * X * Δ⁻¹
      = GeneralLinearGroup.scalar ι (ζ ^ (quadExp M).val) * (X * H ^ m) := by
    apply Units.ext
    simpa only [Units.val_mul] using hΔX
  have hconjX : MulAut.conj A₀⁻¹ X = x := by
    change (MulAut.conj A₀⁻¹ * MulAut.conj A₀) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hconjH : MulAut.conj A₀⁻¹ H = h := by
    change (MulAut.conj A₀⁻¹ * MulAut.conj A₀) h = h
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hconjH_pow : MulAut.conj A₀⁻¹ (H ^ m) = h ^ m := by
    rw [map_pow, hconjH]
  have hconj_inv : MulAut.conj A₀⁻¹ (Δ⁻¹) = (MulAut.conj A₀⁻¹ Δ)⁻¹ := map_inv _ _
  have hDconj : MulAut.conj A₀⁻¹ Δ = D := by
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨ζ ^ (quadExp M).val, ?_⟩
  have h := congrArg (MulAut.conj A₀⁻¹) hΔX_unit
  simp only [map_mul] at h
  rw [hconj_inv, hscalar_conj A₀⁻¹, hconjX, hconjH_pow, hDconj] at h
  exact h

theorem card_fiber_add_eq_of_shift {e : ι → ZMod p} {m : ZMod p} {X : GL ι K}
    (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m) (a : ZMod p) :
    Fintype.card {i // e i = a + m} = Fintype.card {i // e i = a} := by
  classical
  let P : Matrix ι ι K := diagonal (fun i => if e i = a + m then (1 : K) else 0)
  let P' : Matrix ι ι K := diagonal (fun i => if e i = a then (1 : K) else 0)
  have hP : P * (X : Matrix ι ι K) = (X : Matrix ι ι K) * P' := by
    have h := diagonal_mul_eq_mul_diagonal_of_shift (X := (X : Matrix ι ι K)) hX
      (fun b : ZMod p => if b = a + m then (1 : K) else 0)
    simpa [P, P'] using h
  have hdetX : IsUnit ((X : Matrix ι ι K).det) := by
    simpa using (X.det).isUnit
  have hrank : P.rank = P'.rank := by
    have h1 : (P * (X : Matrix ι ι K)).rank = P.rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det (X : Matrix ι ι K) P hdetX
    have h2 : ((X : Matrix ι ι K) * P').rank = P'.rank :=
      Matrix.rank_mul_eq_right_of_isUnit_det (X : Matrix ι ι K) P' hdetX
    rw [hP] at h1
    exact h1.symm.trans h2
  have hcardP : Fintype.card {i // e i = a + m} = P.rank := by
    rw [show P = diagonal (fun i => if e i = a + m then (1 : K) else 0) from rfl,
      Matrix.rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by
      by_cases h : e i = a + m <;> simp [h]))
  have hcardP' : Fintype.card {i // e i = a} = P'.rank := by
    rw [show P' = diagonal (fun i => if e i = a then (1 : K) else 0) from rfl,
      Matrix.rank_diagonal]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by
      by_cases h : e i = a <;> simp [h]))
  calc
    Fintype.card {i // e i = a + m} = P.rank := hcardP
    _ = P'.rank := hrank
    _ = Fintype.card {i // e i = a} := hcardP'.symm

theorem card_fiber_mul_eq_of_shift [Fact p.Prime] {e : ι → ZMod p} {m : ZMod p} (hm : m ≠ 0)
    {X : GL ι K} (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m)
    (a : ZMod p) : p * Fintype.card {i // e i = a} = Fintype.card ι := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hshift : ∀ k : ℕ, Fintype.card {i // e i = a + (k : ZMod p) * m} =
      Fintype.card {i // e i = a} := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep := card_fiber_add_eq_of_shift (e := e) (m := m) (X := X) hX
          (a + (k : ZMod p) * m)
        have harg : a + ((k + 1 : ℕ) : ZMod p) * m = (a + (k : ZMod p) * m) + m := by
          push_cast
          ring
        rw [harg, hstep, ih]
  have hsum : (∑ b : ZMod p, Fintype.card {i // e i = b}) = Fintype.card ι := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv e)
  have hb : ∀ b : ZMod p, Fintype.card {i // e i = b} = Fintype.card {i // e i = a} := by
    intro b
    have h := hshift ((b - a) * m⁻¹).val
    have hval : a + (((b - a) * m⁻¹).val : ZMod p) * m = b := by
      rw [ZMod.natCast_zmod_val]
      calc
        a + ((b - a) * m⁻¹) * m = a + (b - a) * (m⁻¹ * m) := by ring
        _ = a + (b - a) * 1 := by rw [inv_mul_cancel₀ hm]
        _ = b := by ring
    rwa [hval] at h
  have hconst : p * Fintype.card {i // e i = a} =
      ∑ b : ZMod p, Fintype.card {i // e i = a} := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, Nat.nsmul_eq_mul]
  calc
    p * Fintype.card {i // e i = a} =
        ∑ b : ZMod p, Fintype.card {i // e i = a} := hconst
    _ = ∑ b : ZMod p, Fintype.card {i // e i = b} :=
        Finset.sum_congr rfl (fun b _ => (hb b).symm)
    _ = Fintype.card ι := hsum

theorem sum_quadExp_three_of_shift {e : ι → ZMod 3} {m₀ : ZMod 3} (hm₀ : m₀ ≠ 0) {X : GL ι K}
    (hX : ∀ i j, (X : Matrix ι ι K) i j ≠ 0 → e i = e j + m₀) :
    (∑ i, quadExp (e i)) = ((Fintype.card ι / 3 : ℕ) : ZMod 3) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard := card_fiber_mul_eq_of_shift (e := e) (m := m₀) hm₀ (X := X) hX (0 : ZMod 3)
  let N : ℕ := Fintype.card {i // e i = 0}
  have hcardN : Fintype.card ι / 3 = N := by
    rw [← hcard]
    exact Nat.mul_div_right _ (by norm_num : 0 < 3)
  have hNb : ∀ b : ZMod 3, Fintype.card {i // e i = b} = N := by
    intro b
    have hb := card_fiber_mul_eq_of_shift (e := e) (m := m₀) hm₀ (X := X) hX b
    exact Nat.mul_left_cancel (by norm_num : 0 < 3) (hb.trans hcard.symm)
  have hsum_b : (∑ b : ZMod 3, quadExp (p := 3) b) = 1 := by
    have h41 : (4 : ZMod 3) = 1 := by
      apply ZMod.val_injective 3
      rw [ZMod.val_ofNat, ZMod.val_one_eq_one_mod]
    have h2inv : (2 : ZMod 3)⁻¹ = 2 := by
      refine ZMod.inv_eq_of_mul_eq_one 3 2 2 ?_
      norm_num
      exact h41
    have h0 : quadExp (p := 3) (0 : ZMod 3) = 0 := by simp [quadExp]
    have h1 : quadExp (p := 3) (1 : ZMod 3) = 0 := by simp [quadExp]
    have h2 : quadExp (p := 3) (2 : ZMod 3) = 1 := by
      simp only [quadExp, h2inv]
      norm_num
      exact h41
    rw [← (ZMod.finEquiv 3).toEquiv.sum_comp (fun b : ZMod 3 => quadExp b)]
    rw [Fin.sum_univ_three]
    change quadExp (p := 3) (0 : ZMod 3) + quadExp (p := 3) (1 : ZMod 3) +
      quadExp (p := 3) (2 : ZMod 3) = 1
    rw [h0, h1, h2]
    norm_num
  have h1 : (∑ i, quadExp (e i)) =
      ∑ b : ZMod 3, (Fintype.card {i // e i = b} : ZMod 3) * quadExp b := by
    rw [← Finset.sum_fiberwise' (s := Finset.univ) (g := e)
      (f := fun b : ZMod 3 => quadExp b)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Fintype.card_subtype]
  rw [h1, hcardN]
  simp_rw [hNb]
  rw [← Finset.mul_sum, hsum_b, mul_one]

theorem exists_quadPhase_three {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {h g : GL ι K}
    (hh : h ^ 3 = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1) (hu₀p : u₀ ^ 3 = 1)
    (hhg : h * g = GeneralLinearGroup.scalar ι u₀ * (g * h)) :
    ∃ D : GL ι K, (D : Matrix ι ι K).det = (ζ : K) ^ (Fintype.card ι / 3) ∧
      ∀ (x : GL ι K) (m : ℕ), h * x = GeneralLinearGroup.scalar ι (ζ ^ m) * (x * h) →
        ∃ c : Kˣ, D * x * D⁻¹ = GeneralLinearGroup.scalar ι c * (x * h ^ m) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨A₀, e, hdiag⟩ := exists_conj_diagonal_exponents hζ hh
  obtain ⟨m₀, hm₀, hX⟩ := exists_shift_of_partner hζ hdiag hu₀ hu₀p hhg
  have hsumf := sum_quadExp_three_of_shift hm₀ hX
  obtain ⟨Δ, -, hΔdet, hΔact⟩ :=
    quadPhase_spec (p := 3) (by norm_num : 3 ≠ 2) hζ hdiag
  refine ⟨A₀⁻¹ * Δ * A₀, ?_, fun x m hx => hΔact x m hx⟩
  rw [hΔdet, hsumf, ZMod.val_natCast, ← pow_eq_pow_mod _ hζK.pow_eq_one]

theorem det_eq_one_of_partner [Fact p.Prime] (hp2 : p ≠ 2) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {h g : GL ι K} (hh : h ^ p = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1) (hu₀p : u₀ ^ p = 1)
    (hhg : h * g = GeneralLinearGroup.scalar ι u₀ * (g * h)) :
    (h : Matrix ι ι K).det = 1 := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨A₀, e, hdiag⟩ := exists_conj_diagonal_exponents hζ hh
  obtain ⟨m₀, hm₀, hX⟩ := exists_shift_of_partner hζ hdiag hu₀ hu₀p hhg
  have hpι : p ∣ Fintype.card ι := by
    have h := card_fiber_mul_eq_of_shift (e := e) (m := m₀) hm₀
      (X := A₀ * g * A₀⁻¹) hX (0 : ZMod p)
    exact ⟨Fintype.card {i // e i = 0}, h.symm⟩
  have hsum : ∑ i, e i = 0 := sum_eq_zero_of_shift hp2 hpι hζK hm₀ hX
  have hdet_conj : ((A₀ * h * A₀⁻¹ : GL ι K) : Matrix ι ι K).det =
      (h : Matrix ι ι K).det := by
    rw [Units.val_mul, Units.val_mul]
    exact Matrix.det_units_conj A₀ (h : Matrix ι ι K)
  rw [← hdet_conj, hdiag, Matrix.det_diagonal]
  have hprod : ∏ i, (ζ : K) ^ (e i).val = (ζ : K) ^ (∑ i, e i).val := by
    have hgen : ∀ s : Finset ι,
        ∏ i ∈ s, (ζ : K) ^ (e i).val = (ζ : K) ^ (∑ i ∈ s, e i).val := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
          rw [Finset.prod_insert hi, ih, Finset.sum_insert hi,
            ← pow_val_add_of_pow_eq_one hζK.pow_eq_one]
    simpa using hgen Finset.univ
  rw [hprod, hsum, ZMod.val_zero, pow_zero]

theorem det_eq_pow_of_pow_eq_scalar [Fact p.Prime] (hp2 : p ≠ 2) {x y : GL ι K}
    (hx : x ^ p = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1) (hu₀p : u₀ ^ p = 1)
    (hxy : x * y = GeneralLinearGroup.scalar ι u₀ * (y * x)) {μ : Kˣ}
    (hy : y ^ p = GeneralLinearGroup.scalar ι μ) :
    (y : Matrix ι ι K).det = (μ : K) ^ (Fintype.card ι / p) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζuK : IsPrimitiveRoot (u₀ : K) p := by
    rw [IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_prime ?_ ?_
    · simpa using congrArg (fun u : Kˣ => (u : K)) hu₀p
    · intro h
      exact hu₀ (Units.ext h)
  have hζu : IsPrimitiveRoot u₀ p := IsPrimitiveRoot.coe_units_iff.mp hζuK
  obtain ⟨A₀, e, hdiag⟩ := exists_conj_diagonal_exponents hζu hx
  obtain ⟨m₀, hm₀, hX⟩ := exists_shift_of_partner hζu hdiag hu₀ hu₀p hxy
  have hpι : p ∣ Fintype.card ι := by
    have h := card_fiber_mul_eq_of_shift (e := e) (m := m₀) hm₀
      (X := A₀ * y * A₀⁻¹) hX (0 : ZMod p)
    exact ⟨Fintype.card {i // e i = 0}, h.symm⟩
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  have hf_inj : Function.Injective f := (algebraMap K L).injective
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_pow_nat_eq (f (μ : K)) (Fact.out : p.Prime).pos
  have hμ_ne : f (μ : K) ≠ 0 := by
    simp
  have hθ_ne : θ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at hθ
    exact hμ_ne hθ.symm
  let θu : Lˣ := Units.mk0 θ hθ_ne
  have hθu_pow : θu ^ p = Units.map f.toMonoidHom μ := by
    ext
    simpa [θu] using hθ
  let x' : GL ι L := GeneralLinearGroup.map f x
  let y' : GL ι L := GeneralLinearGroup.map f y
  have hy' : y' ^ p = GeneralLinearGroup.scalar ι (Units.map f.toMonoidHom μ) := by
    have h := congrArg (GeneralLinearGroup.map f) hy
    simpa [y', GeneralLinearGroup.map_scalar] using h
  have hxy' : x' * y' =
      GeneralLinearGroup.scalar ι (Units.map f.toMonoidHom u₀) * (y' * x') := by
    have h := congrArg (GeneralLinearGroup.map f) hxy
    simpa [x', y', GeneralLinearGroup.map_scalar] using h
  let y'' : GL ι L := GeneralLinearGroup.scalar ι θu⁻¹ * y'
  have hθu_inv_pow : (θu⁻¹) ^ p = (Units.map f.toMonoidHom μ)⁻¹ := by
    rw [inv_pow, hθu_pow]
  have hy''_pow : y'' ^ p = 1 := by
    have hcomm : Commute (GeneralLinearGroup.scalar ι θu⁻¹) y' :=
      GeneralLinearGroup.scalar_commute θu⁻¹ y'
    calc
      y'' ^ p = (GeneralLinearGroup.scalar ι θu⁻¹) ^ p * y' ^ p := hcomm.mul_pow p
      _ = GeneralLinearGroup.scalar ι ((θu⁻¹) ^ p) *
            GeneralLinearGroup.scalar ι (Units.map f.toMonoidHom μ) := by rw [map_pow, hy']
      _ = 1 := by
          rw [← map_mul, hθu_inv_pow, inv_mul_cancel, map_one]
  have hy'x' : y' * x' =
      GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) * (x' * y') := by
    have h := congrArg
      (fun z => (GeneralLinearGroup.scalar ι (Units.map f.toMonoidHom u₀))⁻¹ * z) hxy'
    simpa [mul_assoc] using h.symm
  have hy''x' : y'' * x' =
      GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) * (x' * y'') := by
    calc
      y'' * x' = GeneralLinearGroup.scalar ι θu⁻¹ * (y' * x') := by
          change (GeneralLinearGroup.scalar ι θu⁻¹ * y') * x' =
            GeneralLinearGroup.scalar ι θu⁻¹ * (y' * x')
          rw [mul_assoc]
      _ = GeneralLinearGroup.scalar ι θu⁻¹ *
            (GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) * (x' * y')) := by
          rw [hy'x']
      _ = (GeneralLinearGroup.scalar ι θu⁻¹ *
            GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹)) * (x' * y') := by
          rw [mul_assoc]
      _ = (GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) *
            GeneralLinearGroup.scalar ι θu⁻¹) * (x' * y') := by
          rw [GeneralLinearGroup.scalar_commute]
      _ = GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) *
            (GeneralLinearGroup.scalar ι θu⁻¹ * (x' * y')) := by
          rw [mul_assoc]
      _ = GeneralLinearGroup.scalar ι ((Units.map f.toMonoidHom u₀)⁻¹) * (x' * y'') := by
          congr 1
          calc
            GeneralLinearGroup.scalar ι θu⁻¹ * (x' * y')
                = (GeneralLinearGroup.scalar ι θu⁻¹ * x') * y' := by rw [mul_assoc]
            _ = (x' * GeneralLinearGroup.scalar ι θu⁻¹) * y' := by
                rw [GeneralLinearGroup.scalar_commute]
            _ = x' * (GeneralLinearGroup.scalar ι θu⁻¹ * y') := by rw [mul_assoc]
            _ = x' * y'' := rfl
  have hu₀'_map_ne : Units.map f.toMonoidHom u₀ ≠ 1 := by
    intro h
    apply hu₀
    apply Units.ext
    apply hf_inj
    simpa using congrArg (fun u : Lˣ => (u : L)) h
  have hu₀'_ne : (Units.map f.toMonoidHom u₀)⁻¹ ≠ 1 := inv_ne_one.mpr hu₀'_map_ne
  have hu₀'_pow : ((Units.map f.toMonoidHom u₀)⁻¹) ^ p = 1 := by
    rw [inv_pow]
    have h : (Units.map f.toMonoidHom u₀) ^ p = 1 := by
      rw [← map_pow, hu₀p, map_one]
    rw [h, inv_one]
  have hζuL : IsPrimitiveRoot (Units.map f.toMonoidHom u₀) p := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa using hζuK.map_of_injective hf_inj
  have hζu'' : IsPrimitiveRoot ((Units.map f.toMonoidHom u₀)⁻¹) p := hζuL.inv
  have hdet_y'' : (y'' : Matrix ι ι L).det = 1 :=
    det_eq_one_of_partner (p := p) (K := L) (ζ := (Units.map f.toMonoidHom u₀)⁻¹)
      (h := y'') (g := x') (u₀ := (Units.map f.toMonoidHom u₀)⁻¹)
      hp2 hζu'' hy''_pow hu₀'_ne hu₀'_pow hy''x'
  have hy'_eq : y' = GeneralLinearGroup.scalar ι θu * y'' := by
    change y' = GeneralLinearGroup.scalar ι θu *
      (GeneralLinearGroup.scalar ι θu⁻¹ * y')
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hdet_y' : (y' : Matrix ι ι L).det = (θ : L) ^ Fintype.card ι := by
    rw [hy'_eq, Units.val_mul, Matrix.det_mul, hdet_y'', mul_one]
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ]
    rfl
  have hcard_div : p * (Fintype.card ι / p) = Fintype.card ι := Nat.mul_div_cancel' hpι
  have hθ_card : θ ^ Fintype.card ι = f ((μ : K) ^ (Fintype.card ι / p)) := by
    calc
      θ ^ Fintype.card ι = θ ^ (p * (Fintype.card ι / p)) := by
        conv_lhs => rw [← hcard_div]
      _ = (θ ^ p) ^ (Fintype.card ι / p) := by rw [pow_mul]
      _ = (f (μ : K)) ^ (Fintype.card ι / p) := by rw [hθ]
      _ = f ((μ : K) ^ (Fintype.card ι / p)) := by rw [map_pow]
  have hf_det : f ((y : Matrix ι ι K).det) = θ ^ Fintype.card ι := by
    rw [RingHom.map_det]
    simpa [y'] using hdet_y'
  have hmap_eq : f ((y : Matrix ι ι K).det) = f ((μ : K) ^ (Fintype.card ι / p)) := by
    rw [hf_det, hθ_card]
  exact hf_inj hmap_eq

theorem exists_quadPhase (hp : p.Prime) (hp5 : 5 ≤ p) (hpι : p ∣ Fintype.card ι) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {h g : GL ι K} (hh : h ^ p = 1) {u₀ : Kˣ} (hu₀ : u₀ ≠ 1)
    (hu₀p : u₀ ^ p = 1) (hhg : h * g = GeneralLinearGroup.scalar ι u₀ * (g * h)) :
    ∃ D : GL ι K, (D : Matrix ι ι K).det = 1 ∧
      ∀ (x : GL ι K) (m : ℕ), h * x = GeneralLinearGroup.scalar ι (ζ ^ m) * (x * h) →
        ∃ c : Kˣ, D * x * D⁻¹ = GeneralLinearGroup.scalar ι c * (x * h ^ m) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  obtain ⟨A₀, e, hdiag⟩ := exists_conj_diagonal_exponents hζ hh
  obtain ⟨m₀, hm₀, hX⟩ := exists_shift_of_partner hζ hdiag hu₀ hu₀p hhg
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hsum1 : ∑ i, e i = 0 := sum_eq_zero_of_shift hp2 hpι hζK hm₀ hX
  have hsum2 : ∑ i, e i ^ 2 = 0 := sum_sq_eq_zero_of_shift hp2 hp3 hpι hζK hm₀ hX
  have hsumf : ∑ i, quadExp (e i) = 0 := by
    have h₁ : ∑ i, quadExp (e i) = (2 : ZMod p)⁻¹ * ∑ i, (e i ^ 2 - e i) := by
      simp only [quadExp]
      rw [Finset.mul_sum]
    have h₂ : ∑ i, (e i ^ 2 - e i) = (∑ i, e i ^ 2) - ∑ i, e i :=
      Finset.sum_sub_distrib (s := Finset.univ) (f := fun i => e i ^ 2)
        (g := fun i => e i)
    rw [h₁, h₂, hsum2, hsum1, sub_self, mul_zero]
  obtain ⟨Δ, -, hΔdet, hΔact⟩ := quadPhase_spec hp2 hζ hdiag
  let D : GL ι K := A₀⁻¹ * Δ * A₀
  refine ⟨D, ?_, ?_⟩
  · change (((A₀⁻¹ * Δ * A₀ : GL ι K) : Matrix ι ι K)).det = 1
    rw [hΔdet, hsumf, ZMod.val_zero, pow_zero]
  · intro x m hx
    simpa [D] using hΔact x m hx

end CFSG.StandardType.TypeA.PGLTor
