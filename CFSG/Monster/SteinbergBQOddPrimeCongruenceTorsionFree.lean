module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Monster

open Matrix Finset

variable (p : ℕ) [hp : Fact p.Prime]

@[expose] def ratLocal : Subring ℚ where
  carrier := {x | ¬ p ∣ x.den}
  mul_mem' := by
    intro a b ha hb h
    exact (hp.out.dvd_mul.1 (h.trans (Rat.mul_den_dvd a b))).elim ha hb
  one_mem' := by
    change ¬ p ∣ (1 : ℚ).den
    simp [hp.out.ne_one]
  add_mem' := by
    intro a b ha hb h
    exact (hp.out.dvd_mul.1 (h.trans (Rat.add_den_dvd a b))).elim ha hb
  zero_mem' := by
    change ¬ p ∣ (0 : ℚ).den
    simp [hp.out.ne_one]
  neg_mem' := by
    intro a ha
    change ¬ p ∣ (-a).den
    rwa [Rat.neg_den]

theorem mem_ratLocal {x : ℚ} : x ∈ ratLocal p ↔ ¬ p ∣ x.den :=
  Iff.rfl

theorem mem_ratLocal_iff {x : ℚ} :
    x ∈ ratLocal p ↔ ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ x = a / b := by
  constructor
  · intro hx
    exact ⟨x.num, x.den, by exact_mod_cast x.den_ne_zero,
      fun h => hx (Int.natCast_dvd_natCast.1 h), (Rat.num_div_den x).symm⟩
  · rintro ⟨a, b, -, hb, rfl⟩ h
    rw [← Rat.divInt_eq_div] at h
    exact hb ((Int.natCast_dvd_natCast.2 h).trans (Rat.den_dvd a b))

namespace SteinbergBQ

@[expose] def ratRedFun (x : ℚ) : ZMod p :=
  (x.num : ZMod p) * (x.den : ZMod p)⁻¹

theorem ratRedFun_eq {x : ℚ} {a b : ℤ} (hb : ¬ (p : ℤ) ∣ b) (hx : x = a / b) :
    ratRedFun p x = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero _)
  have hden : ¬ p ∣ x.den := (mem_ratLocal_iff p).2 ⟨a, b, hb0, hb, hx⟩
  have key : x.num * b = a * x.den := by
    have h1 : (x.num : ℚ) / x.den = a / b := by rw [Rat.num_div_den, hx]
    rw [div_eq_div_iff (by exact_mod_cast x.den_ne_zero) (by exact_mod_cast hb0)] at h1
    exact_mod_cast h1
  have key' : (x.num : ZMod p) * b = a * x.den := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod p) key
  have hbz : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 h)
  have hdz : (x.den : ZMod p) ≠ 0 := fun h => hden ((ZMod.natCast_eq_zero_iff _ p).1 h)
  unfold ratRedFun
  field_simp
  linear_combination key'

end SteinbergBQ

@[expose] def ratLocalRed : ratLocal p →+* ZMod p where
  toFun x := SteinbergBQ.ratRedFun p x
  map_one' := by simp [SteinbergBQ.ratRedFun]
  map_mul' x y := by
    have hxy : ¬ (p : ℤ) ∣ (((x : ℚ).den * (y : ℚ).den : ℕ) : ℤ) := fun h =>
      (hp.out.dvd_mul.1 (Int.natCast_dvd_natCast.1 h)).elim x.2 y.2
    have he : ((x * y : ratLocal p) : ℚ) = (((x : ℚ).num * (y : ℚ).num : ℤ) : ℚ) /
        ((((x : ℚ).den * (y : ℚ).den : ℕ) : ℤ) : ℚ) := by
      push_cast
      conv_lhs => rw [← Rat.num_div_den (x : ℚ), ← Rat.num_div_den (y : ℚ)]
      rw [div_mul_div_comm]
    have hxd : ((x : ℚ).den : ZMod p) ≠ 0 := fun h => x.2 ((ZMod.natCast_eq_zero_iff _ p).1 h)
    have hyd : ((y : ℚ).den : ZMod p) ≠ 0 := fun h => y.2 ((ZMod.natCast_eq_zero_iff _ p).1 h)
    rw [SteinbergBQ.ratRedFun_eq p hxy he]
    unfold SteinbergBQ.ratRedFun
    push_cast
    field_simp
  map_zero' := by simp [SteinbergBQ.ratRedFun]
  map_add' x y := by
    have hxy : ¬ (p : ℤ) ∣ (((x : ℚ).den * (y : ℚ).den : ℕ) : ℤ) := fun h =>
      (hp.out.dvd_mul.1 (Int.natCast_dvd_natCast.1 h)).elim x.2 y.2
    have he : ((x + y : ratLocal p) : ℚ) =
        (((x : ℚ).num * (y : ℚ).den + (y : ℚ).num * (x : ℚ).den : ℤ) : ℚ) /
          ((((x : ℚ).den * (y : ℚ).den : ℕ) : ℤ) : ℚ) := by
      push_cast
      conv_lhs => rw [← Rat.num_div_den (x : ℚ), ← Rat.num_div_den (y : ℚ)]
      rw [div_add_div _ _ (by exact_mod_cast (x : ℚ).den_ne_zero)
        (by exact_mod_cast (y : ℚ).den_ne_zero)]
      ring
    have hxd : ((x : ℚ).den : ZMod p) ≠ 0 := fun h => x.2 ((ZMod.natCast_eq_zero_iff _ p).1 h)
    have hyd : ((y : ℚ).den : ZMod p) ≠ 0 := fun h => y.2 ((ZMod.natCast_eq_zero_iff _ p).1 h)
    rw [SteinbergBQ.ratRedFun_eq p hxy he]
    unfold SteinbergBQ.ratRedFun
    push_cast
    field_simp

theorem ratLocalRed_apply (x : ratLocal p) :
    ratLocalRed p x = ((x : ℚ).num : ZMod p) * ((x : ℚ).den : ZMod p)⁻¹ :=
  rfl

theorem ratLocalRed_eq (x : ratLocal p) {a b : ℤ} (hb : ¬ (p : ℤ) ∣ b) (hx : (x : ℚ) = a / b) :
    ratLocalRed p x = (a : ZMod p) * (b : ZMod p)⁻¹ :=
  SteinbergBQ.ratRedFun_eq p hb hx

theorem ratLocalRed_eq_zero_iff (x : ratLocal p) : ratLocalRed p x = 0 ↔ ∃ y, x = p * y := by
  constructor
  · intro h
    have hd : ((x : ℚ).den : ZMod p) ≠ 0 := fun h0 => x.2 ((ZMod.natCast_eq_zero_iff _ p).1 h0)
    rw [ratLocalRed_apply, mul_eq_zero, inv_eq_zero] at h
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (h.resolve_right hd)
    refine ⟨⟨(k : ℚ) / (x : ℚ).den, (mem_ratLocal_iff p).2 ⟨k, (x : ℚ).den,
      by exact_mod_cast (x : ℚ).den_ne_zero, fun h => x.2 (Int.natCast_dvd_natCast.1 h),
      by push_cast; rfl⟩⟩, Subtype.ext ?_⟩
    change (x : ℚ) = (p : ℚ) * ((k : ℚ) / (x : ℚ).den)
    conv_lhs => rw [← Rat.num_div_den (x : ℚ), hk]
    push_cast
    ring
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem isUnit_of_ratLocalRed_ne_zero {x : ratLocal p} (hx : ratLocalRed p x ≠ 0) : IsUnit x := by
  have hn : ¬ (p : ℤ) ∣ (x : ℚ).num := fun h =>
    hx (by rw [ratLocalRed_apply, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h, zero_mul])
  have hn0 : (x : ℚ).num ≠ 0 := fun h => hn (h ▸ dvd_zero _)
  have hx0 : (x : ℚ) ≠ 0 := Rat.num_ne_zero.1 hn0
  have hinv : (x : ℚ)⁻¹ ∈ ratLocal p := (mem_ratLocal_iff p).2 ⟨(x : ℚ).den, (x : ℚ).num, hn0, hn,
    by
      push_cast
      conv_lhs => rw [← Rat.num_div_den (x : ℚ)]
      rw [inv_div]⟩
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hx0))

namespace SteinbergBQ

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

@[expose] def pPowMatrices (k : ℕ) : Submodule (ratLocal p) (Matrix ι ι (ratLocal p)) :=
  LinearMap.range (((p : ratLocal p) ^ k) • LinearMap.id)

variable {p ι}

omit [Fintype ι] [DecidableEq ι] in
theorem mem_pPowMatrices {k : ℕ} {M : Matrix ι ι (ratLocal p)} :
    M ∈ pPowMatrices p ι k ↔ ∃ C, M = (p : ratLocal p) ^ k • C := by
  simp only [pPowMatrices, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
    eq_comm]

omit [DecidableEq ι] in
theorem mul_mem_pPowMatrices_left (A : Matrix ι ι (ratLocal p)) {k : ℕ}
    {M : Matrix ι ι (ratLocal p)} (hM : M ∈ pPowMatrices p ι k) : A * M ∈ pPowMatrices p ι k := by
  obtain ⟨C, rfl⟩ := mem_pPowMatrices.1 hM
  exact mem_pPowMatrices.2 ⟨A * C, Matrix.mul_smul A _ C⟩

omit [DecidableEq ι] in
theorem mul_mem_pPowMatrices_right (A : Matrix ι ι (ratLocal p)) {k : ℕ}
    {M : Matrix ι ι (ratLocal p)} (hM : M ∈ pPowMatrices p ι k) : M * A ∈ pPowMatrices p ι k := by
  obtain ⟨C, rfl⟩ := mem_pPowMatrices.1 hM
  exact mem_pPowMatrices.2 ⟨C * A, Matrix.smul_mul _ C A⟩

omit [DecidableEq ι] in
theorem mul_self_mem_pPowMatrices_two {X : Matrix ι ι (ratLocal p)}
    (hX : X ∈ pPowMatrices p ι 1) : X * X ∈ pPowMatrices p ι 2 := by
  obtain ⟨C, rfl⟩ := mem_pPowMatrices.1 hX
  exact mem_pPowMatrices.2 ⟨C * C, by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_add]⟩

omit [Fintype ι] [DecidableEq ι] in
theorem smul_mem_pPowMatrices_two {M : Matrix ι ι (ratLocal p)} (hM : M ∈ pPowMatrices p ι 1) :
    (p : ratLocal p) • M ∈ pPowMatrices p ι 2 := by
  obtain ⟨C, rfl⟩ := mem_pPowMatrices.1 hM
  exact mem_pPowMatrices.2 ⟨C, by rw [smul_smul, ← pow_succ']⟩

theorem isUnit_of_sub_smul_one_mem {c : ratLocal p} (hc : ratLocalRed p c ≠ 0)
    {M : Matrix ι ι (ratLocal p)} (hM : M - c • 1 ∈ pPowMatrices p ι 1) : IsUnit M := by
  obtain ⟨C, hC⟩ := mem_pPowMatrices.1 hM
  have hMe : M = c • 1 + (p : ratLocal p) ^ 1 • C := by
    rw [← hC]
    abel
  have hmap : (ratLocalRed p).mapMatrix M = ratLocalRed p c • (1 : Matrix ι ι (ZMod p)) := by
    ext i j
    rw [hMe]
    by_cases hij : i = j <;> simp [hij]
  have hdet : ratLocalRed p M.det ≠ 0 := by
    rw [RingHom.map_det, hmap, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_of_ratLocalRed_ne_zero p hdet)

theorem one_add_pow_sub_mem_two {X : Matrix ι ι (ratLocal p)} (hX : X ∈ pPowMatrices p ι 1)
    (i : ℕ) : (1 + X) ^ i - 1 - (i : ratLocal p) • X ∈ pPowMatrices p ι 2 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hid : (1 + X) ^ (i + 1) - 1 - ((i + 1 : ℕ) : ratLocal p) • X =
        ((1 + X) ^ i - 1 - (i : ratLocal p) • X) * (1 + X) + (i : ratLocal p) • (X * X) := by
      push_cast
      simp only [pow_succ, sub_mul, mul_add, mul_one, one_mul, Matrix.smul_mul, add_smul,
        one_smul]
      abel
    rw [hid]
    exact add_mem (mul_mem_pPowMatrices_right _ ih)
      (Submodule.smul_mem _ _ (mul_self_mem_pPowMatrices_two hX))

theorem geom_sum_sub_mem_two (hp2 : p ≠ 2) {X : Matrix ι ι (ratLocal p)}
    (hX : X ∈ pPowMatrices p ι 1) :
    ∑ i ∈ range p, (1 + X) ^ i - (p : ratLocal p) • 1 ∈ pPowMatrices p ι 2 := by
  obtain ⟨m, hm⟩ := hp.out.odd_of_ne_two hp2
  have hsum : ∑ i ∈ range p, i = p * m := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [Finset.sum_range_id_mul_two, hm, Nat.add_sub_cancel]
    ring
  have hsplit : ∑ i ∈ range p, (1 + X) ^ i - (p : ratLocal p) • 1 =
      ∑ i ∈ range p, ((1 + X) ^ i - 1 - (i : ratLocal p) • X) +
        ((∑ i ∈ range p, i : ℕ) : ratLocal p) • X := by
    rw [Nat.cast_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    simp only [sub_add_cancel]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  rw [hsplit, hsum, Nat.cast_mul, mul_smul]
  exact add_mem (Submodule.sum_mem _ fun i _ => one_add_pow_sub_mem_two hX i)
    (smul_mem_pPowMatrices_two (Submodule.smul_mem _ _ hX))

theorem eq_zero_of_one_add_pow_prime (hp2 : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {X : Matrix ι ι (ratLocal p)} (hX : X ∈ pPowMatrices p ι 1) (h : (1 + X) ^ ℓ = 1) :
    X = 0 := by
  have hSX : (∑ i ∈ range ℓ, (1 + X) ^ i) * X = 0 := by
    have h1 := geom_sum_mul (1 + X) ℓ
    rwa [add_sub_cancel_left, h, sub_self] at h1
  by_cases hℓp : ℓ = p
  ·
    rw [hℓp] at hSX
    obtain ⟨W, hW⟩ := mem_pPowMatrices.1 (geom_sum_sub_mem_two hp2 hX)
    have hSe : ∑ i ∈ range p, (1 + X) ^ i = (p : ratLocal p) • (1 + (p : ratLocal p) • W) := by
      rw [smul_add, smul_smul, ← pow_two, ← hW]
      abel
    rw [hSe, Matrix.smul_mul] at hSX
    have hp0 : (p : ratLocal p) ≠ 0 := fun h0 =>
      hp.out.ne_zero (by exact_mod_cast congrArg Subtype.val h0)
    have hU : IsUnit (1 + (p : ratLocal p) • W) := by
      refine isUnit_of_sub_smul_one_mem (c := 1) (by rw [map_one]; exact one_ne_zero) ?_
      rw [one_smul, add_sub_cancel_left]
      exact mem_pPowMatrices.2 ⟨W, by rw [pow_one]⟩
    exact hU.mul_right_eq_zero.1 ((smul_eq_zero.1 hSX).resolve_left hp0)
  ·
    have hS1 : ∑ i ∈ range ℓ, (1 + X) ^ i - (ℓ : ratLocal p) • 1 ∈ pPowMatrices p ι 1 := by
      have hS : ∑ i ∈ range ℓ, (1 + X) ^ i - (ℓ : ratLocal p) • (1 : Matrix ι ι (ratLocal p)) =
          ∑ i ∈ range ℓ, ((1 + X) ^ i - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
      rw [hS]
      refine Submodule.sum_mem _ fun i _ => ?_
      have h1 := geom_sum_mul (1 + X) i
      rw [add_sub_cancel_left] at h1
      rw [← h1]
      exact mul_mem_pPowMatrices_left _ hX
    have hℓz : ratLocalRed p (ℓ : ratLocal p) ≠ 0 := by
      rw [map_natCast]
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff ℓ p).1 h0
      exact hℓp ((Nat.prime_dvd_prime_iff_eq hp.out hℓ).1 hdvd).symm
    exact (isUnit_of_sub_smul_one_mem hℓz hS1).mul_right_eq_zero.1 hSX

theorem sub_one_mem_of_map_eq_one {g : GL ι (ratLocal p)}
    (hg : Matrix.GeneralLinearGroup.map (ratLocalRed p) g = 1) :
    (g : Matrix ι ι (ratLocal p)) - 1 ∈ pPowMatrices p ι 1 := by
  have hentry : ∀ i j, ∃ y : ratLocal p,
      (g : Matrix ι ι (ratLocal p)) i j - (1 : Matrix ι ι (ratLocal p)) i j = p * y := by
    intro i j
    refine (ratLocalRed_eq_zero_iff p _).1 ?_
    have h1 := congrArg (fun u : GL ι (ZMod p) => (u : Matrix ι ι (ZMod p)) i j) hg
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h1
    rw [map_sub, h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  choose C hC using hentry
  refine mem_pPowMatrices.2 ⟨Matrix.of C, ?_⟩
  ext i j
  rw [Matrix.sub_apply, hC, Matrix.smul_apply, pow_one, Matrix.of_apply, smul_eq_mul]

theorem eq_one_of_map_eq_one_of_isOfFinOrder (hp2 : p ≠ 2) {g : GL ι (ratLocal p)}
    (hg : Matrix.GeneralLinearGroup.map (ratLocalRed p) g = 1) (hfin : IsOfFinOrder g) :
    g = 1 := by
  by_contra hne
  have hm0 : orderOf g ≠ 0 := hfin.orderOf_pos.ne'
  have hm1 : orderOf g ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.1 h1)
  obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd hm1
  have hord : orderOf (g ^ (orderOf g / ℓ)) = ℓ := orderOf_pow_orderOf_div hm0 hℓm
  have hh : Matrix.GeneralLinearGroup.map (ratLocalRed p) (g ^ (orderOf g / ℓ)) = 1 := by
    rw [map_pow, hg, one_pow]
  have hX := SteinbergBQ.sub_one_mem_of_map_eq_one hh
  have hpow : (1 + (((g ^ (orderOf g / ℓ) : GL ι (ratLocal p)) : Matrix ι ι (ratLocal p)) -
      1)) ^ ℓ = 1 := by
    have h2 := pow_orderOf_eq_one (g ^ (orderOf g / ℓ))
    rw [hord] at h2
    rw [add_sub_cancel, ← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have h0 := SteinbergBQ.eq_zero_of_one_add_pow_prime hp2 hℓ hX hpow
  have h1 : g ^ (orderOf g / ℓ) = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h0)
  rw [h1, orderOf_one] at hord
  exact hℓ.one_lt.ne hord

end SteinbergBQ

theorem odd_prime_congruence_torsion_free (hp2 : p ≠ 2) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (∀ g : GL ι (ratLocal p), Matrix.GeneralLinearGroup.map (ratLocalRed p) g = 1 →
      IsOfFinOrder g → g = 1) ∧
    ∀ Γ : Subgroup (GL ι (ratLocal p)), Finite Γ →
      Set.InjOn (Matrix.GeneralLinearGroup.map (ratLocalRed p)) (Γ : Set (GL ι (ratLocal p))) := by
  have hker : ∀ g : GL ι (ratLocal p), Matrix.GeneralLinearGroup.map (ratLocalRed p) g = 1 →
      IsOfFinOrder g → g = 1 := fun g hg hfin =>
    SteinbergBQ.eq_one_of_map_eq_one_of_isOfFinOrder hp2 hg hfin
  refine ⟨hker, fun Γ _ g hg g' hg' heq => ?_⟩
  have hfin : IsOfFinOrder (g⁻¹ * g') := Submonoid.isOfFinOrder_coe.2
    (isOfFinOrder_of_finite (⟨g⁻¹ * g', Γ.mul_mem (Γ.inv_mem hg) hg'⟩ : Γ))
  exact inv_mul_eq_one.1 (hker _ (by rw [map_mul, map_inv, heq, inv_mul_cancel]) hfin)

end CFSG.Monster
