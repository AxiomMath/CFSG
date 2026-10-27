module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.Quasithin.Z4c2

open Polynomial

theorem exists_root_charpoly {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n]
    {r : ℕ} (hr : (r : F) ≠ 0) (A : Matrix n n F) (hA : A ^ r = 1) (hA1 : A ≠ 1) :
    ∃ ζ : AlgebraicClosure F, ζ ≠ 1 ∧ ζ ^ r = 1 ∧ aeval ζ A.charpoly = 0 := by
  classical
  set Φ : F[X] := ∑ i ∈ Finset.range r, X ^ i with hΦdef
  have hΦA : aeval A Φ * (A - 1) = 0 := by
    have h := geom_sum_mul A r
    rw [hA, sub_self] at h
    simpa [hΦdef, map_sum] using h
  have hnc : ¬ IsCoprime Φ A.charpoly := by
    rintro ⟨u, v, huv⟩
    have h1 := congrArg (aeval A) huv
    rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at h1
    apply hA1
    have h2 : A - 1 = 0 := by
      calc A - 1 = (aeval A u * aeval A Φ) * (A - 1) := by rw [h1, one_mul]
        _ = aeval A u * (aeval A Φ * (A - 1)) := by rw [mul_assoc]
        _ = 0 := by rw [hΦA, mul_zero]
    exact sub_eq_zero.mp h2
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F (AlgebraicClosure F)] at hnc
  push Not at hnc
  obtain ⟨ζ, hζΦ, hζχ⟩ := hnc
  have hζr : ζ ^ r = 1 := by
    have h := geom_sum_mul ζ r
    have hs : (∑ i ∈ Finset.range r, ζ ^ i) = 0 := by simpa [hΦdef, map_sum] using hζΦ
    rw [hs, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  refine ⟨ζ, ?_, hζr, hζχ⟩
  rintro rfl
  apply hr
  have hs : (∑ i ∈ Finset.range r, (1 : AlgebraicClosure F) ^ i) = 0 := by
    simpa [hΦdef, map_sum] using hζΦ
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  exact (algebraMap F (AlgebraicClosure F)).injective (by simpa using hs)

theorem aeval_pow_card_eq_zero {F K : Type} [Field F] [Finite F] [Field K] [Algebra F K]
    (P : F[X]) {x : K} (hx : aeval x P = 0) : aeval (x ^ Nat.card F) P = 0 := by
  have := Fintype.ofFinite F
  rw [← Polynomial.expand_aeval, Nat.card_eq_fintype_card, FiniteField.Polynomial.expand_card,
    map_pow, hx, zero_pow Fintype.card_ne_zero]

theorem aeval_inv_charpoly_inv {F K : Type} [Field F] [Field K] [Algebra F K] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsUnit M) {x : K} (hx0 : x ≠ 0)
    (hx : aeval x M.charpoly = 0) : aeval x⁻¹ M⁻¹.charpoly = 0 := by
  have hrev : aeval x⁻¹ M.charpoly.reverse = 0 := by
    have : Invertible x := invertibleOfNonzero hx0
    have h := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap F K) x M.charpoly).mpr
      (by rwa [← aeval_def])
    rwa [invOf_eq_inv, ← aeval_def] at h
  rw [Matrix.charpoly_inv M hM, ← Matrix.reverse_charpoly]
  simp [hrev]

theorem pow_eq_pow_iff_zmod {K : Type} [Field K] {ζ : K} {r : ℕ} (hr : 0 < r) (hζ : ζ ^ r = 1)
    (hord : orderOf ζ = r) (m n : ℕ) : ζ ^ m = ζ ^ n ↔ (m : ZMod r) = n := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, hζ⟩
  rw [hfin.pow_eq_pow_iff_modEq, hord, ZMod.natCast_eq_natCast_iff]

theorem two_ne_zero_zmod {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : (2 : ZMod r) ≠ 0 := by
  intro h2
  have h : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h2
  rw [ZMod.natCast_eq_zero_iff] at h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)

theorem orderOf_card_le_natDegree {F K : Type} [Field F] [Finite F] [Field K] [Algebra F K]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (P : F[X]) (hP : P ≠ 0) {ζ : K} (hζ : ζ ^ r = 1)
    (hζ1 : ζ ≠ 1) (hroot : aeval ζ P = 0)
    (hinv : ∀ x : K, x ≠ 0 → aeval x P = 0 → aeval x⁻¹ P = 0) :
    orderOf ((Nat.card F : ℕ) : ZMod r) ≤ P.natDegree ∧
      (Odd (orderOf ((Nat.card F : ℕ) : ZMod r)) →
        2 * orderOf ((Nat.card F : ℕ) : ZMod r) ≤ P.natDegree) := by
  classical
  have : NeZero r := ⟨hr.ne_zero⟩
  set q := Nat.card F with hq
  set u : ZMod r := (q : ZMod r) with hu
  have hord : orderOf ζ = r := by
    have : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hζ hζ1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at hζ
    exact zero_ne_one hζ
  have hpow := pow_eq_pow_iff_zmod hr.pos hζ hord
  let g : ZMod r → K := fun a => ζ ^ a.val
  have hg_inj : Function.Injective g := by
    intro a b hab
    have := (hpow _ _).mp hab
    simpa [ZMod.natCast_zmod_val] using this
  have hg_frob : ∀ a, g (u * a) = g a ^ q := by
    intro a
    show ζ ^ (u * a).val = (ζ ^ a.val) ^ q
    rw [← pow_mul, hpow, ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]
  have hg_neg : ∀ a, g (-a) = (g a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    show ζ ^ (-a).val * ζ ^ a.val = 1
    rw [← pow_add, ← pow_zero ζ, hpow, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, Nat.cast_zero]
    exact neg_add_cancel a
  have hg_one : g 1 = ζ := by
    have h := (hpow (1 : ZMod r).val 1).mpr (by rw [ZMod.natCast_zmod_val, Nat.cast_one])
    rwa [pow_one] at h
  set S : Finset (ZMod r) := Finset.univ.filter (fun a => aeval (g a) P = 0) with hS
  have hmemS : ∀ a, a ∈ S ↔ aeval (g a) P = 0 := fun a => by simp [hS]
  have hS_card : S.card ≤ P.natDegree := by
    calc S.card = (S.image g).card := (Finset.card_image_of_injective _ hg_inj).symm
      _ ≤ (P.aroots K).toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
          rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
          exact ⟨hP, (hmemS a).mp ha⟩
      _ ≤ Multiset.card (P.aroots K) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots_map_le_natDegree _
  have hS_mul : ∀ a ∈ S, u * a ∈ S := by
    intro a ha
    rw [hmemS] at ha ⊢
    rw [hg_frob]
    exact aeval_pow_card_eq_zero P ha
  have hS_neg : ∀ a ∈ S, -a ∈ S := by
    intro a ha
    rw [hmemS] at ha ⊢
    rw [hg_neg]
    exact hinv _ (pow_ne_zero _ hζ0) ha
  have hS_pow : ∀ j : ℕ, u ^ j ∈ S := by
    intro j
    induction j with
    | zero => simpa [hmemS, hg_one] using hroot
    | succ j ih => rw [pow_succ']; exact hS_mul _ ih
  set k := orderOf u with hk
  set T₁ : Finset (ZMod r) := (Finset.range k).image (fun j => u ^ j) with hT₁
  have hT₁card : T₁.card = k := by
    rw [hT₁, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  have hT₁S : T₁ ⊆ S := by
    intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    exact hS_pow j
  refine ⟨?_, fun hodd => ?_⟩
  · calc k = T₁.card := hT₁card.symm
      _ ≤ S.card := Finset.card_le_card hT₁S
      _ ≤ _ := hS_card
  · set T₂ : Finset (ZMod r) := T₁.image (fun a => -a) with hT₂
    have hT₂card : T₂.card = k :=
      (Finset.card_image_of_injective T₁ neg_injective).trans hT₁card
    have hdisj : Disjoint T₁ T₂ := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha1
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      have hj' : j < k := Finset.mem_range.mp hj
      have hs : u ^ (i + (k - j)) = -1 := by
        have h1 : u ^ k = 1 := pow_orderOf_eq_one u
        have h2 : u ^ j * u ^ (k - j) = 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hj'.le, h1]
        calc u ^ (i + (k - j)) = u ^ i * u ^ (k - j) := pow_add _ _ _
          _ = -(u ^ j * u ^ (k - j)) := by rw [← hba]; ring
          _ = -1 := by rw [h2]
      have hdvd : k ∣ 2 * (i + (k - j)) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [mul_comm, pow_mul, hs]
        norm_num
      have hdvd' : k ∣ i + (k - j) :=
        (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.mpr hodd)).mp hdvd
      have h1 : u ^ (i + (k - j)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
      rw [hs] at h1
      exact two_ne_zero_zmod hr hr2 (by linear_combination (-1 : ZMod r) * h1)
    have hsub : T₁ ∪ T₂ ⊆ S := by
      intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact hT₁S h
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
        exact hS_neg b (hT₁S hb)
    calc 2 * k = (T₁ ∪ T₂).card := by
          rw [Finset.card_union_of_disjoint hdisj, hT₁card, hT₂card]; ring
      _ ≤ S.card := Finset.card_le_card hsub
      _ ≤ _ := hS_card

theorem torus_inversion_bound {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (B : Matrix.GeneralLinearGroup (Fin d) F) (hB : B ^ r = 1)
    (hB1 : B ≠ 1) (hconj : ∃ C : Matrix.GeneralLinearGroup (Fin d) F, C * B * C⁻¹ = B⁻¹) :
    orderOf ((Nat.card F : ℕ) : ZMod r) ≤ d ∧
      (Odd (orderOf ((Nat.card F : ℕ) : ZMod r)) →
        2 * orderOf ((Nat.card F : ℕ) : ZMod r) ≤ d) := by
  classical
  obtain ⟨C, hC⟩ := hconj
  set A : Matrix (Fin d) (Fin d) F := (B : Matrix (Fin d) (Fin d) F) with hA
  have hrF : (r : F) ≠ 0 := by
    intro h
    have h2 : 2 ∣ r := (CharP.cast_eq_zero_iff F 2 r).mp h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h2).symm
  have hAr : A ^ r = 1 := by
    rw [hA, ← Units.val_pow_eq_pow_val, hB]
    rfl
  have hA1 : A ≠ 1 := fun h => hB1 (Units.ext h)
  obtain ⟨ζ, hζ1, hζr, hζχ⟩ := exists_root_charpoly hrF A hAr hA1
  have hconj' : A⁻¹.charpoly = A.charpoly := by
    have h1 := Matrix.charpoly_units_conj C A
    have h2 := congrArg Units.val hC
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.coe_units_inv] at h2
    rw [← hA] at h2
    rw [← h2]
    exact h1
  have hinv : ∀ x : AlgebraicClosure F, x ≠ 0 → aeval x A.charpoly = 0 →
      aeval x⁻¹ A.charpoly = 0 := by
    intro x hx0 hx
    have h := aeval_inv_charpoly_inv A B.isUnit hx0 hx
    rwa [hconj'] at h
  have key := orderOf_card_le_natDegree hr hr2 A.charpoly (Matrix.charpoly_monic A).ne_zero
    hζr hζ1 hζχ hinv
  rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at key

end CFSG.Quasithin.Z4c2
