module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
public import CFSG.Fischer.Classification.PartIII.Arf.Witt
public import CFSG.Fischer.Classification.PartIII.Symp.Gauss

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.SteinbergBV

open Module QuadraticMap CFSG.LieType.Universal.Spin

namespace BinaryTwoParts

theorem factorization_two_pow_mul_odd {k m : ℕ} (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Nat.not_odd_zero hm)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.add_apply, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)), add_zero]

theorem odd_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, Odd (f i)) :
    Odd (∏ i ∈ s, f i) :=
  Finset.prod_induction f Odd (fun _ _ ha hb => ha.mul hb) odd_one h

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_two_pow) ((Nat.even_pow' (by omega)).2 even_two) odd_one

theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) :=
  ((Nat.even_pow' (by omega)).2 even_two).add_odd odd_one

theorem factorization_card_linearEquiv_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {d : ℕ} (hd : finrank (ZMod 2) V = d) :
    (Nat.card (V ≃ₗ[ZMod 2] V)).factorization 2 = d * (d - 1) / 2 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hd
  have h1 : Nat.card (V ≃ₗ[ZMod 2] V) = Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) :=
    (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toEquiv)).symm
  rw [h1, Matrix.card_GL_field, ZMod.card]
  have hprod : ∏ i : Fin d, (2 ^ d - 2 ^ (i : ℕ)) =
      2 ^ (∑ i : Fin d, (i : ℕ)) * ∏ i : Fin d, (2 ^ (d - i) - 1) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' i.2.le]
  rw [hprod, factorization_two_pow_mul_odd (odd_finset_prod _ _ fun i _ =>
      odd_two_pow_sub_one (by have := i.2; omega)),
    Fin.sum_univ_eq_sum_range (fun i => i) d, Finset.sum_range_id]

theorem factorization_card_isometryGroup_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {n : ℕ} (hd : finrank (ZMod 2) V = 2 * n)
    (β : LinearMap.BilinForm (ZMod 2) V) (hβ : β.IsAlt) (hnd : β.Nondegenerate) :
    (Nat.card (TauCeti.BilinForm.isometryGroup β)).factorization 2 = n ^ 2 := by
  rw [ComponentInitial.SymplecticFlag.card_isometryGroup n β hβ hnd hd, Nat.card_zmod]
  exact factorization_two_pow_mul_odd (odd_finset_prod _ _ fun j hj =>
    odd_two_pow_sub_one (by have := (Finset.mem_Icc.1 hj).1; omega))

theorem ncard_eq_one_add_card_eq_zero {W : Type*} [Finite W] (f : W → ZMod 2) :
    {w | f w = 1}.ncard + Nat.card {w // f w = 0} = Nat.card W := by
  have hc : {w | f w = 1} = {w | f w = 0}ᶜ := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · intro h h0
      rw [h0] at h
      exact zero_ne_one h
    · intro h
      have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact key _ h
  have h0 : Nat.card {w // f w = 0} = ({w | f w = 0} : Set W).ncard := Nat.card_coe_set_eq _
  rw [hc, h0, add_comm, Set.ncard_add_ncard_compl]

theorem two_mul_ncard_quadPlus (m : ℕ) :
    2 * {v | quadPlus (m + 1) (ZMod 2) v = 1}.ncard + 2 ^ (m + 1) = 4 ^ (m + 1) := by
  have h1 := ncard_eq_one_add_card_eq_zero (quadPlus (m + 1) (ZMod 2))
  have h2 := (Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) m).1
  simp only [Nat.card_zmod, Nat.cast_ofNat] at h2
  have hW : Nat.card (Fin (m + 1) ⊕ Fin (m + 1) → ZMod 2) = 4 ^ (m + 1) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← two_mul, pow_mul]
    norm_num
  rw [hW] at h1
  have h1' : (({v | quadPlus (m + 1) (ZMod 2) v = 1}.ncard : ℕ) : ℤ) +
      (Nat.card {v // quadPlus (m + 1) (ZMod 2) v = 0} : ℤ) = 4 ^ (m + 1) := by
    exact_mod_cast h1
  rw [h2] at h1'
  have e4 : (4 : ℤ) ^ (m + 1) = ((2 : ℤ) ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e2 : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by rw [pow_succ, mul_comm]
  have : (2 * ({v | quadPlus (m + 1) (ZMod 2) v = 1}.ncard : ℤ) + 2 ^ (m + 1) : ℤ) =
      4 ^ (m + 1) := by
    linear_combination 2 * h1' + e4 + ((2 : ℤ) ^ (m + 1) - 1) * e2
  exact_mod_cast this

theorem two_mul_ncard_quadMinus (m : ℕ) :
    2 * {v | quadMinus (m + 1) (ZMod 2) 1 1 v = 1}.ncard = 4 ^ (m + 1) + 2 ^ (m + 1) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have h1 := ncard_eq_one_add_card_eq_zero (quadMinus (m + 1) (ZMod 2) 1 1)
  have h2 := (Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) m hirr).1
  simp only [Nat.card_zmod, Nat.cast_ofNat] at h2
  have hW : Nat.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → ZMod 2) = 4 ^ (m + 1) := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_sum, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel, show m + (m + 2) = 2 * (m + 1) by ring, pow_mul]
    norm_num
  rw [hW] at h1
  have h1' : (({v | quadMinus (m + 1) (ZMod 2) 1 1 v = 1}.ncard : ℕ) : ℤ) +
      (Nat.card {v // quadMinus (m + 1) (ZMod 2) 1 1 v = 0} : ℤ) = 4 ^ (m + 1) := by
    exact_mod_cast h1
  rw [h2] at h1'
  have e4 : (4 : ℤ) ^ (m + 1) = ((2 : ℤ) ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e2 : (2 : ℤ) ^ (m + 1) = 2 * (2 : ℤ) ^ m := by rw [pow_succ, mul_comm]
  have : (2 * ({v | quadMinus (m + 1) (ZMod 2) 1 1 v = 1}.ncard : ℤ) : ℤ) =
      4 ^ (m + 1) + 2 ^ (m + 1) := by
    linear_combination 2 * h1' + e4 + ((2 : ℤ) ^ (m + 1) + 1) * e2
  exact_mod_cast this

theorem factorization_card_orthogonalGroup_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {n : ℕ} (hn : 1 ≤ n) (hd : finrank (ZMod 2) V = 2 * n)
    (q : QuadraticForm (ZMod 2) V) (hq : (polarBilin q).Nondegenerate) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup q)).factorization 2 = n * (n - 1) + 1 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hcardV : Nat.card V = 4 ^ (m + 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod, hd, pow_mul]
    norm_num
  have hnd : ∀ x, (∀ y, polar q x y = 0) → x = 0 := fun x hx => hq.1 x fun y => hx y
  have hodd : ∀ k, Odd (∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i) - 1)) := fun k =>
    odd_finset_prod _ _ fun i hi => odd_two_pow_sub_one (by have := (Finset.mem_Icc.1 hi).1; omega)
  have hexp : (m + 1) * (m + 1 - 1) + 1 = m * (m + 1) + 1 := by
    rw [Nat.add_sub_cancel, mul_comm]
  rw [hexp]
  rcases Fischer.Classification.LocalSymp.two_mul_ncard_quadratic q hnd hcardV with h | h
  ·
    have hP := two_mul_ncard_quadPlus m
    have hN : {v | q v = 1}.ncard = {v | quadPlus (m + 1) (ZMod 2) v = 1}.ncard := by
      generalize 2 ^ (m + 1) = P at h hP
      generalize 4 ^ (m + 1) = F at h hP
      omega
    have hWP : Nat.card V = Nat.card (Fin (m + 1) ⊕ Fin (m + 1) → ZMod 2) := by
      rw [hcardV, Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_eq_fintype_card,
        Fintype.card_fin, ← two_mul, pow_mul]
      norm_num
    obtain ⟨L, hL⟩ := Fischer.Classification.exists_linearEquiv_of_ncard_eq q
      (quadPlus (m + 1) (ZMod 2)) hnd
      (fun x hx => (nondegenerate_polarBilin_quadPlus (m + 1) (ZMod 2)).1 x fun y => hx y) hWP hN
    let e : q.IsometryEquiv (quadPlus (m + 1) (ZMod 2)) := { L with map_app' := hL }
    rw [Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e]
    have hO := (Timmesfeld.ClassicalOrders.card_quadPlus (K := ZMod 2) m).2
    simp only [Nat.card_zmod, Nat.cast_ofNat] at hO
    have hOnat : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) (ZMod 2))) =
        2 ^ (m * (m + 1) + 1) * ((2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1)) := by
      apply Nat.cast_injective (R := ℤ)
      rw [hO]
      push_cast [Nat.one_le_two_pow]
      ring
    rw [hOnat]
    exact factorization_two_pow_mul_odd ((odd_two_pow_sub_one (by omega)).mul (hodd m))
  ·
    have hM := two_mul_ncard_quadMinus m
    have hN : {v | q v = 1}.ncard = {v | quadMinus (m + 1) (ZMod 2) 1 1 v = 1}.ncard := by
      generalize 2 ^ (m + 1) = P at h hM
      generalize 4 ^ (m + 1) = F at h hM
      omega
    have hWM : Nat.card V = Nat.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → ZMod 2) := by
      rw [hcardV, Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_sum,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
        Fintype.card_fin, Nat.add_sub_cancel, show m + (m + 2) = 2 * (m + 1) by ring, pow_mul]
      norm_num
    have hbc : (1 : ZMod 2) ^ 2 - 4 * 1 ≠ 0 := by decide
    obtain ⟨L, hL⟩ := Fischer.Classification.exists_linearEquiv_of_ncard_eq q
      (quadMinus (m + 1) (ZMod 2) 1 1) hnd
      (fun x hx => (nondegenerate_polarBilin_quadMinus (n := m + 1) (K := ZMod 2) hbc).1 x
        fun y => hx y) hWM hN
    let e : q.IsometryEquiv (quadMinus (m + 1) (ZMod 2) 1 1) := { L with map_app' := hL }
    rw [Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e]
    have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
    have hO := (Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) m hirr).2
    simp only [Nat.card_zmod, Nat.cast_ofNat] at hO
    have hOnat :
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) (ZMod 2) 1 1)) =
          2 ^ (m * (m + 1) + 1) *
            ((2 ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1)) := by
      apply Nat.cast_injective (R := ℤ)
      rw [hO]
      push_cast [Nat.one_le_two_pow]
      ring
    rw [hOnat]
    exact factorization_two_pow_mul_odd ((odd_two_pow_add_one (by omega)).mul (hodd m))

end BinaryTwoParts

open BinaryTwoParts in

theorem binary_linear_and_form_isometry_group_two_parts {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {d : ℕ} (hd : finrank (ZMod 2) V = d) :
    ordProj[2] (Nat.card (V ≃ₗ[ZMod 2] V)) = 2 ^ (d * (d - 1) / 2) ∧
    (∀ n : ℕ, d = 2 * n → ∀ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt → β.Nondegenerate →
      ordProj[2] (Nat.card (TauCeti.BilinForm.isometryGroup β)) = 2 ^ (n ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → d = 2 * n → ∀ q : QuadraticForm (ZMod 2) V, (polarBilin q).Nondegenerate →
      ordProj[2] (Nat.card (TauCeti.QuadraticMap.orthogonalGroup q)) =
        2 ^ (n * (n - 1) + 1)) := by
  refine ⟨by rw [factorization_card_linearEquiv_two hd], fun n hn β hβ hnd => ?_,
    fun n hn1 hn q hq => ?_⟩
  · rw [factorization_card_isometryGroup_two (hd.trans hn) β hβ hnd]
  · rw [factorization_card_orthogonalGroup_two hn1 (hd.trans hn) q hq]

end CFSG.LocalAnalysis.SteinbergBV
