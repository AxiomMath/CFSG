module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusMono
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSigned
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusEps

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.StandardType

open scoped Matrix

@[expose] noncomputable def omqPlusEntry (n : ℕ) {F : Type} [Field F] (g : spinGroup (quadPlus n F))
    (b : Fin n) : F :=
  (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b)

@[expose] noncomputable def omqPlusWt {n m : ℕ} {F k : Type} [Field F] [Field k] (ι : F →+* k)
    (ν : Fin n → ZMod m) (g : spinGroup (quadPlus n F)) : k :=
  ∏ b, ι (omqPlusEntry n g b) ^ (ν b).val

variable {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]

private lemma c2slomqpw_spinMatrix_apply (g : spinGroup (quadPlus n F))
    (x y : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y =
      spinAction (quadPlus n F) g (Pi.single y 1) x := by
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]

private lemma c2slomqpw_spinMatrix_mul (g g' : spinGroup (quadPlus n F)) :
    (spinMatrix (quadPlus n F) (g * g') : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (spinMatrix (quadPlus n F) g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  rw [map_mul]
  rfl

private lemma c2slomqpw_torusD_entry_inl {k : Fin n} (τ : Fˣ) (b : Fin n) :
    (spinMatrix (quadPlus n F) (torusD F hn k τ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inl b) (Sum.inl b) =
      ((τ ^ longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b true : Fˣ) : F) := by
  rw [c2slomqpw_spinMatrix_apply, ← plusVec_true n F b, spinAction_torusD]
  simp only [Pi.smul_apply, smul_eq_mul, plusVec_true, Pi.single_eq_same, mul_one]

private lemma c2slomqpw_torusD_entry_inr {k : Fin n} (τ : Fˣ) (b : Fin n) :
    (spinMatrix (quadPlus n F) (torusD F hn k τ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inr b) (Sum.inr b) =
      ((τ ^ longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b false : Fˣ) : F) := by
  rw [c2slomqpw_spinMatrix_apply, ← plusVec_false n F b, spinAction_torusD]
  simp only [Pi.smul_apply, smul_eq_mul, plusVec_false, Pi.single_eq_same, mul_one]

private lemma c2slomqpw_longCoroot_false {k : Fin n} (b : Fin n) :
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b false =
      -longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b true :=
  longCoroot_not (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b true

private def c2slomqpw_diagP (g : spinGroup (quadPlus n F)) : Prop :=
  (∀ x y : Fin n ⊕ Fin n, x ≠ y →
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y = 0) ∧
  (∀ b : Fin n, omqPlusEntry n g b ≠ 0 ∧
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Sum.inr b) (Sum.inr b) = (omqPlusEntry n g b)⁻¹)

private lemma c2slomqpw_diagP_torusD {k : Fin n} (τ : Fˣ) :
    c2slomqpw_diagP (n := n) (F := F) (torusD F hn k τ) := by
  constructor
  · intro x y hxy
    rw [c2slomqpw_spinMatrix_apply]
    rcases y with b | b
    · rw [← plusVec_true n F b, spinAction_torusD]
      simp only [Pi.smul_apply, smul_eq_mul, plusVec_true, Pi.single_apply]
      rw [if_neg hxy, mul_zero]
    · rw [← plusVec_false n F b, spinAction_torusD]
      simp only [Pi.smul_apply, smul_eq_mul, plusVec_false, Pi.single_apply]
      rw [if_neg hxy, mul_zero]
  · intro b
    constructor
    · change (spinMatrix (quadPlus n F) (torusD F hn k τ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) ≠ 0
      rw [c2slomqpw_torusD_entry_inl]
      exact (τ ^ longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b true : Fˣ).ne_zero
    · change (spinMatrix (quadPlus n F) (torusD F hn k τ) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr b) (Sum.inr b) =
          ((spinMatrix (quadPlus n F) (torusD F hn k τ) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b))⁻¹
      rw [c2slomqpw_torusD_entry_inl, c2slomqpw_torusD_entry_inr, c2slomqpw_longCoroot_false,
        zpow_neg]
      simp

private lemma c2slomqpw_diagP_one :
    c2slomqpw_diagP (n := n) (F := F) (1 : spinGroup (quadPlus n F)) := by
  have hM : (spinMatrix (quadPlus n F) (1 : spinGroup (quadPlus n F)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
    rw [map_one]
    rfl
  constructor
  · intro x y hxy
    rw [hM, Matrix.one_apply, if_neg hxy]
  · intro b
    constructor
    · change (spinMatrix (quadPlus n F) (1 : spinGroup (quadPlus n F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) ≠ 0
      rw [hM, Matrix.one_apply, if_pos rfl]
      exact one_ne_zero
    · change (spinMatrix (quadPlus n F) (1 : spinGroup (quadPlus n F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr b) (Sum.inr b) =
          ((spinMatrix (quadPlus n F) (1 : spinGroup (quadPlus n F)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b))⁻¹
      rw [hM, Matrix.one_apply, if_pos rfl, Matrix.one_apply, if_pos rfl, inv_one]

private lemma c2slomqpw_diagP_mul {g g' : spinGroup (quadPlus n F)}
    (hg : c2slomqpw_diagP (n := n) (F := F) g)
    (hg' : c2slomqpw_diagP (n := n) (F := F) g') :
    c2slomqpw_diagP (n := n) (F := F) (g * g') := by
  obtain ⟨hgo, hgd⟩ := hg
  obtain ⟨hg'o, hg'd⟩ := hg'
  have hmul := c2slomqpw_spinMatrix_mul (n := n) (F := F) g g'
  have hdiag : ∀ x : Fin n ⊕ Fin n,
      (spinMatrix (quadPlus n F) (g * g') : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x x =
        (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x x *
          (spinMatrix (quadPlus n F) g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x x := by
    intro x
    rw [hmul, Matrix.mul_apply]
    refine Finset.sum_eq_single x ?_ ?_
    · intro z _ hzx
      rw [hgo x z (Ne.symm hzx), zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  constructor
  · intro x y hxy
    rw [hmul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hzx : z = x
    · rw [hzx, hg'o x y hxy, mul_zero]
    · rw [hgo x z (Ne.symm hzx), zero_mul]
  · intro b
    have hentry : omqPlusEntry n (g * g') b = omqPlusEntry n g b * omqPlusEntry n g' b := by
      change (spinMatrix (quadPlus n F) (g * g') :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) = _
      rw [hdiag (Sum.inl b)]
      rfl
    constructor
    · rw [hentry]
      exact mul_ne_zero (hgd b).1 (hg'd b).1
    · change (spinMatrix (quadPlus n F) (g * g') :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr b) (Sum.inr b) =
          (omqPlusEntry n (g * g') b)⁻¹
      rw [hdiag (Sum.inr b), (hgd b).2, (hg'd b).2, hentry, mul_inv_rev]
      exact mul_comm _ _

include hn in
theorem omq_omPlus_H_diagonal {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) :
    (∀ x y : Fin n ⊕ Fin n, x ≠ y →
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y = 0) ∧
    (∀ b : Fin n, omqPlusEntry n g b ≠ 0 ∧
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Sum.inr b) (Sum.inr b) = (omqPlusEntry n g b)⁻¹) := by
  rw [omPlusCurtisDatum_H (hn := hn)] at hg
  change c2slomqpw_diagP (n := n) (F := F) g
  exact Subgroup.iSup_induction (C := c2slomqpw_diagP (n := n) (F := F))
    (fun k => (torusD F hn k).range) hg
    (fun k x hx => by
      obtain ⟨τ, rfl⟩ := hx
      exact c2slomqpw_diagP_torusD (hn := hn) τ)
    (c2slomqpw_diagP_one (n := n) (F := F))
    (fun x y hx hy => c2slomqpw_diagP_mul hx hy)

include hn in
theorem omq_omPlus_wt_mul {m : ℕ} {k : Type} [Field k] (ι : F →+* k) (ν : Fin n → ZMod m)
    {g g' : spinGroup (quadPlus n F)} (hg : g ∈ (omPlusCurtisDatum n F hn).H)
    (hg' : g' ∈ (omPlusCurtisDatum n F hn).H) :
    omqPlusWt ι ν (g * g') = omqPlusWt ι ν g * omqPlusWt ι ν g' := by
  obtain ⟨hgo, hgd⟩ := omq_omPlus_H_diagonal (hn := hn) hg
  obtain ⟨hg'o, hg'd⟩ := omq_omPlus_H_diagonal (hn := hn) hg'
  have hmul := c2slomqpw_spinMatrix_mul (n := n) (F := F) g g'
  have hentry : ∀ b : Fin n,
      omqPlusEntry n (g * g') b = omqPlusEntry n g b * omqPlusEntry n g' b := by
    intro b
    change (spinMatrix (quadPlus n F) (g * g') :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) = _
    rw [hmul, Matrix.mul_apply]
    refine (Finset.sum_eq_single (Sum.inl b) ?_ ?_).trans ?_
    · intro z _ hz
      rw [hgo (Sum.inl b) z (Ne.symm hz), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (Sum.inl b)) h
    · rfl
  simp only [omqPlusWt, hentry, map_mul, mul_pow]
  exact Finset.prod_mul_distrib

private lemma c2slomqpw_longCoroot_eq_toStdD (hn2 : 2 ≤ n) (k : Fin n) (b : Fin n) :
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) b true =
      toStdD n (Pi.single k 1) b := by
  rw [toStdD_single_eq hn2 k]
  cases h : rootSignD n k <;>
    simp [longCoroot, h, Pi.add_apply, Pi.single_apply, boolSign_true, boolSign_false]

private lemma c2slomqpw_prod_zpow_val {ι : Type*} [Fintype ι] {k : Type} [Field k]
    (u : kˣ) (e : ι → ℤ) (n' : ι → ℕ) :
    ∏ b, ((u : k) ^ (e b)) ^ (n' b) = ((u ^ (∑ b, e b * (n' b : ℤ)) : kˣ) : k) := by
  have hfac : ∀ b, ((u : k) ^ (e b)) ^ (n' b) =
      ((u ^ (e b * (n' b : ℤ)) : kˣ) : k) := by
    intro b
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  have hfac2 : ∀ b, ((u ^ (e b * (n' b : ℤ)) : kˣ) : k) =
      (Units.coeHom k) (u ^ (e b * (n' b : ℤ))) := fun _ => rfl
  simp only [hfac, hfac2]
  rw [← map_prod (Units.coeHom k)]
  exact congrArg (Units.coeHom k)
    (Finset.prod_zpow_eq_zpow_sum Finset.univ u (fun b => e b * (n' b : ℤ)))

include hn in
theorem omq_omPlus_wt_torusD {m : ℕ} (hm : m = Nat.card Fˣ) {k : Type} [Field k] (ι : F →+* k)
    (ν : Fin n → ZMod m) (i : Fin n) (a : Fˣ) :
    omqPlusWt ι ν (torusD F hn i a) = ι (a : F) ^ (omqEpsLabels n m ν i).val := by
  haveI : NeZero m := ⟨by rw [hm]; exact (Nat.card_pos (α := Fˣ)).ne'⟩
  have hpow : ∀ b : Fin n, omqPlusEntry n (torusD F hn i a) b =
      ((a ^ toStdD n (Pi.single i 1) b : Fˣ) : F) := by
    intro b
    change (spinMatrix (quadPlus n F) (torusD F hn i a) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) = _
    rw [c2slomqpw_torusD_entry_inl, c2slomqpw_longCoroot_eq_toStdD (by omega)]
  have hι : ∀ b : Fin n, ι (omqPlusEntry n (torusD F hn i a) b) =
      (ι (a : F)) ^ (toStdD n (Pi.single i 1) b) := by
    intro b
    rw [hpow b, Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hpos : ι (a : F) ≠ 0 := by
    intro h0
    have h1 : ι (a : F) * ι ((a⁻¹ : Fˣ) : F) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  let u : kˣ := Units.mk0 (ι (a : F)) hpos
  have hu : (u : k) = ι (a : F) := Units.val_mk0 hpos
  have hu_m : u ^ m = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hu, ← map_pow, hm,
      ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  have hS : ((∑ b, toStdD n (Pi.single i 1) b * ((ν b).val : ℤ) : ℤ) : ZMod m) =
      omqEpsLabels n m ν i := by
    rw [omqEpsLabels, Int.cast_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
  have hmod : (∑ b, toStdD n (Pi.single i 1) b * ((ν b).val : ℤ)) ≡
      ((omqEpsLabels n m ν i).val : ℤ) [ZMOD (m : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff, hS, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hmod' : (∑ b, toStdD n (Pi.single i 1) b * ((ν b).val : ℤ)) ≡
      ((omqEpsLabels n m ν i).val : ℤ) [ZMOD (orderOf u : ℤ)] := by
    refine Int.ModEq.of_dvd (n := (m : ℤ)) ?_ hmod
    exact_mod_cast orderOf_dvd_iff_pow_eq_one.mpr hu_m
  have hprod : ∏ b, ((u : k) ^ (toStdD n (Pi.single i 1) b)) ^ (ν b).val =
      ((u ^ (∑ b, toStdD n (Pi.single i 1) b * ((ν b).val : ℤ)) : kˣ) : k) :=
    c2slomqpw_prod_zpow_val u (fun b => toStdD n (Pi.single i 1) b) (fun b => (ν b).val)
  calc omqPlusWt ι ν (torusD F hn i a)
      = ∏ b, ((ι (a : F)) ^ (toStdD n (Pi.single i 1) b)) ^ (ν b).val := by
        simp only [omqPlusWt, hι]
    _ = ∏ b, ((u : k) ^ (toStdD n (Pi.single i 1) b)) ^ (ν b).val := by rw [hu]
    _ = ((u ^ (∑ b, toStdD n (Pi.single i 1) b * ((ν b).val : ℤ)) : kˣ) : k) := hprod
    _ = ((u ^ (omqEpsLabels n m ν i).val : kˣ) : k) := by
        rw [zpow_eq_zpow_iff_modEq.mpr hmod', zpow_natCast]
    _ = ι (a : F) ^ (omqEpsLabels n m ν i).val := by
        rw [Units.val_pow_eq_pow_val, hu]

private lemma c2slomqpw_spinMatrix_inv (g : spinGroup (quadPlus n F)) :
    (spinMatrix (quadPlus n F) g⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)⁻¹ := by
  rw [map_inv]
  exact Matrix.GeneralLinearGroup.coe_inv _

private lemma c2slomqpw_mulVec_single (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (x y : Fin n ⊕ Fin n) :
    (A *ᵥ Pi.single y 1) x = A x y := by
  rw [Matrix.mulVec_single_one, Matrix.col_apply]

private lemma c2slomqpw_permMatrix_mulVec_single (ρ : Equiv.Perm (Fin n ⊕ Fin n))
    (x : Fin n ⊕ Fin n) :
    Equiv.Perm.permMatrix F ρ *ᵥ Pi.single x 1 = Pi.single (ρ.symm x) 1 := by
  funext i
  simp only [Matrix.permMatrix_mulVec, Function.comp_apply, Pi.single_apply,
    Equiv.eq_symm_apply]

private lemma c2slomqpw_permMatrix_inv (ρ : Equiv.Perm (Fin n ⊕ Fin n)) :
    (Equiv.Perm.permMatrix F ρ)⁻¹ = Equiv.Perm.permMatrix F ρ.symm := by
  have hmem : ρ.symm * ρ = 1 := by ext x; simp
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.permMatrix_mul (σ := ρ.symm) (τ := ρ), hmem, Matrix.permMatrix_one]

private lemma c2slomqpw_diag_mulVec {D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hD : ∀ x y : Fin n ⊕ Fin n, x ≠ y → D x y = 0) (j : Fin n ⊕ Fin n) :
    D *ᵥ Pi.single j 1 = D j j • Pi.single j 1 := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  refine (Finset.sum_eq_single j ?_ ?_).trans ?_
  · intro z _ hz
    rw [Pi.single_apply, if_neg hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h
  · rw [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · rw [hij, Pi.single_eq_same, mul_one]
    · rw [Pi.single_apply, if_neg hij, mul_zero, hD i j hij]

private lemma c2slomqpw_zpow_eq_pow_of_modEq {k : Type} [Field k] (u : kˣ) {a : ℤ} {b : ℕ}
    (h : a ≡ (b : ℤ) [ZMOD (orderOf u : ℤ)]) :
    ((u ^ a : kˣ) : k) = ((u ^ b : kˣ) : k) := by
  have h1 : u ^ a = u ^ b := (zpow_eq_zpow_iff_modEq.mpr h).trans (zpow_natCast u b)
  rw [h1]

private lemma c2slomqpw_conj_entry {g h : spinGroup (quadPlus n F)}
    {ρ : Equiv.Perm (Fin n ⊕ Fin n)}
    (hMg : (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Equiv.Perm.permMatrix F ρ)
    (hoff : ∀ x y : Fin n ⊕ Fin n, x ≠ y →
      (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y = 0)
    (a : Fin n) :
    (spinMatrix (quadPlus n F) (g⁻¹ * h * g) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl a) (Sum.inl a) =
      (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (ρ.symm (Sum.inl a)) (ρ.symm (Sum.inl a)) := by
  have hMinv : ((spinMatrix (quadPlus n F) g :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))⁻¹ = Equiv.Perm.permMatrix F ρ.symm := by
    rw [hMg, c2slomqpw_permMatrix_inv]
  have hMw : (spinMatrix (quadPlus n F) (g⁻¹ * h * g) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      ((spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))⁻¹ *
        (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [show g⁻¹ * h * g = (g⁻¹ * h) * g from rfl, c2slomqpw_spinMatrix_mul,
      c2slomqpw_spinMatrix_mul, c2slomqpw_spinMatrix_inv]
  have hvec : (spinMatrix (quadPlus n F) (g⁻¹ * h * g) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single (Sum.inl a) 1 =
      (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (ρ.symm (Sum.inl a)) (ρ.symm (Sum.inl a)) • Pi.single (Sum.inl a) 1 := by
    rw [hMw]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hMinv]
    rw [hMg]
    rw [c2slomqpw_permMatrix_mulVec_single]
    rw [c2slomqpw_diag_mulVec hoff]
    rw [Matrix.mulVec_smul]
    rw [c2slomqpw_permMatrix_mulVec_single]
    rw [Equiv.symm_symm, Equiv.apply_symm_apply]
  have hcongr := congrFun hvec (Sum.inl a)
  rw [c2slomqpw_mulVec_single, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hcongr
  exact hcongr

include hn in
theorem omq_omPlus_wt_conj {m : ℕ} (hm : m = Nat.card Fˣ) {k : Type} [Field k] (ι : F →+* k)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hxr : OmRealizes n x π s) (hs : SpIsSign s) (ν : Fin n → ZMod m)
    {h : spinGroup (quadPlus n F)} (hh : h ∈ (omPlusCurtisDatum n F hn).H) :
    ((omPlusCurtisDatum n F hn).nW x)⁻¹ * h * (omPlusCurtisDatum n F hn).nW x ∈
        (omPlusCurtisDatum n F hn).H ∧
      omqPlusWt ι ν (((omPlusCurtisDatum n F hn).nW x)⁻¹ * h * (omPlusCurtisDatum n F hn).nW x) =
        omqPlusWt ι (omqSignedAct π s ν) h := by
  let g : spinGroup (quadPlus n F) := (omPlusCurtisDatum n F hn).nW x
  have hMg : (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Equiv.Perm.permMatrix F (spMonoPerm π s).symm :=
    spinMatrix_nW_omPlusCurtisDatum (hn := hn) hxr hs
  obtain ⟨hoff, hgd⟩ := omq_omPlus_H_diagonal (hn := hn) hh
  have hentry : ∀ a : Fin n, omqPlusEntry n (g⁻¹ * h * g) a =
      (omqPlusEntry n h (π a)) ^ (s a) := by
    intro a
    change (spinMatrix (quadPlus n F) (g⁻¹ * h * g) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl a) (Sum.inl a) =
        (omqPlusEntry n h (π a)) ^ (s a)
    rw [c2slomqpw_conj_entry (g := g) (h := h) (ρ := (spMonoPerm π s).symm) hMg hoff a]
    change (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (spMonoPerm π s (Sum.inl a)) (spMonoPerm π s (Sum.inl a)) =
      (omqPlusEntry n h (π a)) ^ (s a)
    rw [spMonoPerm_inl]
    rcases hs a with hs1 | hs1
    · rw [if_pos hs1, hs1]
      change omqPlusEntry n h (π a) = omqPlusEntry n h (π a) ^ (1 : ℤ)
      rw [zpow_one]
    · rw [if_neg (by rw [hs1]; norm_num), hs1]
      change (spinMatrix (quadPlus n F) h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Sum.inr (π a)) (Sum.inr (π a)) = (omqPlusEntry n h (π a)) ^ (-1 : ℤ)
      rw [(hgd (π a)).2, zpow_neg_one]
  have hwt : omqPlusWt ι ν (g⁻¹ * h * g) = omqPlusWt ι (omqSignedAct π s ν) h := by
    haveI : NeZero m := ⟨by rw [hm]; exact (Nat.card_pos (α := Fˣ)).ne'⟩
    have hιentry : ∀ a : Fin n, ι (omqPlusEntry n (g⁻¹ * h * g) a) =
        (ι (omqPlusEntry n h (π a))) ^ (s a) := by
      intro a
      rw [hentry a, map_zpow₀]
    simp only [omqPlusWt, hιentry]
    trans ∏ a, ((ι (omqPlusEntry n h (π a)) ^ s (π.symm (π a))) ^
      (ν (π.symm (π a))).val : k)
    · refine Finset.prod_congr rfl fun a _ => ?_
      rw [Equiv.symm_apply_apply]
    trans ∏ b, ((ι (omqPlusEntry n h b) ^ s (π.symm b)) ^ (ν (π.symm b)).val : k)
    · exact Equiv.prod_comp π (fun b => (ι (omqPlusEntry n h b) ^ s (π.symm b)) ^
        (ν (π.symm b)).val)
    refine Finset.prod_congr rfl fun b _ => ?_
    let v : Fˣ := Units.mk0 (omqPlusEntry n h b) (hgd b).1
    let u : kˣ := Units.map ι.toMonoidHom v
    have hu : (u : k) = ι (omqPlusEntry n h b) := rfl
    have hv_m : v ^ m = 1 := by rw [hm, pow_card_eq_one']
    have hu_m : u ^ m = 1 := by
      change (Units.map ι.toMonoidHom v) ^ m = 1
      rw [← map_pow, hv_m, map_one]
    have hcast : (((s (π.symm b)) * ((ν (π.symm b)).val : ℤ) : ℤ) : ZMod m) =
        omqSignedAct π s ν b := by
      rw [omqSignedAct, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hmod : (s (π.symm b)) * ((ν (π.symm b)).val : ℤ) ≡
        ((omqSignedAct π s ν b).val : ℤ) [ZMOD (m : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff, hcast, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hmod' : (s (π.symm b)) * ((ν (π.symm b)).val : ℤ) ≡
        ((omqSignedAct π s ν b).val : ℤ) [ZMOD (orderOf u : ℤ)] := by
      refine Int.ModEq.of_dvd (n := (m : ℤ)) ?_ hmod
      exact_mod_cast orderOf_dvd_iff_pow_eq_one.mpr hu_m
    have hfactor : ((u : k) ^ (s (π.symm b))) ^ ((ν (π.symm b)).val) =
        (u : k) ^ ((omqSignedAct π s ν b).val) := by
      rw [← Units.val_zpow_eq_zpow_val, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul,
        ← Units.val_pow_eq_pow_val]
      exact c2slomqpw_zpow_eq_pow_of_modEq u hmod'
    change ((u : k) ^ (s (π.symm b))) ^ ((ν (π.symm b)).val) =
      (u : k) ^ ((omqSignedAct π s ν b).val)
    exact hfactor
  exact ⟨CFSG.Quasithin.SmithCurtis.CurtisDatum.nW_normH (D := omPlusCurtisDatum n F hn) x hh,
    hwt⟩

include hn in
theorem omq_omPlus_wt_injective {m : ℕ} (hm : m = Nat.card Fˣ) (hodd : Odd m) {k : Type}
    [Field k] (ι : F →+* k) {ν ν' : Fin n → ZMod m}
    (h : ∀ g ∈ (omPlusCurtisDatum n F hn).H, omqPlusWt ι ν g = omqPlusWt ι ν' g) : ν = ν' := by
  haveI : NeZero m := ⟨by rw [hm]; exact (Nat.card_pos (α := Fˣ)).ne'⟩
  obtain ⟨a₀, ha₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf a₀ = m :=
    (orderOf_eq_card_of_forall_mem_zpowers ha₀).trans hm.symm
  let f : Fˣ →* kˣ := Units.map ι.toMonoidHom
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : ι (x : F) = ι (y : F) := by
      have := congrArg (fun u : kˣ => (u : k)) hxy
      exact this
    exact Units.ext (ι.injective hxy')
  have hordf : orderOf (f a₀) = m := by
    rw [orderOf_injective f hf_inj a₀, hord]
  apply (omq_labels_bijective (n := n) hn hodd).injective
  funext i
  have hfa : (f a₀ : k) = ι (a₀ : F) := rfl
  have hιa : (ι (a₀ : F)) ^ (omqEpsLabels n m ν i).val =
      (ι (a₀ : F)) ^ (omqEpsLabels n m ν' i).val := by
    rw [← omq_omPlus_wt_torusD (hn := hn) hm ι ν i a₀,
      ← omq_omPlus_wt_torusD (hn := hn) hm ι ν' i a₀]
    exact h (torusD F hn i a₀) (Subgroup.mem_iSup_of_mem i ⟨a₀, rfl⟩)
  have hu : f a₀ ^ (omqEpsLabels n m ν i).val =
      f a₀ ^ (omqEpsLabels n m ν' i).val := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hfa]
    exact hιa
  have hEq : (omqEpsLabels n m ν i).val = (omqEpsLabels n m ν' i).val := by
    have hmod := pow_eq_pow_iff_modEq.mp hu
    rw [hordf] at hmod
    exact Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← ZMod.natCast_zmod_val (omqEpsLabels n m ν i),
    ← ZMod.natCast_zmod_val (omqEpsLabels n m ν' i), hEq]

end CFSG.LocalAnalysis.WeakClosure81
