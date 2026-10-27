module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem

variable {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem c2slomqcr_entry_one (b : Fin n) :
    omqPlusEntry n (1 : spinGroup (quadPlus n F)) b = 1 := by
  change (spinMatrix (quadPlus n F) (1 : spinGroup (quadPlus n F)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl b) (Sum.inl b) = 1
  rw [map_one]
  simp

private theorem c2slomqcr_longCoroot_true (hn : 3 ≤ n) (k : Fin n) (m : Fin n) :
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m true =
      toStdD n (Pi.single k 1) m := by
  rw [toStdD_single_eq (by omega) k]
  cases hσ : rootSignD n k <;>
    simp [longCoroot, hσ, Pi.single_apply]

private theorem c2slomqcr_longCoroot_eq (hn : 3 ≤ n) (k : Fin n) (m : Fin n) (r : Bool) :
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m r =
      boolSign r * toStdD n (Pi.single k 1) m := by
  cases r
  · have h := longCoroot_not (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m true
    rw [show (false : Bool) = !true from rfl, h, c2slomqcr_longCoroot_true (hn := hn),
      boolSign_not, boolSign_true]
    ring
  · rw [c2slomqcr_longCoroot_true (hn := hn), boolSign_true, one_mul]

private theorem c2slomqcr_exponent (hn : 3 ≤ n) (i k : Fin n) :
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)
        (rootIdxD' n i) (!rootSignD n i) +
      longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) (rootIdxD n i) false =
      -cartanD n k i := by
  rw [c2slomqcr_longCoroot_eq hn k (rootIdxD' n i) (!rootSignD n i),
    c2slomqcr_longCoroot_eq hn k (rootIdxD n i) false, boolSign_not, boolSign_false]
  have hcart : cartanD n k i = toStdD n (Pi.single k 1) (rootIdxD n i) +
      boolSign (rootSignD n i) * toStdD n (Pi.single k 1) (rootIdxD' n i) := by
    rw [← coroot_single (cartanD n) k i,
      CFSG.LieType.Steinberg.SpinPlus.coroot_eq_dotProduct (by omega) k (Pi.single i 1),
      toStdD_single_eq (by omega) i]
    simp
  rw [hcart]
  ring

private noncomputable def c2slomqcr_eps (n : ℕ) (i : Fin n) (m : ℕ) : Fin n → ZMod m :=
  fun b => ((toStdD n (Pi.single i 1) b : ℤ) : ZMod m)

private theorem c2slomqcr_eps_labels_eq (hn : 3 ≤ n) (i k : Fin n) (m : ℕ) :
    omqEpsLabels n m (c2slomqcr_eps n i m) k = ((cartanD n k i : ℤ) : ZMod m) := by
  rw [omqEpsLabels]
  have hsum : (∑ b, c2slomqcr_eps n i m b *
      ((toStdD n (Pi.single k 1) b : ℤ) : ZMod m)) =
      ((∑ b, toStdD n (Pi.single i 1) b * toStdD n (Pi.single k 1) b : ℤ) : ZMod m) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [c2slomqcr_eps, ← Int.cast_mul]
  rw [hsum]
  have hdot : (∑ b, toStdD n (Pi.single i 1) b * toStdD n (Pi.single k 1) b) =
      coroot (cartanD n) k (Pi.single i 1) := by
    rw [CFSG.LieType.Steinberg.SpinPlus.coroot_eq_dotProduct (by omega) k (Pi.single i 1)]
    rfl
  rw [hdot, coroot_single]

private theorem c2slomqcr_zpow_labels (hn : 3 ≤ n) (i k : Fin n) (τ : Fˣ) :
    (τ : Fˣ) ^ ((omqEpsLabels n (Nat.card Fˣ) (c2slomqcr_eps n i (Nat.card Fˣ)) k).val) =
      (τ : Fˣ) ^ (cartanD n k i) := by
  haveI : NeZero (Nat.card Fˣ) := ⟨Nat.card_pos.ne'⟩
  have hmod : (((omqEpsLabels n (Nat.card Fˣ) (c2slomqcr_eps n i (Nat.card Fˣ)) k).val : ℤ) ≡
      cartanD n k i [ZMOD Nat.card Fˣ]) := by
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact c2slomqcr_eps_labels_eq hn i k (Nat.card Fˣ)
  have horder : orderOf τ ∣ Nat.card Fˣ := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact pow_card_eq_one'
  have horderZ : (orderOf τ : ℤ) ∣ (Nat.card Fˣ : ℤ) := by exact_mod_cast horder
  have hmod' := hmod.of_dvd horderZ
  rw [← zpow_natCast]
  exact (zpow_eq_zpow_iff_modEq).mpr hmod'

private theorem c2slomqcr_wt_ne_zero (hn : 3 ≤ n) (i : Fin n)
    (h : (omPlusCurtisDatum n F hn).H) :
    omqPlusWt (RingHom.id F) (c2slomqcr_eps n i (Nat.card Fˣ)) (h : spinGroup (quadPlus n F)) ≠
      0 := by
  rw [omqPlusWt]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
    pow_ne_zero _ ((omq_omPlus_H_diagonal (hn := hn) h.2).2 b).1)

private noncomputable def c2slomqcr_char (hn : 3 ≤ n) (i : Fin n) :
    (omPlusCurtisDatum n F hn).H →* Fˣ where
  toFun h := Units.mk0
    (omqPlusWt (RingHom.id F) (c2slomqcr_eps n i (Nat.card Fˣ)) (h : spinGroup (quadPlus n F)))
    (c2slomqcr_wt_ne_zero hn i h)
  map_one' := by
    apply Units.ext
    simp [omqPlusWt, c2slomqcr_entry_one]
  map_mul' := by
    intro g g'
    apply Units.ext
    exact omq_omPlus_wt_mul (hn := hn) (RingHom.id F) (c2slomqcr_eps n i (Nat.card Fˣ))
      g.2 g'.2

private theorem c2slomqcr_char_val (hn : 3 ≤ n) (i : Fin n)
    (h : (omPlusCurtisDatum n F hn).H) :
    ((c2slomqcr_char hn i h : Fˣ) : F) =
      omqPlusWt (RingHom.id F) (c2slomqcr_eps n i (Nat.card Fˣ))
        (h : spinGroup (quadPlus n F)) :=
  rfl

private theorem c2slomqcr_char_torusD (hn : 3 ≤ n) (i k : Fin n) (τ : Fˣ)
    (hx : torusD F hn k τ ∈ (omPlusCurtisDatum n F hn).H) :
    c2slomqcr_char hn i ⟨torusD F hn k τ, hx⟩ = (τ : Fˣ) ^ (cartanD n k i) := by
  apply Units.ext
  rw [c2slomqcr_char_val,
    omq_omPlus_wt_torusD (hn := hn) (m := Nat.card Fˣ) rfl (RingHom.id F)
      (c2slomqcr_eps n i (Nat.card Fˣ)) k τ, RingHom.id_apply]
  simpa using congrArg (fun u : Fˣ => (u : F)) (c2slomqcr_zpow_labels hn i k τ)

include hn in
theorem omq_omPlus_exists_alpha (i : Fin n) :
    ∃ α : (omPlusCurtisDatum n F hn).H →* Fˣ,
      (∀ (h : (omPlusCurtisDatum n F hn).H) (t : F),
        (h : spinGroup (quadPlus n F)) * negRootD F hn i (Multiplicative.ofAdd t) *
            (h : spinGroup (quadPlus n F))⁻¹ =
          negRootD F hn i (Multiplicative.ofAdd (((α h)⁻¹ : Fˣ) * t))) ∧
      ∀ (m : ℕ) {k : Type} [Field k] (ι : F →+* k) (h : (omPlusCurtisDatum n F hn).H),
        m = Nat.card Fˣ →
          ι (((α h : Fˣ)) : F) =
            omqPlusWt ι (fun b => ((toStdD n (Pi.single i 1) b : ℤ) : ZMod m))
              (h : spinGroup (quadPlus n F)) := by
  refine ⟨c2slomqcr_char hn i, ?_, ?_⟩
  · intro h t
    let Hmem : (⨆ k, (torusD F hn k).range) = (omPlusCurtisDatum n F hn).H :=
      (omPlusCurtisDatum_H (K := F) (hn := hn)).symm
    let C : ∀ g : spinGroup (quadPlus n F), g ∈ (⨆ k, (torusD F hn k).range) → Prop :=
      fun g hg => ∀ t : F,
        g * negRootD F hn i (Multiplicative.ofAdd t) * g⁻¹ =
          negRootD F hn i (Multiplicative.ofAdd
            ((((c2slomqcr_char hn i ⟨g, Hmem ▸ hg⟩)⁻¹ : Fˣ) : F) * t))
    have hh : h.1 ∈ ⨆ k, (torusD F hn k).range := by
      rw [← omPlusCurtisDatum_H (K := F) (hn := hn)]
      exact h.2
    have hC : C h.1 hh := by
      refine Subgroup.iSup_induction' (C := C) (fun k => (torusD F hn k).range) ?_ ?_ ?_ hh
      · intro k x hx
        obtain ⟨τ, rfl⟩ := hx
        intro t'
        have hchar := c2slomqcr_char_torusD hn i k τ
          (Hmem ▸ Subgroup.mem_iSup_of_mem k ⟨τ, rfl⟩)
        have hexp := c2slomqcr_exponent hn i k
        have hscal : (((τ ^ (longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)
              (rootIdxD' n i) (!rootSignD n i) +
            longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)
              (rootIdxD n i) false) : Fˣ)) : F) =
            ((((c2slomqcr_char hn i ⟨torusD F hn k τ,
              Hmem ▸ Subgroup.mem_iSup_of_mem k ⟨τ, rfl⟩⟩)⁻¹ : Fˣ)) : F) := by
          rw [hexp, hchar, ← zpow_neg]
        conv_lhs => rw [negRootD, torusD_conj_longRoot]
        conv_rhs => rw [negRootD]
        rw [hscal]
      · intro t'
        simp [Units.val_inv_eq_inv_val, c2slomqcr_char_val, omqPlusWt, c2slomqcr_entry_one]
      · intro x y hx hy ihx ihy t'
        have hchar_mul : c2slomqcr_char hn i ⟨x * y, Hmem ▸ mul_mem hx hy⟩ =
            c2slomqcr_char hn i ⟨x, Hmem ▸ hx⟩ *
              c2slomqcr_char hn i ⟨y, Hmem ▸ hy⟩ := by
          apply Units.ext
          rw [Units.val_mul, c2slomqcr_char_val, c2slomqcr_char_val, c2slomqcr_char_val]
          exact omq_omPlus_wt_mul (hn := hn) (RingHom.id F) (c2slomqcr_eps n i (Nat.card Fˣ))
            (Hmem ▸ hx) (Hmem ▸ hy)
        rw [show (x * y) * negRootD F hn i (Multiplicative.ofAdd t') * (x * y)⁻¹ =
            x * (y * negRootD F hn i (Multiplicative.ofAdd t') * y⁻¹) * x⁻¹ by group,
          ihy t',
          ihx ((↑((c2slomqcr_char hn i ⟨y, Hmem ▸ hy⟩)⁻¹) : F) * t'), hchar_mul]
        have hs : (↑((c2slomqcr_char hn i ⟨x, Hmem ▸ hx⟩)⁻¹) : F) *
            ((↑((c2slomqcr_char hn i ⟨y, Hmem ▸ hy⟩)⁻¹) : F) * t') =
            (↑(((c2slomqcr_char hn i ⟨x, Hmem ▸ hx⟩) *
              (c2slomqcr_char hn i ⟨y, Hmem ▸ hy⟩))⁻¹) : F) * t' := by
          simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev]
          ring
        rw [hs]
    exact hC t
  · intro m k _ ι h hm
    rw [c2slomqcr_char_val]
    subst hm
    simp only [omqPlusWt, RingHom.id_apply]
    rw [map_prod]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    rw [map_pow]
    rfl

end CFSG.LocalAnalysis.WeakClosure81
