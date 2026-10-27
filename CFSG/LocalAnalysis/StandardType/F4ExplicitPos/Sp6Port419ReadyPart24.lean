module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart23

@[expose] public section

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley IsNilpotent
open scoped Nat
open scoped commutatorElement
variable {τ : Tag}

namespace RootOperatorFamily'
variable {D : AdjData τ}

theorem comm_rat_of_not_isRoot_two_add_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R]
    {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (h : IsRoot τ (α.1 + β.1))
    (h21 : ¬IsRoot τ (2 • α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      F.elt R ⟨_, h⟩ ((coeff11_without117 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : R) * c * d ^ 2) := by
  have hli := linIndepPair_of_ne α.2 β.2 hne hne'
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hz' := bracket_smul_without117 F hD hβα h c d
  have hγα : α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 1) (k :=
      1) (l := 0)
    (by omega) (by simp) (by simp)
  have hαγ : ¬IsRoot τ (α.1 + (α.1 + β.1)) := by
    rwa [show α.1 + (α.1 + β.1) = 2 • α.1 + β.1 by rw [two_nsmul]; abel]
  have haz := commute_smul_without117 F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ c
    (c * d * bracketCoeff_without117 F hD α β)
  rw [elt_eq_exp_without117 F, elt_eq_exp_without117 F, elt_eq_exp_without117 F,
      elt_eq_exp_without117 F, neg_smul, neg_smul,
    elt_eq_exp_without117 F]
  have hγβ : α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 1) (k :=
      0) (l := 1)
    (by omega) (by simp) (by simp)
  have hβγeq : β.1 + (α.1 + β.1) = α.1 + 2 • β.1 := by rw [two_nsmul]; abel
  by_cases h12 : IsRoot τ (α.1 + 2 • β.1)
  · have hβγ : IsRoot τ (β.1 + (α.1 + β.1)) := by rwa [hβγeq]
    have hw' := bracket_smul_without117 F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d
      (c * d * bracketCoeff_without117 F hD α β)
    rw [D_congr_without117 F (show (⟨_, hβγ⟩ : Root τ).1 = (⟨_, h12⟩ : Root τ).1 from hβγeq)] at hw'
    have hγ'α : α.1 + 2 • β.1 ≠ -α.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 2) (k :=
        1)
      (l := 0) (by omega) (by simp) (by simp)
    have hαγ' : ¬IsRoot τ (α.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 2) (by omega)
        (by omega) (by omega)
      rwa [show 2 • α.1 + 2 • β.1 = α.1 + (α.1 + 2 • β.1) by rw [two_nsmul α.1]; abel] at this
    have hγ'γ : α.1 + 2 • β.1 ≠ -(α.1 + β.1) := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 2)
      (k := 1) (l := 1) (by omega) (by simp) (by simp)
    have hγγ' : ¬IsRoot τ (α.1 + β.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 3) (by omega)
        (by omega) (by omega)
      rwa [show 2 • α.1 + 3 • β.1 = α.1 + β.1 + (α.1 + 2 • β.1) by
        rw [two_nsmul α.1, show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel] at this
    have hγ'β : α.1 + 2 • β.1 ≠ -β.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 2) (k :=
        0)
      (l := 1) (by omega) (by simp) (by simp)
    have hβγ' : ¬IsRoot τ (β.1 + (α.1 + 2 • β.1)) := by
      have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 1) (j := 3) (by omega)
        (by omega) (by omega)
      rwa [show 1 • α.1 + 3 • β.1 = β.1 + (α.1 + 2 • β.1) by
        rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, one_nsmul]; abel] at this
    have hN' : bracketCoeff_without117 F hD β ⟨_, h⟩ = 2 ∨ bracketCoeff_without117 F hD β ⟨_,
        h⟩ = -2 := by
      have := bracketCoeff_natAbs_without117 F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ
      rw [stringNorm_of_isRoot_without117 (by simpa using α.2)] at this
      omega
    rw [commutator_exp (isNilpotent_smul_D_without117 F α c) (isNilpotent_smul_D_without117 F β d)
        (isNilpotent_smul_D_without117 F ⟨_, h⟩ _) (isNilpotent_smul_D_without117 F ⟨_,
            h12⟩ _) hz' hw' haz
        (commute_smul_without117 F hD (β := α) (γ := ⟨_, h12⟩) hγ'α hαγ' c _)
        (commute_smul_without117 F hD (β := ⟨_, h⟩) (γ := ⟨_, h12⟩) hγ'γ hγγ' _ _)
        (commute_smul_without117 F hD (β := β) (γ := ⟨_, h12⟩) hγ'β hβγ' d _),
      eltOr_of_isRoot_without117 F R h12, elt_eq_exp_without117 F, coeff12_without117,
          dite_eq_left h, coeff11_without117]
    congr 2
    · ring_nf
    · rcases hN' with hN' | hN' <;> rw [hN']
      · rw [show bracketCoeff_without117 F hD α β * 2 / 2 = bracketCoeff_without117 F hD α
          β by omega,
          show d * (c * d * (bracketCoeff_without117 F hD α β : R)) * ((2 : ℤ) : R) =
            2 * ((bracketCoeff_without117 F hD α β : R) * c * d ^ 2) by push_cast; ring_nf,
          two_inv_smul_two_mul_smul_without117]
      · rw [show bracketCoeff_without117 F hD α β * -2 / 2 = -bracketCoeff_without117 F hD α
          β by omega,
          show d * (c * d * (bracketCoeff_without117 F hD α β : R)) * ((-2 : ℤ) : R) =
            2 * (((-bracketCoeff_without117 F hD α β : ℤ) : R) * c * d ^ 2) by push_cast; ring_nf,
          two_inv_smul_two_mul_smul_without117]
  · have hβγ : ¬IsRoot τ (β.1 + (α.1 + β.1)) := by rwa [hβγeq]
    have hbz := commute_smul_without117 F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d
      (c * d * bracketCoeff_without117 F hD α β)
    rw [commutator_exp (w := 0) (isNilpotent_smul_D_without117 F α c)
        (isNilpotent_smul_D_without117 F β d)
        (isNilpotent_smul_D_without117 F ⟨_, h⟩ _) IsNilpotent.zero hz'
            (by rw [hbz.eq, sub_self]) haz
        (Commute.zero_right _) (Commute.zero_right _) (Commute.zero_right _),
      eltOr_of_not_isRoot_without117 F R h12, smul_zero, exp_zero, mul_one, mul_one,
          coeff11_without117]
    congr 2
    ring

theorem comm_rat_of_isRoot_two_add_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R]
    {α β : Root τ} (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (h : IsRoot τ (α.1 + β.1))
    (h21 : IsRoot τ (2 • α.1 + β.1)) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      F.elt R ⟨_, h⟩ ((coeff11_without117 F hD α β : R) * c * d) *
        F.elt R ⟨_, h21⟩ ((coeff21_without117 F hD α β : R) * c ^ 2 * d) := by
  have hli := linIndepPair_of_ne α.2 β.2 hne hne'
  have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
    not_isRoot_add_two_and_two_add hτ α.2 β.2 hne hne' ⟨h12, h21⟩
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have hz' := bracket_smul_without117 F hD hβα h c d
  have hγα : α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 1) (k :=
      1) (l := 0)
    (by omega) (by simp) (by simp)
  have hαγeq : α.1 + (α.1 + β.1) = 2 • α.1 + β.1 := by rw [two_nsmul]; abel
  have hαγ : IsRoot τ (α.1 + (α.1 + β.1)) := by rwa [hαγeq]
  have hu' := bracket_smul_without117 F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ c
    (c * d * bracketCoeff_without117 F hD α β)
  rw [D_congr_without117 F (show (⟨_, hαγ⟩ : Root τ).1 = (⟨_, h21⟩ : Root τ).1 from hαγeq)] at hu'
  have hγβ : α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep'_without117 hli (i := 1) (j := 1) (k :=
      0) (l := 1)
    (by omega) (by simp) (by simp)
  have hβγ : ¬IsRoot τ (β.1 + (α.1 + β.1)) := by
    rwa [show β.1 + (α.1 + β.1) = α.1 + 2 • β.1 by rw [two_nsmul]; abel]
  have hγ''β : 2 • α.1 + β.1 ≠ -β.1 := ne_neg_of_linIndep'_without117 hli (i := 2) (j := 1) (k := 0)
    (l := 1) (by omega) (by simp) (by simp)
  have hβγ'' : ¬IsRoot τ (β.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 2) (j := 2) (by omega)
      (by omega) (by omega)
    rwa [show 2 • α.1 + 2 • β.1 = β.1 + (2 • α.1 + β.1) by rw [two_nsmul β.1]; abel] at this
  have hγ''γ : 2 • α.1 + β.1 ≠ -(α.1 + β.1) := ne_neg_of_linIndep'_without117 hli (i := 2) (j := 1)
    (k := 1) (l := 1) (by omega) (by simp) (by simp)
  have hγγ'' : ¬IsRoot τ (α.1 + β.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 3) (j := 2) (by omega)
      (by omega) (by omega)
    rwa [show 3 • α.1 + 2 • β.1 = α.1 + β.1 + (2 • α.1 + β.1) by
      rw [two_nsmul β.1, show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul]; abel] at this
  have hγ''α : 2 • α.1 + β.1 ≠ -α.1 := ne_neg_of_linIndep'_without117 hli (i := 2) (j := 1) (k := 1)
    (l := 0) (by omega) (by simp) (by simp)
  have hαγ'' : ¬IsRoot τ (α.1 + (2 • α.1 + β.1)) := by
    have := not_isRoot_nsmul_add_nsmul hτ α.2 β.2 hne hne' (i := 3) (j := 1) (by omega)
      (by omega) (by omega)
    rwa [show 3 • α.1 + 1 • β.1 = α.1 + (2 • α.1 + β.1) by
      rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul, one_nsmul, one_nsmul]; abel] at this
  have hN'' : bracketCoeff_without117 F hD α ⟨_, h⟩ = 2 ∨ bracketCoeff_without117 F hD α ⟨_,
      h⟩ = -2 := by
    have := bracketCoeff_natAbs_without117 F hD (β := α) (γ := ⟨_, h⟩) hγα hαγ
    rw [stringNorm_of_isRoot_without117 (by simpa using β.2)] at this
    omega
  rw [elt_eq_exp_without117 F, elt_eq_exp_without117 F, elt_eq_exp_without117 F,
      elt_eq_exp_without117 F, neg_smul, neg_smul,
    commutator_exp' (isNilpotent_smul_D_without117 F α c) (isNilpotent_smul_D_without117 F β d)
      (isNilpotent_smul_D_without117 F ⟨_, h⟩ _) (isNilpotent_smul_D_without117 F ⟨_,
          h21⟩ _) hz' hu'
      (commute_smul_without117 F hD (β := β) (γ := ⟨_, h⟩) hγβ hβγ d _)
      (commute_smul_without117 F hD (β := β) (γ := ⟨_, h21⟩) hγ''β hβγ'' d _)
      (commute_smul_without117 F hD (β := ⟨_, h⟩) (γ := ⟨_, h21⟩) hγ''γ hγγ'' _ _)
      (commute_smul_without117 F hD (β := α) (γ := ⟨_, h21⟩) hγ''α hαγ'' c _),
    elt_eq_exp_without117 F, elt_eq_exp_without117 F, coeff21_without117, dite_eq_left h,
        coeff11_without117]
  congr 2
  · ring_nf
  · rcases hN'' with hN'' | hN'' <;> rw [hN'']
    · rw [show bracketCoeff_without117 F hD α β * 2 / 2 = bracketCoeff_without117 F hD α β by omega,
        show c * (c * d * (bracketCoeff_without117 F hD α β : R)) * ((2 : ℤ) : R) =
          2 * ((bracketCoeff_without117 F hD α β : R) * c ^ 2 * d) by push_cast; ring_nf,
        two_inv_smul_two_mul_smul_without117]
    · rw [show bracketCoeff_without117 F hD α β * -2 / 2 = -bracketCoeff_without117 F hD α
        β by omega,
        show c * (c * d * (bracketCoeff_without117 F hD α β : R)) * ((-2 : ℤ) : R) =
          2 * (((-bracketCoeff_without117 F hD α β : ℤ) : R) * c ^ 2 * d) by push_cast; ring_nf,
        two_inv_smul_two_mul_smul_without117]

theorem comm_rat_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    (hτ : NoG2 τ) {R : Type} [CommRing R] [Algebra ℚ R] {α β : Root τ}
    (hne : α.1 ≠ β.1) (hne' : α.1 ≠ -β.1) (c d : R) :
    F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d) =
      eltOr F R (α.1 + β.1) ((coeff11_without117 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : R) * c * d ^ 2) *
          eltOr F R (2 • α.1 + β.1) ((coeff21_without117 F hD α β : R) * c ^ 2 * d) := by
  by_cases h : IsRoot τ (α.1 + β.1)
  · by_cases h21 : IsRoot τ (2 • α.1 + β.1)
    · have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
        not_isRoot_add_two_and_two_add hτ α.2 β.2 hne hne' ⟨h12, h21⟩
      rw [comm_rat_of_isRoot_two_add_without117 F hD hτ hne hne' h h21,
          eltOr_of_isRoot_without117 F R h,
        eltOr_of_not_isRoot_without117 F R h12, eltOr_of_isRoot_without117 F R h21, mul_one]
    · rw [comm_rat_of_not_isRoot_two_add_without117 F hD hτ hne hne' h h21,
        eltOr_of_isRoot_without117 F R h,
        eltOr_of_not_isRoot_without117 F R h21, mul_one]
  · have h12 : ¬IsRoot τ (α.1 + 2 • β.1) := fun h12 =>
      h (isRoot_add_of_isRoot_add_two_smul β.2 α.2 hne hne' h12)
    have h21 : ¬IsRoot τ (2 • α.1 + β.1) := fun h21 => h (by
      rw [add_comm]
      exact isRoot_add_of_isRoot_add_two_smul α.2 β.2 (Ne.symm hne)
        (fun h' => hne' (by rw [h', neg_neg])) (by rwa [add_comm]))
    rw [comm_rat_of_not_isRoot_add_without117 F hD hne' h, eltOr_of_not_isRoot_without117 F R h,
      eltOr_of_not_isRoot_without117 F R h12, eltOr_of_not_isRoot_without117 F R h21, mul_one,
          mul_one]

theorem baseChange_eltOr_without117
    (F : RootOperatorFamily τ) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (γ : Fin τ.rank → ℤ) (x : R) : BaseChange f (eltOr F R γ x) (eltOr F S γ (f x)) := by
  by_cases h : IsRoot τ γ
  · rw [eltOr_of_isRoot_without117 F R h, eltOr_of_isRoot_without117 F S h]
    exact BaseChange.elt_without117 F _ x
  · rw [eltOr_of_not_isRoot_without117 F R h, eltOr_of_not_isRoot_without117 F S h]
    exact BaseChange.one_without117

theorem baseChange_comm_lhs_without117
    (F : RootOperatorFamily τ) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (α β : Root τ) (c d : R) :
    BaseChange f (F.elt R α c * F.elt R β d * F.elt R α (-c) * F.elt R β (-d))
      (F.elt S α (f c) * F.elt S β (f d) * F.elt S α (-f c) * F.elt S β (-f d)) := by
  have h3 := BaseChange.elt_without117 F (f := f) α (-c)
  have h4 := BaseChange.elt_without117 F (f := f) β (-d)
  rw [map_neg] at h3 h4
  exact BaseChange.mul_without117 (BaseChange.mul_without117
    (BaseChange.mul_without117 (BaseChange.elt_without117 F α c) (BaseChange.elt_without117 F β d))
        h3) h4

theorem baseChange_comm_rhs_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (α β : Root τ) (c d : R) :
    BaseChange f (eltOr F R (α.1 + β.1) ((coeff11_without117 F hD α β : R) * c * d) *
        eltOr F R (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : R) * c * d ^ 2) *
          eltOr F R (2 • α.1 + β.1) ((coeff21_without117 F hD α β : R) * c ^ 2 * d))
      (eltOr F S (α.1 + β.1) ((coeff11_without117 F hD α β : S) * f c * f d) *
        eltOr F S (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : S) * f c * f d ^ 2) *
          eltOr F S (2 • α.1 + β.1) ((coeff21_without117 F hD α β : S) * f c ^ 2 * f d)) := by
  have h1 := baseChange_eltOr_without117 F f (α.1 + β.1) ((coeff11_without117 F hD α β : R) * c * d)
  have h2 := baseChange_eltOr_without117 F f (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : R) * c
      * d ^ 2)
  have h3 := baseChange_eltOr_without117 F f (2 • α.1 + β.1) ((coeff21_without117 F hD α β : R) * c
      ^ 2 * d)
  simp only [map_mul, map_pow, map_intCast] at h1 h2 h3
  exact BaseChange.mul_without117 (BaseChange.mul_without117 h1 h2) h3

open MvPolynomial in
theorem comm_formula_without117
    (F : RootOperatorFamily τ) (hD : D.Valid)
    (hτ : NoG2 τ) {S : Type} [CommRing S] {α β : Root τ} (hne : α.1 ≠ β.1)
    (hne' : α.1 ≠ -β.1) (c d : S) :
    F.elt S α c * F.elt S β d * F.elt S α (-c) * F.elt S β (-d) =
      eltOr F S (α.1 + β.1) ((coeff11_without117 F hD α β : S) * c * d) *
        eltOr F S (α.1 + 2 • β.1) ((coeff12_without117 F hD α β : S) * c * d ^ 2) *
          eltOr F S (2 • α.1 + β.1) ((coeff21_without117 F hD α β : S) * c ^ 2 * d) := by
  set f₀ : MvPolynomial (Fin 2) ℤ →+* MvPolynomial (Fin 2) ℚ := map (Int.castRingHom ℚ)
  have hf₀ : Function.Injective f₀ := map_injective _ Int.cast_injective
  have hX : ∀ i, f₀ (X i) = X i := fun i => map_X _ i
  have hl₀ := baseChange_comm_lhs_without117 F f₀ α β (X 0) (X 1)
  have hr₀ := baseChange_comm_rhs_without117 F hD f₀ α β (X 0) (X 1)
  rw [hX, hX] at hl₀ hr₀
  rw [← comm_rat_without117 (R := MvPolynomial (Fin 2) ℚ) F hD hτ hne hne'] at hr₀
  have huniv := BaseChange.eq_of_injective_without117 hf₀ hl₀ hr₀
  set g : MvPolynomial (Fin 2) ℤ →+* S := eval₂Hom (Int.castRingHom S) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hl := baseChange_comm_lhs_without117 F g α β (X 0) (X 1)
  have hr := baseChange_comm_rhs_without117 F hD g α β (X 0) (X 1)
  rw [hg0, hg1] at hl hr
  rw [huniv] at hl
  exact BaseChange.unique_without117 hl hr

end RootOperatorFamily'

theorem natAbs_div_two_of_natAbs_eq_two_without117 {m : ℤ} (h : m.natAbs = 2) :
    (m / 2).natAbs = 1 := by
  rcases Int.natAbs_eq_iff.1 h with rfl | rfl <;> decide

theorem not_isRoot_sub_of_iform_without117
    (hτ : NoG2 τ) {α β : Fin τ.rank → ℤ}
    (h : iform α α + iform β β = 6) (hαβ : iform α β = -2) : ¬IsRoot τ (β - α) := fun hr => by
  have h2 := iform_self_cases hτ hr
  simp only [iform_sub_left, iform_sub_right] at h2
  rw [iform_comm β α] at h2
  omega

namespace RootOperatorFamily'

variable {D : AdjData τ}

theorem natAbs_coeff12_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (hτ : NoG2 τ) {α β : Root τ} (hne : α.1 ≠ β.1)
    (hne' : α.1 ≠ -β.1) (h : IsRoot τ (α.1 + 2 • β.1)) :
    (coeff12_without117 F hD α β).natAbs = 1 := by
  have h1 : IsRoot τ (α.1 + β.1) := isRoot_add_of_isRoot_add_two_smul β.2 α.2 hne hne' h
  have h' : IsRoot τ (1 • α.1 + 2 • β.1) := by rwa [one_smul]
  obtain ⟨hαα, hββ, hαβ⟩ : iform α.1 α.1 = 4 ∧ iform β.1 β.1 = 2 ∧ iform α.1 β.1 = -2 := by
    rcases exponent_pair_cases hτ α.2 β.2 hne hne' le_rfl (by norm_num) h' with h | h | h
    · omega
    · exact h.2.2
    · omega
  have hn : ¬IsRoot τ (β.1 - α.1) := not_isRoot_sub_of_iform_without117 hτ (by omega) hαβ
  have hN1 : (bracketCoeff_without117 F hD α β).natAbs = 1 := by
    rw [bracketCoeff_natAbs_without117 F hD (fun h' => hne' (by rw [h', neg_neg])) h1,
      stringNorm_of_not_isRoot_without117 hn]
  have hsum : β.1 + (α.1 + β.1) = α.1 + 2 • β.1 := by rw [two_nsmul]; abel
  have hN2 : (bracketCoeff_without117 F hD β ⟨α.1 + β.1, h1⟩).natAbs = 2 := by
    rw [bracketCoeff_natAbs_without117 F hD (γ := ⟨α.1 + β.1, h1⟩)
        (fun h' => h.ne_zero (by rw [← hsum, show α.1 + β.1 = -β.1 from h', add_neg_cancel]))
        (by rw [hsum]; exact h),
      stringNorm_of_isRoot_without117 (by rw [add_sub_cancel_right]; exact α.2)]
  rw [coeff12_without117, dite_eq_left h1]
  exact natAbs_div_two_of_natAbs_eq_two_without117 (by rw [Int.natAbs_mul, hN1, hN2])

theorem natAbs_coeff21_without117
    (F : RootOperatorFamily τ) (hD : D.Valid) (hτ : NoG2 τ) {α β : Root τ} (hne : α.1 ≠ β.1)
    (hne' : α.1 ≠ -β.1) (h : IsRoot τ (2 • α.1 + β.1)) :
    (coeff21_without117 F hD α β).natAbs = 1 := by
  have hβα : β.1 ≠ -α.1 := fun h' => hne' (by rw [h', neg_neg])
  have h1 : IsRoot τ (α.1 + β.1) := by
    rw [add_comm]
    exact isRoot_add_of_isRoot_add_two_smul α.2 β.2 (Ne.symm hne) hβα (by rwa [add_comm])
  have h' : IsRoot τ (2 • α.1 + 1 • β.1) := by rwa [one_smul]
  obtain ⟨hαα, hββ, hαβ⟩ : iform α.1 α.1 = 2 ∧ iform β.1 β.1 = 4 ∧ iform α.1 β.1 = -2 := by
    rcases exponent_pair_cases hτ α.2 β.2 hne hne' (by norm_num) le_rfl h' with h | h | h
    · omega
    · omega
    · exact h.2.2
  have hn : ¬IsRoot τ (β.1 - α.1) := not_isRoot_sub_of_iform_without117 hτ (by omega) hαβ
  have hN1 : (bracketCoeff_without117 F hD α β).natAbs = 1 := by
    rw [bracketCoeff_natAbs_without117 F hD hβα h1, stringNorm_of_not_isRoot_without117 hn]
  have hsum : α.1 + (α.1 + β.1) = 2 • α.1 + β.1 := by rw [two_nsmul]; abel
  have hN2 : (bracketCoeff_without117 F hD α ⟨α.1 + β.1, h1⟩).natAbs = 2 := by
    rw [bracketCoeff_natAbs_without117 F hD (γ := ⟨α.1 + β.1, h1⟩)
        (fun h' => h.ne_zero (by rw [← hsum, show α.1 + β.1 = -α.1 from h', add_neg_cancel]))
        (by rw [hsum]; exact h),
      stringNorm_of_isRoot_without117 (by rw [add_sub_cancel_left]; exact β.2)]
  rw [coeff21_without117, dite_eq_left h1]
  exact natAbs_div_two_of_natAbs_eq_two_without117 (by rw [Int.natAbs_mul, hN1, hN2])

end RootOperatorFamily'

section GroupLayer

variable {K : Type} [Field K]

theorem xPar_of_isRoot_without117
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c = F.eltElement ⟨γ, h⟩ c := by
  classical
  exact dite_eq_left h

theorem xPar_of_not_isRoot_without117
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ) (c : K) :
    xPar F γ c = 1 := by
  classical
  exact dite_eq_right h

theorem xPar_add_without117
    (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) (c d : K) :
    xPar F γ (c + d) = xPar F γ c * xPar F γ d := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot_without117 F h, xPar_of_isRoot_without117 F h,
      xPar_of_isRoot_without117 F h, F.eltElement_add]
  · rw [xPar_of_not_isRoot_without117 F h, xPar_of_not_isRoot_without117 F h,
      xPar_of_not_isRoot_without117 F h, mul_one]

theorem xPar_zero_without117
    (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) : xPar F γ (0 : K) = 1 := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot_without117 F h, F.eltElement_zero]
  · rw [xPar_of_not_isRoot_without117 F h]

theorem xPar_neg_without117
    (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) (c : K) : (xPar F γ c)⁻¹ = xPar F γ (-c) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← xPar_add_without117 F, neg_add_cancel,
    xPar_zero_without117 F]

theorem endHom_xPar_without117
    (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ) (c : K) :
    endHom K (xPar F γ c) = RootOperatorFamily'.eltOr F K γ c := by
  by_cases h : IsRoot τ γ
  · rw [xPar_of_isRoot_without117 F h, RootOperatorFamily'.eltOr_of_isRoot_without117 F K h]
    rfl
  · rw [xPar_of_not_isRoot_without117 F h, RootOperatorFamily'.eltOr_of_not_isRoot_without117 F K h,
      map_one]

variable {D : AdjData τ}

end GroupLayer
end CFSG.LieType.Steinberg.Adjoint
end

end
