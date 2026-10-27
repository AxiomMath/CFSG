module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBstarBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

section Fix

@[expose] def fixSub (S : ι → Prop) : Subgroup (GL ι K) where
  carrier := {x | ∀ i, S i → ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i}
  mul_mem' {x y} hx hy i hi i' := by
    rw [Units.val_mul, Matrix.mul_apply]
    simp only [hy i hi, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    have := hx i hi i'
    rw [Matrix.one_apply] at this
    exact this
  one_mem' i _ i' := rfl
  inv_mem' {x} hx i hi i' := by
    have h1 : (x : Matrix ι ι K) *ᵥ Pi.single i 1 = Pi.single i 1 :=
      mulVec_single_eq_of_col (hx i hi)
    have h2 : ((x⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Pi.single i 1 = Pi.single i 1 := by
      conv_lhs => rw [← h1]
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have h3 := congrFun h2 i'
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at h3
    rw [Matrix.one_apply, h3]

theorem mem_fixSub {S : ι → Prop} {x : GL ι K} :
    x ∈ fixSub S ↔ ∀ i, S i → ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i :=
  Iff.rfl

theorem commutator_diagGL_col {a : GL ι K} {δ : ι → Kˣ} {n : ι}
    (h : ∀ k, ((a⁻¹ : GL ι K) : Matrix ι ι K) k n ≠ 0 → δ k = δ n) (i' : ι) :
    ((a * TauCeti.diagGL δ * a⁻¹ * (TauCeti.diagGL δ)⁻¹ : GL ι K) : Matrix ι ι K) i' n =
      (1 : Matrix ι ι K) i' n := by
  have hcol : ∀ k, ((TauCeti.diagGL δ * (a⁻¹ * (TauCeti.diagGL δ)⁻¹) : GL ι K) : Matrix ι ι K) k n =
      ((a⁻¹ : GL ι K) : Matrix ι ι K) k n := by
    intro k
    rw [← map_inv, Units.val_mul, Units.val_mul, TauCeti.diagGL_coe, TauCeti.diagGL_coe,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hk : ((a⁻¹ : GL ι K) : Matrix ι ι K) k n = 0
    · rw [hk]
      simp
    · rw [h k hk, Pi.inv_apply, mul_comm, mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, mul_one]
  have e : a * TauCeti.diagGL δ * a⁻¹ * (TauCeti.diagGL δ)⁻¹ =
      a * (TauCeti.diagGL δ * (a⁻¹ * (TauCeti.diagGL δ)⁻¹)) := by group
  rw [e, Units.val_mul, Matrix.mul_apply]
  simp only [hcol]
  rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end Fix

section Exponent

open SeitzReduction.OmegaPilot

variable [CharP K 2]

theorem sq_eq_one_of_fix {QF : QuadraticForm K (ι → K)} {a0 b0 a1 b1 : ι}
    (h0 : IsHypCoord QF a0 b0) (h1 : IsHypCoord QF a1 b1) (hab : a0 ≠ b1)
    (hba : b0 ≠ a1) (hbb : b0 ≠ b1) {x : GL ι K} (hxO : x ∈ LargeEvenOrthGroup ⇑QF)
    (hx : x ∈ fixSub fun i => i ≠ b0 ∧ i ≠ b1) : x ^ 2 = 1 := by
  set X : Matrix ι ι K := (x : Matrix ι ι K) with hX
  have hcol : ∀ i, i ≠ b0 → i ≠ b1 → X *ᵥ Pi.single i 1 = Pi.single i 1 := fun i h1' h2' =>
    mulVec_single_eq_of_col (hx i ⟨h1', h2'⟩)
  have hpol : ∀ i j, QuadraticMap.polar QF (X *ᵥ Pi.single i 1) (X *ᵥ Pi.single j 1) =
      QuadraticMap.polar QF (Pi.single i 1) (Pi.single j 1) :=
    fun i j => polar_mulVec_of_mem_orthGroup hxO _ _
  have hentry : ∀ j, X b0 j = (1 : Matrix ι ι K) b0 j ∧ X b1 j = (1 : Matrix ι ι K) b1 j := by
    intro j
    by_cases hj0 : j = b0
    · subst hj0
      have e1 := hpol a0 j
      rw [hcol a0 h0.ne (Ne.symm hab).symm, h0.polar_left, h0.polar_left,
        Matrix.mulVec_single_one, Matrix.col_apply] at e1
      have e2 := hpol a1 j
      rw [hcol a1 hba.symm (h1.ne), h1.polar_left, h1.polar_left, Matrix.mulVec_single_one,
        Matrix.col_apply] at e2
      exact ⟨by rw [e1, Pi.single_apply, Matrix.one_apply],
        by rw [e2, Pi.single_apply, Matrix.one_apply]⟩
    · by_cases hj1 : j = b1
      · subst hj1
        have e1 := hpol a0 j
        rw [hcol a0 h0.ne (Ne.symm hab).symm, h0.polar_left, h0.polar_left,
          Matrix.mulVec_single_one, Matrix.col_apply] at e1
        have e2 := hpol a1 j
        rw [hcol a1 hba.symm (h1.ne), h1.polar_left, h1.polar_left, Matrix.mulVec_single_one,
          Matrix.col_apply] at e2
        exact ⟨by rw [e1, Pi.single_apply, Matrix.one_apply],
          by rw [e2, Pi.single_apply, Matrix.one_apply]⟩
      · exact ⟨hx j ⟨hj0, hj1⟩ b0, hx j ⟨hj0, hj1⟩ b1⟩
  set N : Matrix ι ι K := X - 1 with hN
  have hNcol : ∀ i j, N i j ≠ 0 → (j = b0 ∨ j = b1) ∧ i ≠ b0 ∧ i ≠ b1 := by
    intro i j hij
    refine ⟨?_, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      apply hij
      rw [hN, Matrix.sub_apply, show X i j = (1 : Matrix ι ι K) i j from hx j ⟨hcon.1, hcon.2⟩ i,
        sub_self]
    · rintro rfl
      exact hij (by rw [hN, Matrix.sub_apply, (hentry j).1, sub_self])
    · rintro rfl
      exact hij (by rw [hN, Matrix.sub_apply, (hentry j).2, sub_self])
  have hNN : N * N = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hkj : N k j = 0
    · rw [hkj, mul_zero]
    · obtain ⟨-, hk0, hk1⟩ := hNcol k j hkj
      by_cases hik : N i k = 0
      · rw [hik, zero_mul]
      · rcases (hNcol i k hik).1 with h | h <;> contradiction
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hX]
  have hXN : X = 1 + N := by rw [hN, add_sub_cancel]
  rw [hXN, sq]
  have hN2 : N + N = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
    _ = 1 := by rw [hN2, hNN, add_zero, add_zero]

end Exponent

section Std

open SeitzReduction.OmegaPilot

omit [Fintype ι] in
theorem isHypCoord_swap {QF : QuadraticForm K (ι → K)} {a b : ι} (h : IsHypCoord QF a b) :
    IsHypCoord QF b a where
  ne := h.ne.symm
  map_left := h.map_right
  map_right := h.map_left
  polar_left := h.polar_right
  polar_right := h.polar_left

@[expose] def BFam {Ω : Subgroup (GL ι K)} (H : Set Ω) (E : Subgroup Ω) (P : Subgroup Ω) : Prop :=
  IsPGroup 2 P ∧ (∀ x ∈ P, ∀ h ∈ H, x * h = h * x) ∧ (∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ ∈ P) ∧
    P ≤ ⁅P, E⁆

variable [Finite K] [CharP K 2]

theorem exists_invariant_twoSubgroup {QF : QuadraticForm K (ι → K)} {a0 b0 a1 b1 : ι}
    (h0 : IsHypCoord QF a0 b0) (h1 : IsHypCoord QF a1 b1) (ha01 : a0 ≠ a1) (hab : a0 ≠ b1)
    (hba : b0 ≠ a1) (hbb : b0 ≠ b1) {Ω : Subgroup (GL ι K)}
    (hΩO : Ω ≤ LargeEvenOrthGroup ⇑QF) {E : Subgroup Ω} {H : Set Ω} (hHE : H ⊆ E)
    {ζ : Kˣ} (hζ2 : ζ * ζ ≠ 1) {δ₁ : ι → Kˣ} (hh₁ : ∃ h ∈ H, (h : GL ι K) = TauCeti.diagGL δ₁)
    (hδ₁a0 : δ₁ a0 = ζ) (hδ₁b1 : δ₁ b1 = ζ) (hδ₁b0 : δ₁ b0 = ζ⁻¹) (hδ₁a1 : δ₁ a1 = ζ⁻¹)
    (hδ₁o : ∀ j, j ≠ a0 → j ≠ b0 → j ≠ a1 → j ≠ b1 → δ₁ j ≠ ζ ∧ δ₁ j ≠ ζ⁻¹)
    (hEdiag : ∀ e ∈ E, ∃ δ : ι → Kˣ, (e : GL ι K) = TauCeti.diagGL δ)
    (hsep : ∀ i, i ≠ a0 → i ≠ b0 → i ≠ a1 → i ≠ b1 → ∀ k,
      (∀ h ∈ H, ∀ δ, (h : GL ι K) = TauCeti.diagGL δ → δ k = δ i) →
      ∀ e ∈ E, ∀ δ, (e : GL ι K) = TauCeti.diagGL δ → δ k = δ i)
    {δ₀ : ι → Kˣ} (ht₀ : ∃ t ∈ E, (t : GL ι K) = TauCeti.diagGL δ₀) (hδ₀a0 : δ₀ a0 = ζ)
    (hδ₀b1 : δ₀ b1 = 1) {Y : Subgroup Ω} (hY : BFam H E Y)
    (hYU : Y ≤ (fixSub fun i => i ≠ b0 ∧ i ≠ b1).comap Ω.subtype) (hY1 : Y ≠ ⊥)
    {p : ℕ} (hp : Odd p) (φ : MulAut Ω) (hφ : φ ^ p = 1) (hφE : ∀ e ∈ E, φ e = e) :
    ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ e ∈ E, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧
      ∀ u ∈ U, φ u ∈ U := by
  set Up := (fixSub fun i => i ≠ b0 ∧ i ≠ b1).comap Ω.subtype with hUp
  set Um := (fixSub fun i => i ≠ a0 ∧ i ≠ a1).comap Ω.subtype with hUm
  have hUp2 : IsPGroup 2 Up := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using sq_eq_one_of_fix h0 h1 hab hba hbb (hΩO x.1.2) x.2))⟩
  have hUm2 : IsPGroup 2 Um := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using sq_eq_one_of_fix (isHypCoord_swap h0) (isHypCoord_swap h1) hba hab
      ha01 (hΩO x.1.2) x.2))⟩
  have hUU : Up ⊓ Um = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxp, hxm⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Units.ext
    ext i' i
    by_cases hi : i ≠ b0 ∧ i ≠ b1
    · exact hxp i hi i'
    · push Not at hi
      have hi' : i ≠ a0 ∧ i ≠ a1 := by
        by_cases hib : i = b0
        · rw [hib]
          exact ⟨h0.ne.symm, hba⟩
        · rw [hi hib]
          exact ⟨hab.symm, h1.ne.symm⟩
      exact hxm i hi' i'
  have hEφ : E.map φ.toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y ∈ E
      rw [hφE y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hφE x hx⟩
  have hF : ∀ P, BFam H E P → BFam H E (P.map φ.toMonoidHom) := by
    rintro P ⟨hP2, hPc, hPn, hPe⟩
    refine ⟨hP2.map _, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ h hh
      have hφh : φ h = h := hφE h (hHE hh)
      change φ x * h = h * φ x
      rw [← hφh, ← map_mul, ← map_mul, hPc x hx h hh]
    · rintro e he _ ⟨x, hx, rfl⟩
      refine ⟨e * x * e⁻¹, hPn e he x hx, ?_⟩
      change φ (e * x * e⁻¹) = e * φ x * e⁻¹
      rw [map_mul, map_mul, map_inv, hφE e he]
    · calc P.map φ.toMonoidHom ≤ (⁅P, E⁆).map φ.toMonoidHom := Subgroup.map_mono hPe
        _ = ⁅P.map φ.toMonoidHom, E.map φ.toMonoidHom⁆ := Subgroup.map_commutator _ _ _
        _ = ⁅P.map φ.toMonoidHom, E⁆ := by rw [hEφ]
  obtain ⟨h₁, h₁H, hh₁δ⟩ := hh₁
  obtain ⟨t₀, ht₀E, ht₀δ⟩ := ht₀
  have hcomm_entry : ∀ (x : GL ι K) (δ : ι → Kˣ),
      x * TauCeti.diagGL δ = TauCeti.diagGL δ * x →
      ∀ i j, (x : Matrix ι ι K) i j ≠ 0 → δ i = δ j := by
    intro x δ hx i j hij
    by_contra hne
    exact hij (eq_zero_of_commute_diagonal (commute_diagGL_iff.mp hx)
      (fun h => hne (Units.ext h)))
  have hne : ζ ≠ ζ⁻¹ := fun h => hζ2 (by nth_rewrite 2 [h]; exact mul_inv_cancel ζ)
  have hval : ∀ j, δ₁ j = ζ → j = a0 ∨ j = b1 := by
    intro j hj
    by_contra hc
    push Not at hc
    by_cases hj0 : j = b0
    · rw [hj0, hδ₁b0] at hj
      exact hne hj.symm
    · by_cases hj1 : j = a1
      · rw [hj1, hδ₁a1] at hj
        exact hne hj.symm
      · exact (hδ₁o j hc.1 hj0 hj1 hc.2).1 hj
  have hval' : ∀ j, δ₁ j = ζ⁻¹ → j = b0 ∨ j = a1 := by
    intro j hj
    by_contra hc
    push Not at hc
    by_cases hj0 : j = a0
    · rw [hj0, hδ₁a0] at hj
      exact hne hj
    · by_cases hj1 : j = b1
      · rw [hj1, hδ₁b1] at hj
        exact hne hj
      · exact (hδ₁o j hj0 hc.1 hc.2 hj1).2 hj
  have hKL : ∀ P, BFam H E P → P ≤ Up ∨ P ≤ Um := by
    rintro P ⟨hP2, hPc, hPn, hPe⟩
    have hc1 : ∀ x ∈ P.map Ω.subtype, ∀ i j, (x : Matrix ι ι K) i j ≠ 0 → δ₁ i = δ₁ j := by
      rintro _ ⟨y, hy, rfl⟩ i j hij
      refine hcomm_entry (y : GL ι K) δ₁ ?_ i j hij
      have := congrArg Subtype.val (hPc y hy h₁ h₁H)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hh₁δ] at this
      exact this
    have hrow : ∀ x ∈ P.map Ω.subtype, ∀ j, j ≠ a0 → j ≠ b1 →
        (x : Matrix ι ι K) a0 j = 0 ∧ (x : Matrix ι ι K) b1 j = 0 := by
      intro x hx j hj0 hj1
      constructor
      · by_contra h
        have := hc1 x hx a0 j h
        rw [hδ₁a0] at this
        rcases hval j this.symm with h' | h' <;> contradiction
      · by_contra h
        have := hc1 x hx b1 j h
        rw [hδ₁b1] at this
        rcases hval j this.symm with h' | h' <;> contradiction
    have hcolW : ∀ x ∈ P.map Ω.subtype, ∀ i, i ≠ a0 → i ≠ b1 →
        (x : Matrix ι ι K) i a0 = 0 ∧ (x : Matrix ι ι K) i b1 = 0 := by
      intro x hx i hi0 hi1
      constructor
      · by_contra h
        have := hc1 x hx i a0 h
        rw [hδ₁a0] at this
        rcases hval i this with h' | h' <;> contradiction
      · by_contra h
        have := hc1 x hx i b1 h
        rw [hδ₁b1] at this
        rcases hval i this with h' | h' <;> contradiction
    have hcolW' : ∀ x ∈ P.map Ω.subtype, ∀ i, i ≠ b0 → i ≠ a1 →
        (x : Matrix ι ι K) i b0 = 0 ∧ (x : Matrix ι ι K) i a1 = 0 := by
      intro x hx i hi0 hi1
      constructor
      · by_contra h
        have := hc1 x hx i b0 h
        rw [hδ₁b0] at this
        rcases hval' i this with h' | h' <;> contradiction
      · by_contra h
        have := hc1 x hx i a1 h
        rw [hδ₁a1] at this
        rcases hval' i this with h' | h' <;> contradiction
    have hnorm : ∀ x ∈ P.map Ω.subtype,
        TauCeti.diagGL δ₀ * x * (TauCeti.diagGL δ₀)⁻¹ ∈ P.map Ω.subtype := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨t₀ * y * t₀⁻¹, hPn t₀ ht₀E y hy, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, ht₀δ]
    have hrest : ∀ x ∈ P.map Ω.subtype, ∀ i, i ≠ a0 → i ≠ b0 → i ≠ a1 → i ≠ b1 →
        ∀ i', (x : Matrix ι ι K) i' i = (1 : Matrix ι ι K) i' i := by
      rintro _ ⟨y, hy, rfl⟩ i h1' h2' h3' h4'
      have hle : ⁅P, E⁆ ≤ (fixSub fun j => j = i).comap Ω.subtype := by
        rw [Subgroup.commutator_le]
        intro a ha e he
        obtain ⟨δe, hδe⟩ := hEdiag e he
        intro j hj i'
        rw [hj]
        change ((a * e * a⁻¹ * e⁻¹ : Ω) : GL ι K) i' i = _
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hδe]
        refine commutator_diagGL_col (fun k hk => ?_) i'
        refine hsep i h1' h2' h3' h4' k (fun h hh δ hδ => ?_) e he δe hδe
        have hc := congrArg Subtype.val (hPc a⁻¹ (P.inv_mem ha) h hh)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hδ] at hc
        exact hcomm_entry _ δ hc k i hk
      exact (hle (hPe hy)) i rfl
    rcases fix_or_fix_of_pGroup h0 h1 ha01 hab hba hbb hζ2 hδ₀a0 hδ₀b1
      ((Subgroup.map_subtype_le P).trans hΩO) (hP2.map _) hrow hcolW hcolW' hnorm hrest with
      hA | hB
    · left
      intro y hy i hi i'
      exact hA _ ⟨y, hy, rfl⟩ i hi.1 hi.2 i'
    · right
      intro y hy i hi i'
      exact hB _ ⟨y, hy, rfl⟩ i hi.1 hi.2 i'
  have hsup : ∀ Uq : Subgroup Ω, IsPGroup 2 Uq → ∀ S : Set (Subgroup Ω),
      (∀ P ∈ S, BFam H E P ∧ P ≤ Uq) → BFam H E (sSup S) := by
    intro Uq hUq S hS
    refine ⟨hUq.to_le (sSup_le fun P hP => (hS P hP).2), ?_, ?_, ?_⟩
    · have hle : sSup S ≤ Subgroup.centralizer H := sSup_le fun P hP x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact ((hS P hP).1.2.1 x hx h hh).symm
      intro x hx h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) h hh).symm
    · intro e he
      have hle : sSup S ≤ (sSup S).comap (MulAut.conj e).toMonoidHom :=
        sSup_le fun P hP x hx => by
          change e * x * e⁻¹ ∈ sSup S
          exact le_sSup hP ((hS P hP).1.2.2.1 e he x hx)
      intro x hx
      exact hle hx
    · exact sSup_le fun P hP =>
        (hS P hP).1.2.2.2.trans (Subgroup.commutator_mono (le_sSup hP) le_rfl)
  obtain ⟨Z, hZF, hZ1, -, hZφ⟩ := exists_invariant_of_dichotomy hp φ hφ (BFam H E) Up Um hF hKL
    hUU (hsup Up hUp2) (hsup Um hUm2) hY hYU hY1
  exact ⟨Z, hZ1, hZF.1, hZF.2.2.1, fun u hu => hZφ ⟨u, hu, rfl⟩⟩

end Std

end TableBOrth

end CFSG.StandardType
