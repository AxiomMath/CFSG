module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {F : Type} [Field F]

theorem t148_diagUnits_comm (a b c a' b' c' : Fˣ) :
    diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
  rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]

theorem t148_diagUnits_one : diagUnits (1 : Fˣ) 1 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]

theorem t148_diagUnits_pow (u v w : Fˣ) (n : ℕ) :
    diagUnits u v w ^ n = diagUnits (u ^ n) (v ^ n) (w ^ n) := by
  induction n with
  | zero => simp [t148_diagUnits_one]
  | succ n ih => simp only [pow_succ, ih, diagUnits_mul]

theorem t148_diagUnits_eq_one {u v w : Fˣ} (h : diagUnits u v w = 1) :
    u = 1 ∧ v = 1 ∧ w = 1 := by
  have h' := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_diagUnits, Units.val_one] at h'
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · simpa using congrFun (congrFun h' 0) 0
  · simpa using congrFun (congrFun h' 1) 1
  · simpa using congrFun (congrFun h' 2) 2

theorem t148_units_eq_one_of_pow_char {p : ℕ} [Fact p.Prime] [CharP F p] {u : Fˣ}
    (hu : u ^ p = 1) : u = 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h1 : ((u : F) - 1) ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, sub_self]
  apply Units.ext
  exact sub_eq_zero.mp ((pow_eq_zero_iff hp0).mp h1)

theorem t148_conj_pow (g a : GL (Fin 3) F) (n : ℕ) :
    (g⁻¹ * a * g) ^ n = g⁻¹ * a ^ n * g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, ih]
    group

theorem t148_eq_zero_of_mulVec {N : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ w : Fin 3 → F, N *ᵥ w = 0) : N = 0 := by
  ext i j
  have hij := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hij
  simpa using hij

theorem t148_kill {X T : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F}
    (hspan : ∀ w : Fin 3 → F, ∃ c0 c1 c2 : F,
      w = c0 • v + c1 • (X *ᵥ v) + c2 • (X *ᵥ (X *ᵥ v)))
    (hT : T * X = X * T) (hv : T *ᵥ v = 0) : T = 0 := by
  have hcomm : ∀ w, T *ᵥ (X *ᵥ w) = X *ᵥ (T *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hT]
  have h1 : T *ᵥ (X *ᵥ v) = 0 := by rw [hcomm, hv, Matrix.mulVec_zero]
  have h2 : T *ᵥ (X *ᵥ (X *ᵥ v)) = 0 := by rw [hcomm, h1, Matrix.mulVec_zero]
  have hall : ∀ w, T *ᵥ w = 0 := by
    intro w
    obtain ⟨c0, c1, c2, rfl⟩ := hspan w
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hv, h1, h2, smul_zero, add_zero]
  exact t148_eq_zero_of_mulVec hall

theorem t148_commute_poly_X (X : Matrix (Fin 3) (Fin 3) F) (c0 c1 c2 : F) :
    Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X)) X := by
  have h1 : Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F)) X :=
    (Commute.one_left X).smul_left c0
  have h2 : Commute (c1 • X) X := (Commute.refl X).smul_left c1
  have h3 : Commute (c2 • (X * X)) X :=
    ((Commute.refl X).mul_left (Commute.refl X)).smul_left c2
  exact (h1.add_left h2).add_left h3

theorem t148_commute_poly (X : Matrix (Fin 3) (Fin 3) F) (c0 c1 c2 d0 d1 d2 : F) :
    Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X))
      (d0 • (1 : Matrix (Fin 3) (Fin 3) F) + d1 • X + d2 • (X * X)) := by
  have hS := t148_commute_poly_X X c0 c1 c2
  have h0 : Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X))
      (d0 • (1 : Matrix (Fin 3) (Fin 3) F)) := (Commute.one_right _).smul_right d0
  have h1 : Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X))
      (d1 • X) := hS.smul_right d1
  have h2 : Commute (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X))
      (d2 • (X * X)) := (hS.mul_right hS).smul_right d2
  exact (h0.add_right h1).add_right h2

theorem t148_span {X : Matrix (Fin 3) (Fin 3) F} {ℓ : F}
    (hirr : ∀ W : Submodule F (Fin 3 → F), (∀ w ∈ W, X *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX3 : X ^ 3 = ℓ • (1 : Matrix (Fin 3) (Fin 3) F)) {v : Fin 3 → F} (hv : v ≠ 0) :
    ∀ w : Fin 3 → F, ∃ c0 c1 c2 : F,
      w = c0 • v + c1 • (X *ᵥ v) + c2 • (X *ᵥ (X *ᵥ v)) := by
  have hXXX : X * (X * X) = ℓ • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← hX3, pow_three]
  have h3 : X *ᵥ (X *ᵥ (X *ᵥ v)) = ℓ • v := by
    simp only [Matrix.mulVec_mulVec, hXXX, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hgen : ∀ g ∈ ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)),
      X *ᵥ g ∈ Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h <;> rw [h]
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · rw [h3]
      exact Submodule.smul_mem _ ℓ (Submodule.subset_span (by simp))
  have hle : Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) ≤
      (Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F))).comap
        (Matrix.mulVecLin X) := by
    rw [Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact hgen g hg
  have hinv : ∀ w ∈ Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)),
      X *ᵥ w ∈ Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) := by
    intro w hw
    have h := hle hw
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h
  have htop : Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) = ⊤ := by
    rcases hirr _ hinv with h | h
    · exfalso
      have hvmem : v ∈ Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) :=
        Submodule.subset_span (by simp)
      rw [h, Submodule.mem_bot] at hvmem
      exact hv hvmem
    · exact h
  intro w
  have hw : w ∈ Submodule.span F ({v, X *ᵥ v, X *ᵥ (X *ᵥ v)} : Set (Fin 3 → F)) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c0, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hw
  obtain ⟨c1, c2, rfl⟩ := Submodule.mem_span_pair.mp hz
  exact ⟨c0, c1, c2, by rw [add_assoc]⟩

theorem t148_poly_of_commute {X A : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F}
    (hspan : ∀ w : Fin 3 → F, ∃ c0 c1 c2 : F,
      w = c0 • v + c1 • (X *ᵥ v) + c2 • (X *ᵥ (X *ᵥ v)))
    (hA : A * X = X * A) :
    ∃ c0 c1 c2 : F, A = c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X) := by
  obtain ⟨c0, c1, c2, hc⟩ := hspan (A *ᵥ v)
  refine ⟨c0, c1, c2, ?_⟩
  have hPX := (t148_commute_poly_X X c0 c1 c2).eq
  have hPv : (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X)) *ᵥ v = A *ᵥ v := by
    rw [hc, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hkill := t148_kill
    (T := A - (c0 • (1 : Matrix (Fin 3) (Fin 3) F) + c1 • X + c2 • (X * X)))
    hspan (by rw [sub_mul, mul_sub, hA, hPX]) (by rw [Matrix.sub_mulVec, hPv, sub_self])
  exact sub_eq_zero.mp hkill

theorem comm_of_commute_conj_diagTau {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (g : GL (Fin 3) F)
    {a b : GL (Fin 3) F} (ha : a * (g * diagTau hτ * g⁻¹) = (g * diagTau hτ * g⁻¹) * a)
    (hb : b * (g * diagTau hτ * g⁻¹) = (g * diagTau hτ * g⁻¹) * b) : a * b = b * a := by
  have ha' : (g⁻¹ * a * g) * diagTau hτ = diagTau hτ * (g⁻¹ * a * g) := by
    calc (g⁻¹ * a * g) * diagTau hτ = g⁻¹ * (a * (g * diagTau hτ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * diagTau hτ * g⁻¹) * a) * g := by rw [ha]
      _ = diagTau hτ * (g⁻¹ * a * g) := by group
  have hb' : (g⁻¹ * b * g) * diagTau hτ = diagTau hτ * (g⁻¹ * b * g) := by
    calc (g⁻¹ * b * g) * diagTau hτ = g⁻¹ * (b * (g * diagTau hτ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * diagTau hτ * g⁻¹) * b) * g := by rw [hb]
      _ = diagTau hτ * (g⁻¹ * b * g) := by group
  obtain ⟨u₁, v₁, w₁, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148W.exists_eq_diagUnits_of_commute hτ hτ1 ha'
  obtain ⟨u₂, v₂, w₂, hB⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148W.exists_eq_diagUnits_of_commute hτ hτ1 hb'
  have ha2 : a = g * diagUnits u₁ v₁ w₁ * g⁻¹ := by
    rw [← hA]
    group
  have hb2 : b = g * diagUnits u₂ v₂ w₂ * g⁻¹ := by
    rw [← hB]
    group
  rw [ha2, hb2]
  calc g * diagUnits u₁ v₁ w₁ * g⁻¹ * (g * diagUnits u₂ v₂ w₂ * g⁻¹)
      = g * (diagUnits u₁ v₁ w₁ * diagUnits u₂ v₂ w₂) * g⁻¹ := by group
    _ = g * (diagUnits u₂ v₂ w₂ * diagUnits u₁ v₁ w₁) * g⁻¹ := by
        rw [t148_diagUnits_comm]
    _ = g * diagUnits u₂ v₂ w₂ * g⁻¹ * (g * diagUnits u₁ v₁ w₁ * g⁻¹) := by group

theorem eq_one_of_commute_conj_diagTau {p : ℕ} [Fact p.Prime] [CharP F p] {τ : F}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (g : GL (Fin 3) F) {a : GL (Fin 3) F}
    (ha : a * (g * diagTau hτ * g⁻¹) = (g * diagTau hτ * g⁻¹) * a) (hap : a ^ p = 1) :
    a = 1 := by
  have ha' : (g⁻¹ * a * g) * diagTau hτ = diagTau hτ * (g⁻¹ * a * g) := by
    calc (g⁻¹ * a * g) * diagTau hτ = g⁻¹ * (a * (g * diagTau hτ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * diagTau hτ * g⁻¹) * a) * g := by rw [ha]
      _ = diagTau hτ * (g⁻¹ * a * g) := by group
  obtain ⟨u, v, w, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec14.Ronan148W.exists_eq_diagUnits_of_commute hτ hτ1 ha'
  have hpow : (g⁻¹ * a * g) ^ p = 1 := by
    rw [t148_conj_pow, hap, mul_one, inv_mul_cancel]
  rw [hA, t148_diagUnits_pow] at hpow
  obtain ⟨hu, hv, hw⟩ := t148_diagUnits_eq_one hpow
  have hu1 := t148_units_eq_one_of_pow_char hu
  have hv1 := t148_units_eq_one_of_pow_char hv
  have hw1 := t148_units_eq_one_of_pow_char hw
  subst hu1 hv1 hw1
  rw [t148_diagUnits_one] at hA
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [hA, mul_one, mul_inv_cancel]

theorem comm_of_commute_irred {y : GL (Fin 3) F}
    (hirr : ∀ W : Submodule F (Fin 3 → F),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hy3 : y ^ 3 ∈ StatedScalars (Fin 3) F)
    {a b : GL (Fin 3) F} (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  obtain ⟨ℓ, hℓ⟩ := MonoidHom.mem_range.mp hy3
  have hX3 : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = (ℓ : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_pow_eq_pow_val, ← hℓ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hv : (Pi.single (0 : Fin 3) (1 : F) : Fin 3 → F) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  have hspan := t148_span hirr hX3 hv
  have hA : (a : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (a : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul, ha]
  have hB : (b : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (b : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hb]
  obtain ⟨c0, c1, c2, hAe⟩ := t148_poly_of_commute hspan hA
  obtain ⟨d0, d1, d2, hBe⟩ := t148_poly_of_commute hspan hB
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hAe, hBe]
  exact (t148_commute_poly _ c0 c1 c2 d0 d1 d2).eq

theorem eq_one_of_commute_irred {p : ℕ} [Fact p.Prime] [CharP F p] {y : GL (Fin 3) F}
    (hirr : ∀ W : Submodule F (Fin 3 → F),
      (∀ v ∈ W, (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    {a : GL (Fin 3) F} (ha : a * y = y * a) (hap : a ^ p = 1) : a = 1 := by
  have hA : (a : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (a : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, ← Units.val_mul, ha]
  have hNX : ((a : Matrix (Fin 3) (Fin 3) F) - 1) * (y : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * ((a : Matrix (Fin 3) (Fin 3) F) - 1) := by
    rw [sub_mul, mul_sub, hA, one_mul, mul_one]
  have hNp : ((a : Matrix (Fin 3) (Fin 3) F) - 1) ^ p = 0 := by
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow, ← Units.val_pow_eq_pow_val,
      hap, Units.val_one, sub_self]
  have hinvW : ∀ v ∈ LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin 3) (Fin 3) F) - 1)),
      (y : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈
        LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin 3) (Fin 3) F) - 1)) := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hNX, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases hirr _ hinvW with hbot | htop
  · exfalso
    have hdet : ((a : Matrix (Fin 3) (Fin 3) F) - 1).det ≠ 0 := by
      intro hd
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
      have hvW : v ∈ LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin 3) (Fin 3) F) - 1)) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hv
      rw [hbot, Submodule.mem_bot] at hvW
      exact hv0 hvW
    have hunit : IsUnit ((a : Matrix (Fin 3) (Fin 3) F) - 1) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hu : IsUnit (((a : Matrix (Fin 3) (Fin 3) F) - 1) ^ p) := hunit.pow p
    rw [hNp] at hu
    exact not_isUnit_zero hu
  · have hN0 : (a : Matrix (Fin 3) (Fin 3) F) - 1 = 0 := by
      apply t148_eq_zero_of_mulVec
      intro w
      have hw : w ∈ LinearMap.ker (Matrix.mulVecLin ((a : Matrix (Fin 3) (Fin 3) F) - 1)) := by
        rw [htop]
        exact Submodule.mem_top
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp hN0

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
