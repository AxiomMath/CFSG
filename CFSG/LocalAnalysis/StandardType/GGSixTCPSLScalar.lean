module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux

public section

namespace CFSG.StandardType.TableCRes

section OrderP

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition


private theorem tcPSL_eq_scalar {F : Type} [Field F] {N : ℕ} [Nonempty (Fin N)]
    (g : GL (Fin N) F) (c : F)
    (hg : (g : Matrix (Fin N) (Fin N) F) = Matrix.scalar (Fin N) c) :
    ∃ u : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin N) u := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hmul := Units.mul_inv g
    rw [hg, map_zero, zero_mul] at hmul
    exact zero_ne_one hmul
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hg

private theorem tcPSL_unit_eq_one_of_pow {F : Type} [Field F] (m p : ℕ) (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card Fˣ) (c : Fˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c ^ p = 1) : c = 1 := by
  have hcp : c ^ p = 1 := by
    apply Units.ext
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (c ^ p) = 1 := by
      rw [map_pow]
      exact hc
    have h2 := congrArg (fun g : GL (Fin (m + 1)) F => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F))
      h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h2
    have h3 : Matrix.scalar (Fin (m + 1)) ((c ^ p : Fˣ) : F) = Matrix.scalar (Fin (m + 1)) 1 := by
      rw [h2, map_one]
    exact (Matrix.scalar_inj.mp h3).trans Units.val_one.symm
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf c ∣ Nat.card Fˣ := orderOf_dvd_natCard c
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd h2 hpF

private theorem tcPSL_commute_mul_scalar {F : Type} [Field F] {N : ℕ} {x y : GL (Fin N) F}
    (hxy : Commute x y) (c d : Fˣ) :
    Commute (x * Matrix.GeneralLinearGroup.scalar (Fin N) c)
      (y * Matrix.GeneralLinearGroup.scalar (Fin N) d) := by
  have h1 : Commute x (Matrix.GeneralLinearGroup.scalar (Fin N) d) :=
    (Matrix.GeneralLinearGroup.scalar_commute d x).symm
  have h2 : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c) y :=
    Matrix.GeneralLinearGroup.scalar_commute c y
  have h3 : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c)
      (Matrix.GeneralLinearGroup.scalar (Fin N) d) :=
    Matrix.GeneralLinearGroup.scalar_commute c _
  exact Commute.mul_left (hxy.mul_right h1) (h2.mul_right h3)

private theorem tcPSL_mul_of_orderp (m f p : ℕ) (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ)
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {B : Subgroup X} {τ : X → GL (Fin (m + 1)) (GaloisField 2 f)}
    (hτl : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (τ b) b)
    (hτp : ∀ b ∈ B, τ b ^ p = 1)
    (hτc : ∀ b ∈ B, ∀ b' ∈ B, Commute (τ b) (τ b')) :
    ∀ b ∈ B, ∀ b' ∈ B, τ (b * b') = τ b * τ b' := by
  intro b hb b' hb'
  have h1 : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (τ b' * τ b) (b * b') :=
    IsGLLift.mul (hτl b hb) (hτl b' hb')
  have h2 : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (τ (b * b')) (b * b') :=
    hτl (b * b') (B.mul_mem hb hb')
  obtain ⟨c, hc⟩ := isGLLift_unique_PSL m (GaloisField 2 f) ψ hψ h1 h2
  obtain ⟨u, hu⟩ := tcPSL_eq_scalar _ c hc
  have hXY : τ b' * τ b = τ (b * b') * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
    rw [← hu, mul_inv_cancel_left]
  have hYS : Commute (τ (b * b')) (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u) :=
    (Matrix.GeneralLinearGroup.scalar_commute u (τ (b * b'))).symm
  have hpow : (τ b' * τ b) ^ p = 1 := by
    rw [(hτc b' hb' b hb).mul_pow, hτp b' hb', hτp b hb, one_mul]
  have hSp : Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u ^ p = 1 := by
    rw [hXY, hYS.mul_pow, hτp (b * b') (B.mul_mem hb hb'), one_mul] at hpow
    exact hpow
  have hu1 : u = 1 := tcPSL_unit_eq_one_of_pow m p hp hpF u hSp
  rw [hu1, map_one, mul_one] at hXY
  exact hXY.symm.trans (hτc b hb b' hb').eq.symm

theorem exists_orderp_lifts_PSL (m f p : ℕ) (hf : f ≠ 0) (hp : p.Prime) (hpF : ¬ p ∣ 2 ^ f - 1)
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {B : Subgroup X} (hB : ∀ b ∈ B, b ^ p = 1) {σ : X → GL (Fin (m + 1)) (GaloisField 2 f)}
    (hσ : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (σ b) b)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute (σ b) (σ b')) :
    ∃ (τ : X → GL (Fin (m + 1)) (GaloisField 2 f)) (w : X → (GaloisField 2 f)ˣ),
      (∀ b ∈ B, τ b = σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b)) ∧
      (∀ b ∈ B, τ b ^ p = 1) ∧ (∀ b ∈ B, ∀ b' ∈ B, τ (b * b') = τ b * τ b') := by
  have hpF' : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f hf]
    exact hpF
  have hw : ∀ b : X, ∃ w : (GaloisField 2 f)ˣ, b ∈ B →
      (σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) w) ^ p = 1 := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨u, hu⟩ := lift_pow_scalar_PSL m f p ψ hψ (hσ b hb) (hB b hb)
      obtain ⟨w, hwp⟩ := exists_scalar_mul_pow_eq_one hp hpF' (σ b) u hu
      exact ⟨w, fun _ => hwp⟩
    · exact ⟨1, fun h => absurd h hb⟩
  choose w hw using hw
  have hτl : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ
      (σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b)) b :=
    fun b hb => isGLLift_mul_scalar (hσ b hb) (w b)
  have hτc : ∀ b ∈ B, ∀ b' ∈ B,
      Commute (σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b))
        (σ b' * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b')) :=
    fun b hb b' hb' => tcPSL_commute_mul_scalar (hcomm b hb b' hb') (w b) (w b')
  have hτp : ∀ b ∈ B, (σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b)) ^ p = 1 :=
    fun b hb => hw b hb
  exact ⟨fun b => σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b), w,
    fun b _ => rfl, hτp,
    tcPSL_mul_of_orderp m f p hp hpF' ψ hψ
      (τ := fun b => σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b)) hτl hτp hτc⟩

end OrderP

section Fixed

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private theorem tcPSL_glScalar_eq_algebraMap {F : Type} [Field F] {N : ℕ} (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin N) c : GL (Fin N) F) :
      Matrix (Fin N) (Fin N) F) = algebraMap F (Matrix (Fin N) (Fin N) F) (c : F) := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal]
  rfl

theorem exists_fixed_PSL {F : Type} [Field F] [Finite F] [CharP F 2] {N p : ℕ} (hp : p.Prime)
    {X : Type} [Group X] {D : Subgroup X}
    (hD : Nat.card D = p ^ 2) {σ τ : X → GL (Fin N) F} {w : X → Fˣ}
    (hτσ : ∀ b ∈ D, τ b = σ b * Matrix.GeneralLinearGroup.scalar (Fin N) (w b))
    (hτp : ∀ b ∈ D, τ b ^ p = 1) (hτmul : ∀ b ∈ D, ∀ b' ∈ D, τ (b * b') = τ b * τ b')
    (hS : ∀ s ∈ σ '' (D : Set X), ∀ s' ∈ σ '' (D : Set X), Commute s s')
    (hodd : ∀ s ∈ σ '' (D : Set X), Odd (orderOf s)) {e : Matrix (Fin N) (Fin N) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) e)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) e) :
    (∃ y ∈ D, (τ y : Matrix (Fin N) (Fin N) F) * e ≠ e) ∧
      ∃ g₀ ∈ D, g₀ ≠ 1 ∧ (τ g₀ : Matrix (Fin N) (Fin N) F) * e = e := by
  classical
  obtain ⟨K, instF, instA, instFin, π, hsurj, hker, hfin⟩ := exists_blockField hS hodd he
  have hσmem : ∀ d : X, d ∈ D →
      (σ d : Matrix (Fin N) (Fin N) F) ∈ Algebra.adjoin F (Units.val '' (σ '' (D : Set X))) :=
    fun d hd => Algebra.subset_adjoin ⟨σ d, ⟨d, hd, rfl⟩, rfl⟩
  have hmemτ : ∀ y : X, y ∈ D →
      (τ y : Matrix (Fin N) (Fin N) F) ∈ Algebra.adjoin F (Units.val '' (σ '' (D : Set X))) := by
    intro y hy
    rw [hτσ y hy, Units.val_mul, tcPSL_glScalar_eq_algebraMap]
    exact mul_mem (hσmem y hy) (Subalgebra.algebraMap_mem _ _)
  obtain ⟨t, ht⟩ : ∃ t : D → Algebra.adjoin F (Units.val '' (σ '' (D : Set X))),
      ∀ y : D, ((t y : Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) :
        Matrix (Fin N) (Fin N) F) = (τ y.1 : Matrix (Fin N) (Fin N) F) :=
    ⟨fun y => ⟨τ y.1, hmemτ y.1 y.2⟩, fun y => rfl⟩
  have hpowA : ∀ y : D, t y ^ p = 1 := by
    intro y
    apply Subtype.ext
    rw [Subalgebra.coe_pow, ht, Subalgebra.coe_one, ← Units.val_pow_eq_pow_val, hτp y.1 y.2,
      Units.val_one]
  have hπpow : ∀ y : D, π (t y) ^ p = 1 := fun y => by
    rw [← map_pow, hpowA y, map_one]
  have hfix : ∀ y : D, π (t y) = 1 ↔ (τ y.1 : Matrix (Fin N) (Fin N) F) * e = e := by
    intro y
    have key := hker (t y - 1)
    have hv : ((t y - 1 : Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) :
        Matrix (Fin N) (Fin N) F) * e = (τ y.1 : Matrix (Fin N) (Fin N) F) * e - e := by
      rw [Subalgebra.coe_sub, Subalgebra.coe_one, ht, sub_mul, one_mul]
    rw [hv, map_sub, map_one, sub_eq_zero, sub_eq_zero] at key
    exact key
  have hmul_t : ∀ y y' : D, t (y * y') = t y * t y' := by
    intro y y'
    apply Subtype.ext
    have h := congrArg Units.val (hτmul y.1 y.2 y'.1 y'.2)
    rw [Units.val_mul] at h
    simp only [Subalgebra.coe_mul, ht]
    exact h
  have hmulπ : ∀ y y' : D, π (t (y * y')) = π (t y) * π (t y') := fun y y' => by
    rw [hmul_t, map_mul]
  have hτ1 : τ 1 = 1 := by
    have h := hτmul 1 D.one_mem 1 D.one_mem
    rw [mul_one] at h
    have h2 : τ 1 * τ 1 = τ 1 * 1 := by
      rw [mul_one]
      exact h.symm
    exact mul_left_cancel h2
  have ht1 : t 1 = 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_one, ht]
    show ((τ 1 : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1
    rw [hτ1, Units.val_one]
  have hinv : ∀ y : D, π (t y⁻¹) * π (t y) = 1 := by
    intro y
    rw [← hmulπ, inv_mul_cancel, ht1, map_one]
  refine ⟨?_, ?_⟩
  ·
    by_contra h1
    push Not at h1
    have hrange : ∀ a : Algebra.adjoin F (Units.val '' (σ '' (D : Set X))),
        π a ∈ (algebraMap F K).range := by
      rintro ⟨a, ha⟩
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨u, ⟨d, hd, rfl⟩, rfl⟩ := hx
        have hπt : π (t ⟨d, hd⟩) = 1 := (hfix ⟨d, hd⟩).mpr (h1 d hd)
        have hEq : (⟨(σ d : Matrix (Fin N) (Fin N) F), hσmem d hd⟩ :
            Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) =
            t ⟨d, hd⟩ * algebraMap F (Algebra.adjoin F (Units.val '' (σ '' (D : Set X))))
              (((w d)⁻¹ : Fˣ) : F) := by
          apply Subtype.ext
          rw [Subalgebra.coe_mul, ht]
          show (σ d : Matrix (Fin N) (Fin N) F) = (τ d : Matrix (Fin N) (Fin N) F) *
            algebraMap F (Matrix (Fin N) (Fin N) F) (((w d)⁻¹ : Fˣ) : F)
          rw [hτσ d hd, Units.val_mul, tcPSL_glScalar_eq_algebraMap, mul_assoc, ← map_mul,
            Units.mul_inv, map_one, mul_one]
        refine RingHom.mem_range.mpr ⟨(((w d)⁻¹ : Fˣ) : F), ?_⟩
        rw [hEq, map_mul, hπt, one_mul, π.commutes]
      | algebraMap r => exact ⟨r, (π.commutes r).symm⟩
      | add x y hx hy hx' hy' =>
        show π (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
        rw [map_add]
        exact add_mem hx' hy'
      | mul x y hx hy hx' hy' =>
        show π (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
        rw [map_mul]
        exact mul_mem hx' hy'
    have hone : Module.finrank F K = 1 := by
      rw [finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero]
      intro w'
      obtain ⟨a, rfl⟩ := hsurj w'
      obtain ⟨r, hr⟩ := hrange a
      exact ⟨r, by rw [Algebra.smul_def, mul_one]; exact hr⟩
    omega
  ·
    by_contra h2
    push Not at h2
    have hinj : ∀ y y' : D, π (t y) = π (t y') → y = y' := by
      intro y y' hyy
      have hg : π (t (y⁻¹ * y')) = 1 := by
        rw [hmulπ, ← hyy]
        exact hinv y
      have hgone : y⁻¹ * y' = 1 := by
        by_contra hne
        exact h2 (y⁻¹ * y').1 (y⁻¹ * y').2 (fun h => hne (Subtype.ext h)) ((hfix _).mp hg)
      exact inv_mul_eq_one.mp hgone
    have hcard : Nat.card D ≤ p := by
      have hfc : (Polynomial.nthRootsFinset p (1 : K)).card ≤ p :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots p 1)
      have hcardS : Nat.card (Polynomial.nthRootsFinset p (1 : K)) =
          (Polynomial.nthRootsFinset p (1 : K)).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      let g : D → Polynomial.nthRootsFinset p (1 : K) := fun y =>
        ⟨π (t y), (Polynomial.mem_nthRootsFinset hp.pos 1).mpr (hπpow y)⟩
      have hg_inj : Function.Injective g := fun y y' hyy => hinj y y' (congrArg Subtype.val hyy)
      exact (Nat.card_le_card_of_injective g hg_inj).trans (hcardS.le.trans hfc)
    rw [hD] at hcard
    nlinarith [hp.two_le]

end Fixed

section BlockDeg

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private theorem tcPSL_scalar_eq_algebraMap {F : Type} [Field F] {N : ℕ} (c : F) :
    Matrix.scalar (Fin N) c = algebraMap F (Matrix (Fin N) (Fin N) F) c := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  rfl

theorem dvd_card_pow_blockDegree_PSL {F : Type} [Field F] [Finite F] [CharP F 2] {N p : ℕ}
    (hp : p.Prime) {X : Type} [Group X] {D : Subgroup X} {σ τ : X → GL (Fin N) F} {w : X → Fˣ}
    (hτσ : ∀ b ∈ D, τ b = σ b * Matrix.GeneralLinearGroup.scalar (Fin N) (w b))
    (hτp : ∀ b ∈ D, τ b ^ p = 1)
    (hS : ∀ s ∈ σ '' (D : Set X), ∀ s' ∈ σ '' (D : Set X), Commute s s')
    (hodd : ∀ s ∈ σ '' (D : Set X), Odd (orderOf s)) {e : Matrix (Fin N) (Fin N) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) e) {y : X}
    (hyD : y ∈ D) (hye : (τ y : Matrix (Fin N) (Fin N) F) * e ≠ e) :
    p ∣ Nat.card F ^ blockDegree (Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) e - 1 := by
  obtain ⟨K, instF, instA, instFin, π, _hsurj, hker, hdeg⟩ :=
    exists_blockField hS hodd he
  have hτmem : (τ y : Matrix (Fin N) (Fin N) F) ∈
      Algebra.adjoin F (Units.val '' (σ '' (D : Set X))) := by
    have h1 : (τ y : Matrix (Fin N) (Fin N) F) =
        (σ y : Matrix (Fin N) (Fin N) F) *
          algebraMap F (Matrix (Fin N) (Fin N) F) (w y : F) := by
      rw [hτσ y hyD, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
        tcPSL_scalar_eq_algebraMap]
    rw [h1]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨σ y, ⟨y, hyD, rfl⟩, rfl⟩)
      (Subalgebra.algebraMap_mem _ _)
  obtain ⟨t, ht⟩ : ∃ t : Algebra.adjoin F (Units.val '' (σ '' (D : Set X))),
      (t : Matrix (Fin N) (Fin N) F) = (τ y : Matrix (Fin N) (Fin N) F) :=
    ⟨⟨_, hτmem⟩, rfl⟩
  have htp : t ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ht, ← Units.val_pow_eq_pow_val, hτp y hyD, Units.val_one,
      Subalgebra.coe_one]
  have hζp : π t ^ p = 1 := by rw [← map_pow, htp, map_one]
  have hζne : π t ≠ 1 := by
    intro h1
    have h2 : π (t - 1) = 0 := by rw [map_sub, h1, map_one, sub_self]
    have h3 := (hker (t - 1)).mp h2
    apply hye
    rw [Subalgebra.coe_sub, Subalgebra.coe_one, ht, sub_mul, one_mul, sub_eq_zero] at h3
    exact h3
  have hζ0 : π t ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have : Fact p.Prime := ⟨hp⟩
  have hu_pow : (Units.mk0 (π t) hζ0) ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hζp
  have hu_ne : Units.mk0 (π t) hζ0 ≠ 1 := by
    intro h
    apply hζne
    have h' := congrArg Units.val h
    rwa [Units.val_mk0, Units.val_one] at h'
  have hord : orderOf (Units.mk0 (π t) hζ0) = p := orderOf_eq_prime hu_pow hu_ne
  have hdvd : p ∣ Nat.card (Units K) := by
    have h := orderOf_dvd_natCard (Units.mk0 (π t) hζ0)
    rwa [hord] at h
  have : Module.Finite F K := Module.Finite.of_finite
  have hcard : Nat.card K =
      Nat.card F ^ blockDegree (Algebra.adjoin F (Units.val '' (σ '' (D : Set X)))) e := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hdeg]
  rw [Nat.card_units, hcard] at hdvd
  exact hdvd

end BlockDeg

end CFSG.StandardType.TableCRes
