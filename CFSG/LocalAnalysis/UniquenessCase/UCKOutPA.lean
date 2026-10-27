module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossDefs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.OutP

open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
  (diagGL permGL coe_diagGL coe_permGL permGL_mul_diagGL_mul_inv)

theorem sq_dvd_pow_sub_one {p ℓ f : ℕ} (hp : p.Prime) (hℓ : 1 ≤ ℓ) (hpf : p ∣ f)
    (h : p ∣ ℓ ^ f - 1) : p ^ 2 ∣ ℓ ^ f - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, rfl⟩ := hpf
  have hpow : ℓ ^ (p * g) = (ℓ ^ g) ^ p := by rw [← pow_mul, mul_comm]
  rw [hpow] at h ⊢
  have hx1 : 1 ≤ ℓ ^ g := Nat.one_le_pow _ _ hℓ
  have hxp : 1 ≤ (ℓ ^ g) ^ p := Nat.one_le_pow _ _ hx1
  have h1 : ((ℓ ^ g : ℕ) : ZMod p) = 1 := by
    have h2 : (((ℓ ^ g) ^ p - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rw [Nat.cast_sub hxp, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h2
    exact sub_eq_zero.1 h2
  have h3 : p ∣ ℓ ^ g - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hx1, h1, Nat.cast_one, sub_self]
  have h4 : (p : ℤ) ∣ ((ℓ ^ g : ℕ) : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.2 h3
    rwa [Nat.cast_sub hx1, Nat.cast_one] at this
  have h5 := dvd_sub_pow_of_dvd_sub h4 1
  rw [pow_one, one_pow] at h5
  have h6 : (((p ^ 2 : ℕ)) : ℤ) ∣ (((ℓ ^ g) ^ p - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hxp, Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
    exact h5
  exact Int.natCast_dvd_natCast.1 h6

theorem sq_dvd_pow_add_one {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpf : p ∣ f)
    (h : p ∣ ℓ ^ f + 1) : p ^ 2 ∣ ℓ ^ f + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, rfl⟩ := hpf
  have hpow : ℓ ^ (p * g) = (ℓ ^ g) ^ p := by rw [← pow_mul, mul_comm]
  rw [hpow] at h ⊢
  have h1 : ((ℓ ^ g : ℕ) : ZMod p) + 1 = 0 := by
    have h2 : (((ℓ ^ g) ^ p + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    rwa [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h2
  have h3 : p ∣ ℓ ^ g + 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, h1]
  have h4 : (p : ℤ) ∣ ((ℓ ^ g : ℕ) : ℤ) - (-1) := by
    have := Int.natCast_dvd_natCast.2 h3
    rwa [Nat.cast_add, Nat.cast_one, ← sub_neg_eq_add] at this
  have h5 := dvd_sub_pow_of_dvd_sub h4 1
  rw [pow_one, (hp.odd_of_ne_two hp2).neg_one_pow, sub_neg_eq_add] at h5
  have h6 : (((p ^ 2 : ℕ)) : ℤ) ∣ (((ℓ ^ g) ^ p + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_one]
    exact h5
  exact Int.natCast_dvd_natCast.1 h6

variable {F : Type} [Field F]

@[expose] noncomputable def powDiag (κ : Fˣ) : GL (Fin 5) F :=
  diagGL 5 fun i => κ ^ (i : ℕ)

theorem scalar_mul_comm (c : Fˣ) (g : GL (Fin 5) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 5) c * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
  ext : 1
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : F) (fun r => Commute.all (c : F) r) _).eq

theorem scalar_eq_diagGL (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 5) c = diagGL 5 fun _ => c := by
  ext : 1
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagGL, Matrix.scalar_apply]

theorem eq_of_diagGL_eq_scalar {u : Fin 5 → Fˣ} {c : Fˣ}
    (h : diagGL 5 u = Matrix.GeneralLinearGroup.scalar (Fin 5) c) (i : Fin 5) : u i = c := by
  have h1 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) i i) h
  simp only [coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

theorem conj_scalar_mul (c : Fˣ) (U W : GL (Fin 5) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 5) c * U * W *
        (Matrix.GeneralLinearGroup.scalar (Fin 5) c * U)⁻¹ = U * W * U⁻¹ := by
  calc Matrix.GeneralLinearGroup.scalar (Fin 5) c * U * W *
        (Matrix.GeneralLinearGroup.scalar (Fin 5) c * U)⁻¹
      = Matrix.GeneralLinearGroup.scalar (Fin 5) c * (U * W * U⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin 5) c)⁻¹ := by group
    _ = U * W * U⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) c *
          (Matrix.GeneralLinearGroup.scalar (Fin 5) c)⁻¹ := by rw [scalar_mul_comm]
    _ = U * W * U⁻¹ := by group

theorem exists_ne_zero_of_row (B : GL (Fin 5) F) (i : Fin 5) :
    ∃ j, (B : Matrix (Fin 5) (Fin 5) F) i j ≠ 0 := by
  by_contra h
  push Not at h
  exact (Matrix.isUnits_det_units B).ne_zero (Matrix.det_eq_zero_of_row_eq_zero i h)

theorem eq_of_conj_diagGL {B : GL (Fin 5) F} {v : Fin 5 → Fˣ} {μ : Fˣ}
    (h : B * diagGL 5 v * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) μ * diagGL 5 v)
    {i j : Fin 5} (hij : (B : Matrix (Fin 5) (Fin 5) F) i j ≠ 0) : v j = μ * v i := by
  have h1 : B * diagGL 5 v = Matrix.GeneralLinearGroup.scalar (Fin 5) μ * diagGL 5 v * B := by
    rw [← h, inv_mul_cancel_right]
  have h2 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) i j) h1
  simp only [Units.val_mul, coe_diagGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul] at h2
  apply Units.ext
  rw [Units.val_mul]
  apply mul_left_cancel₀ hij
  rw [h2]
  ring

theorem fin_eq_of_pow_eq {ζ : Fˣ} (hζ : orderOf ζ = 5) {i j s : Fin 5}
    (h : ζ ^ (j : ℕ) = ζ ^ ((i : ℕ) + (s : ℕ))) : j = i + s := by
  rw [pow_eq_pow_iff_modEq, hζ] at h
  unfold Nat.ModEq at h
  apply Fin.ext
  rw [Fin.val_add]
  have hj := j.isLt
  omega

theorem exists_shift {ζ : Fˣ} (hζ : orderOf ζ = 5) {B : GL (Fin 5) F} {μ : Fˣ}
    (h : B * powDiag ζ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) μ * powDiag ζ) :
    ∃ s : Fin 5, ∀ i j, (B : Matrix (Fin 5) (Fin 5) F) i j ≠ 0 → j = i + s := by
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero_of_row B 0
  have hμ : ζ ^ (j₀ : ℕ) = μ := by
    have := eq_of_conj_diagGL (v := fun i => ζ ^ (i : ℕ)) h hj₀
    simpa using this
  refine ⟨j₀, fun i j hij => fin_eq_of_pow_eq hζ ?_⟩
  have := eq_of_conj_diagGL (v := fun i => ζ ^ (i : ℕ)) h hij
  rw [this, ← hμ, ← pow_add, add_comm]

theorem shift_eq_zero {ζ : Fˣ} (hζ : orderOf ζ = 5) {B : GL (Fin 5) F} {μ : Fˣ} {s : Fin 5}
    (h : B * diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] * B⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) μ * diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1])
    (hs : ∀ i j, (B : Matrix (Fin 5) (Fin 5) F) i j ≠ 0 → j = i + s) : s = 0 := by
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  have hdiag : ∀ i, (B : Matrix (Fin 5) (Fin 5) F) i (i + s) ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne_zero_of_row B i
    rwa [← hs i j hj]
  have key : ∀ i, (![ζ, ζ⁻¹, 1, 1, 1] : Fin 5 → Fˣ) (i + s) = μ * ![ζ, ζ⁻¹, 1, 1, 1] i :=
    fun i => eq_of_conj_diagGL h (hdiag i)
  fin_cases s
  · rfl
  · have a := key 2
    have b := key 4
    simp at a b
    exact absurd (b.trans a.symm) hζ1
  · have a := key 2
    have b := key 3
    simp at a b
    exact absurd (b.trans a.symm) hζ1
  · have a := key 4
    have b := key 2
    simp at a b
    exact absurd (b.trans a.symm) hζ1
  · have a := key 3
    have b := key 0
    simp at a b
    rw [← a, one_mul] at b
    exact absurd b.symm hζ1

theorem eq_scalar_mul_powDiag {ζ : Fˣ} (hζ : orderOf ζ = 5) {B : GL (Fin 5) F}
    (h₁ : ∃ μ : Fˣ, B * powDiag ζ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 5) μ * powDiag ζ)
    (h₂ : ∃ μ : Fˣ, B * diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] * B⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) μ * diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1])
    (h₃ : ∃ μ : Fˣ, B * permGL 5 (finRotate 5) * B⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) μ * permGL 5 (finRotate 5)) :
    ∃ a κ : Fˣ, κ ^ 5 = 1 ∧ B = Matrix.GeneralLinearGroup.scalar (Fin 5) a * powDiag κ := by
  obtain ⟨μ₁, e₁⟩ := h₁
  obtain ⟨μ₂, e₂⟩ := h₂
  obtain ⟨κ, e₃⟩ := h₃
  obtain ⟨s, hs⟩ := exists_shift hζ e₁
  have hs0 := shift_eq_zero hζ e₂ hs
  subst hs0
  simp only [add_zero] at hs
  have hm : ∀ i, (B : Matrix (Fin 5) (Fin 5) F) i i ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne_zero_of_row B i
    obtain rfl := hs i j hj
    exact hj
  let m : Fin 5 → Fˣ := fun i => Units.mk0 _ (hm i)
  have hBm : B = diagGL 5 m := by
    ext i j : 2
    rw [coe_diagGL]
    by_cases hij : i = j
    · subst hij
      simp [m]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_contra hne
      exact hij (hs i j hne).symm
  have hstep : ∀ i, m i = κ * m ((finRotate 5)⁻¹ i) := by
    have h1 : B * (permGL 5 (finRotate 5) * B⁻¹ * (permGL 5 (finRotate 5))⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin 5) κ := by
      calc B * (permGL 5 (finRotate 5) * B⁻¹ * (permGL 5 (finRotate 5))⁻¹)
          = B * permGL 5 (finRotate 5) * B⁻¹ * (permGL 5 (finRotate 5))⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 5) κ := by rw [e₃]; group
    rw [hBm, ← map_inv, permGL_mul_diagGL_mul_inv, ← map_mul] at h1
    intro i
    have h2 := eq_of_diagGL_eq_scalar h1 i
    simp only [Pi.mul_apply, Pi.inv_apply] at h2
    rw [← h2, inv_mul_cancel_right]
  have r1 := hstep 1
  have r2 := hstep 2
  have r3 := hstep 3
  have r4 := hstep 4
  have r0 := hstep 0
  have e10 : (finRotate 5)⁻¹ 1 = 0 := by decide
  have e21 : (finRotate 5)⁻¹ 2 = 1 := by decide
  have e32 : (finRotate 5)⁻¹ 3 = 2 := by decide
  have e43 : (finRotate 5)⁻¹ 4 = 3 := by decide
  have e04 : (finRotate 5)⁻¹ 0 = 4 := by decide
  rw [e10] at r1
  rw [e21] at r2
  rw [e32] at r3
  rw [e43] at r4
  rw [e04] at r0
  have v0 : m 0 = m 0 * κ ^ 0 := by rw [pow_zero, mul_one]
  have v1 : m 1 = m 0 * κ ^ 1 := by rw [r1, pow_one, mul_comm]
  have v2 : m 2 = m 0 * κ ^ 2 := by rw [r2, v1, mul_left_comm, ← pow_succ']
  have v3 : m 3 = m 0 * κ ^ 3 := by rw [r3, v2, mul_left_comm, ← pow_succ']
  have v4 : m 4 = m 0 * κ ^ 4 := by rw [r4, v3, mul_left_comm, ← pow_succ']
  have hκ : κ ^ 5 = 1 := by
    have : m 0 * κ ^ 5 = m 0 := by rw [pow_succ', mul_left_comm, ← v4, ← r0]
    exact mul_eq_left.1 this
  refine ⟨m 0, κ, hκ, ?_⟩
  rw [hBm, powDiag, scalar_eq_diagGL, ← map_mul]
  congr 1
  funext i
  fin_cases i
  · exact v0
  · exact v1
  · exact v2
  · exact v3
  · exact v4

@[expose] noncomputable def torusFive (ζ : Fˣ) : Subgroup (GL (Fin 5) F) :=
  Subgroup.map (diagGL 5) (Subgroup.pi Set.univ fun _ => Subgroup.zpowers ζ)

theorem diagGL_mem_torusFive {ζ : Fˣ} {u : Fin 5 → Fˣ} (hu : ∀ i, u i ∈ Subgroup.zpowers ζ) :
    (diagGL 5 u : GL (Fin 5) F) ∈ torusFive ζ :=
  Subgroup.mem_map.2 ⟨u, (Subgroup.mem_pi _).2 (fun i _ => hu i), rfl⟩

theorem pow_five_of_mem_zpowers {ζ : Fˣ} (hζ : orderOf ζ = 5) {x : Fˣ}
    (hx : x ∈ Subgroup.zpowers ζ) : x ^ 5 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← hζ]
  exact orderOf_dvd_of_mem_zpowers hx

theorem pow_five_of_mem_torusFive {ζ : Fˣ} (hζ : orderOf ζ = 5) {g : GL (Fin 5) F}
    (hg : g ∈ torusFive ζ) : g ^ 5 = 1 := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  rw [← map_pow]
  have : u ^ 5 = 1 := by
    funext i
    exact pow_five_of_mem_zpowers hζ ((Subgroup.mem_pi _).1 hu i (Set.mem_univ i))
  rw [this, map_one]

theorem permGL_mem_normalizer_torusFive {ζ : Fˣ} (σ : Equiv.Perm (Fin 5)) :
    (permGL 5 σ : GL (Fin 5) F) ∈ Subgroup.normalizer (torusFive ζ : Set (GL (Fin 5) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
    rw [permGL_mul_diagGL_mul_inv]
    exact diagGL_mem_torusFive (fun i => (Subgroup.mem_pi _).1 hu (σ⁻¹ i) (Set.mem_univ _))
  · intro hg
    obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 hg
    have : g = permGL 5 σ⁻¹ * diagGL 5 u * (permGL 5 σ⁻¹)⁻¹ := by
      rw [hu', map_inv, inv_inv]
      group
    rw [this, permGL_mul_diagGL_mul_inv]
    exact diagGL_mem_torusFive (fun i => (Subgroup.mem_pi _).1 hu _ (Set.mem_univ _))

theorem isPGroup_torusFive_sup {ζ : Fˣ} (hζ : orderOf ζ = 5) :
    IsPGroup 5 ↥(torusFive ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) F)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hT : IsPGroup 5 ↥(torusFive ζ : Subgroup (GL (Fin 5) F)) := by
    intro x
    exact ⟨1, by apply Subtype.ext; simpa using pow_five_of_mem_torusFive hζ x.2⟩
  have hC : IsPGroup 5 ↥(Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) F)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow]
    have : (finRotate 5) ^ 5 = 1 := by decide
    rw [this, map_one]
  exact IsPGroup.to_sup_of_normal_left' hT hC
    (Subgroup.zpowers_le.2 (permGL_mem_normalizer_torusFive _))

theorem mem_range_conj_of_fixes {S P : Type} [Group S] [Group P] [Finite P]
    (ι : S →* GL (Fin 5) F) (hι : Function.Injective ι) (π : S →* P)
    (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ∃ c : Fˣ, ι s = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    {ζ : Fˣ} (hζ : orderOf ζ = 5) (hD : ∀ κ : Fˣ, κ ^ 5 = 1 → ∃ s : S, ι s = powDiag κ)
    (hd : ∃ s : S, ι s = diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1])
    (hc : ∃ s : S, ι s = permGL 5 (finRotate 5))
    (A : GL (Fin 5) F) (γ : S → S) (hγ : ∀ s, ι (γ s) = A * ι s * A⁻¹)
    (β : MulAut P) (hβ : ∀ s, β (π s) = π (γ s))
    {T : Subgroup P} (hT : IsPGroup 5 T) (hTi : ¬ 5 ∣ T.index) (hβT : ∀ t ∈ T, β t = t) :
    β ∈ (MulAut.conj : P →* MulAut P).range := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s₁, hs₁⟩ := hD ζ (by rw [← hζ]; exact pow_orderOf_eq_one ζ)
  obtain ⟨s₂, hs₂⟩ := hd
  obtain ⟨s₃, hs₃⟩ := hc
  set Q₀ : Subgroup S :=
    (torusFive ζ ⊔ Subgroup.zpowers (permGL 5 (finRotate 5) : GL (Fin 5) F)).comap ι with hQ₀
  have hQp : IsPGroup 5 (Q₀.map π) :=
    ((isPGroup_torusFive_sup hζ).comap_of_injective ι hι).map π
  have hm₁ : π s₁ ∈ Q₀.map π := by
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_comap.2 (Subgroup.mem_sup_left ?_))
    rw [hs₁]
    exact diagGL_mem_torusFive (fun i => Subgroup.npow_mem_zpowers ζ _)
  have hm₂ : π s₂ ∈ Q₀.map π := by
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_comap.2 (Subgroup.mem_sup_left ?_))
    rw [hs₂]
    refine diagGL_mem_torusFive (fun i => ?_)
    fin_cases i
    · exact Subgroup.mem_zpowers ζ
    · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
    · exact Subgroup.one_mem _
  have hm₃ : π s₃ ∈ Q₀.map π := by
    refine Subgroup.mem_map_of_mem π (Subgroup.mem_comap.2 (Subgroup.mem_sup_right ?_))
    rw [hs₃]
    exact Subgroup.mem_zpowers _
  obtain ⟨R, hQR⟩ := hQp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P R (hT.toSylow hTi)
  have hgT : ∀ x ∈ Q₀.map π, g * x * g⁻¹ ∈ T := by
    intro x hx
    have h1 : ((g • R : Sylow 5 P) : Subgroup P) =
        (R : Subgroup P).map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      rfl
    have h2 : g * x * g⁻¹ ∈ ((g • R : Sylow 5 P) : Subgroup P) := by
      rw [h1]
      exact ⟨x, hQR hx, rfl⟩
    rw [hg] at h2
    exact h2
  obtain ⟨G, rfl⟩ := hπ g
  have hrel : ∀ s : S, π s ∈ Q₀.map π → ∃ μ : Fˣ,
      (ι G)⁻¹ * A * ι G * ι s * ((ι G)⁻¹ * A * ι G)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 5) μ * ι s := by
    intro s hs
    have h1 := hβT _ (hgT _ hs)
    rw [← map_inv, ← map_mul, ← map_mul, hβ] at h1
    have h2 : π ((G * s * G⁻¹)⁻¹ * γ (G * s * G⁻¹)) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨c, hc⟩ := hker _ h2
    refine ⟨c, ?_⟩
    rw [map_mul, map_inv, hγ] at hc
    simp only [map_mul, map_inv] at hc
    have hX : A * (ι G * ι s * (ι G)⁻¹) * A⁻¹ =
        ι G * ι s * (ι G)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
      rw [← hc]
      group
    calc (ι G)⁻¹ * A * ι G * ι s * ((ι G)⁻¹ * A * ι G)⁻¹
        = (ι G)⁻¹ * (A * (ι G * ι s * (ι G)⁻¹) * A⁻¹) * ι G := by group
      _ = (ι G)⁻¹ * (ι G * ι s * (ι G)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 5) c) * ι G := by
          rw [hX]
      _ = (ι G)⁻¹ * (ι G * ι s * (ι G)⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin 5) c * ι G) := by group
      _ = (ι G)⁻¹ * (ι G * ι s * (ι G)⁻¹) *
            (ι G * Matrix.GeneralLinearGroup.scalar (Fin 5) c) := by rw [scalar_mul_comm]
      _ = ι s * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 5) c * ι s := (scalar_mul_comm c _).symm
  obtain ⟨a, κ, hκ, hB⟩ := eq_scalar_mul_powDiag hζ (by rw [← hs₁]; exact hrel s₁ hm₁)
    (by rw [← hs₂]; exact hrel s₂ hm₂) (by rw [← hs₃]; exact hrel s₃ hm₃)
  obtain ⟨D, hD'⟩ := hD κ hκ
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 5) a * ι (G * D * G⁻¹) := by
    have h1 : A = ι G * ((ι G)⁻¹ * A * ι G) * (ι G)⁻¹ := by group
    rw [h1, hB, map_mul, map_mul, map_inv, hD', ← mul_assoc (ι G),
      ← scalar_mul_comm a (ι G)]
    group
  refine ⟨π (G * D * G⁻¹), ?_⟩
  ext y
  obtain ⟨s, rfl⟩ := hπ y
  rw [MulAut.conj_apply, hβ, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply hι
  rw [hγ, hA, conj_scalar_mul]
  simp only [map_mul, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UCK.OutP
