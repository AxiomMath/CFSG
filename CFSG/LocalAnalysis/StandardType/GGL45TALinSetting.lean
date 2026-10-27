module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearDescent
public import CFSG.LocalAnalysis.StandardType.GGL45TACyclic

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.StandardType.LinearFieldFix CFSG.LocalAnalysis.GLTheoremA

variable {d : ℕ} {k : Type} [Field k] {K : Type} [Group K]

theorem scalar_mem_center {z : GL (Fin d) k} (hz : z ∈ LargeEvenScalars (Fin d) k) :
    z ∈ Subgroup.center (GL (Fin d) k) := by
  obtain ⟨c, rfl⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact (TypeA.PGLTor.commute_scalar c g).eq.symm

theorem conj_mem_sl (x : GL (Fin d) k) {h : GL (Fin d) k} (hh : h ∈ LargeEvenSLGroup (Fin d) k) :
    x * h * x⁻¹ ∈ LargeEvenSLGroup (Fin d) k := by
  rw [TypeA.mem_largeEvenSLGroup_iff] at hh ⊢
  have hx : (x : Matrix (Fin d) (Fin d) k).det * ((x⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hh, mul_one, hx]

theorem map_mem_sl (σ : k ≃+* k) {h : GL (Fin d) k} (hh : h ∈ LargeEvenSLGroup (Fin d) k) :
    Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSLGroup (Fin d) k :=
  YS09Field.sl_map_mem σ h hh

theorem mem_scalars_of_conj_eq (hd : 3 ≤ d) {π : LargeEvenSLGroup (Fin d) k →* K}
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) {c : GL (Fin d) k}
    (hc : ∀ h h' : LargeEvenSLGroup (Fin d) k, (h' : GL (Fin d) k) = c * h * c⁻¹ → π h' = π h) :
    c ∈ LargeEvenScalars (Fin d) k := by
  have hcomm : ∀ g ∈ LargeEvenSLGroup (Fin d) k, Commute c g := by
    intro g hg
    refine commute_of_commutator_mem_center (commutator_slGroup hd) (fun g hg => ?_) hg
    let h : LargeEvenSLGroup (Fin d) k := ⟨g, hg⟩
    let h' : LargeEvenSLGroup (Fin d) k := ⟨c * g * c⁻¹, conj_mem_sl c hg⟩
    have h1 : π h' = π h := hc h h' rfl
    have h2 : h' * h⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := scalar_mem_center (hker _ h2)
    rw [commutatorElement_def]
    exact h3
  exact mem_scalars_of_commute_elemSL c fun i j hij => hcomm _ (elemSL k hij).2

@[expose] def Implements (π : LargeEvenSLGroup (Fin d) k →* K) (e : MulAut K) (x : GL (Fin d) k) :
    Prop :=
  ∀ h h' : LargeEvenSLGroup (Fin d) k, (h' : GL (Fin d) k) = x * h * x⁻¹ → e (π h) = π h'

@[expose] def SemilinImpl (π : LargeEvenSLGroup (Fin d) k →* K) (γ : MulAut K) (g : GL (Fin d) k)
    (σ : k ≃+* k) : Prop :=
  ∀ h h' : LargeEvenSLGroup (Fin d) k,
    (h' : GL (Fin d) k) = g * Matrix.GeneralLinearGroup.map σ.toRingHom h * g⁻¹ → γ (π h) = π h'

variable {π : LargeEvenSLGroup (Fin d) k →* K}

theorem implements_unique (hd : 3 ≤ d)
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) {e : MulAut K}
    {x y : GL (Fin d) k} (hx : Implements π e x) (hy : Implements π e y) :
    y⁻¹ * x ∈ LargeEvenScalars (Fin d) k := by
  refine mem_scalars_of_conj_eq hd hker fun h h' hh' => ?_
  let m : LargeEvenSLGroup (Fin d) k := ⟨x * h * x⁻¹, conj_mem_sl x h.2⟩
  have h1 : e (π h) = π m := hx h m rfl
  have h2 : e (π h') = π m := hy h' m (by
    change x * (h : GL (Fin d) k) * x⁻¹ = y * (h' : GL (Fin d) k) * y⁻¹
    rw [hh']
    group)
  exact e.injective (h2.trans h1.symm)

theorem Implements.scalar_mul {e : MulAut K} {x : GL (Fin d) k} (hx : Implements π e x)
    {z : GL (Fin d) k} (hz : z ∈ LargeEvenScalars (Fin d) k) : Implements π e (z * x) := by
  intro h h' hh'
  apply hx h h'
  rw [hh']
  have hzc := Subgroup.mem_center_iff.mp (scalar_mem_center hz)
  calc z * x * (h : GL (Fin d) k) * (z * x)⁻¹ = z * (x * h * x⁻¹) * z⁻¹ := by group
    _ = x * h * x⁻¹ * z * z⁻¹ := by rw [← hzc (x * h * x⁻¹)]
    _ = x * h * x⁻¹ := by group

theorem implements_one_of_scalar {z : GL (Fin d) k} (hz : z ∈ LargeEvenScalars (Fin d) k) :
    Implements π 1 z := by
  intro h h' hh'
  have hzc := Subgroup.mem_center_iff.mp (scalar_mem_center hz)
  have : h' = h := Subtype.ext (by
    rw [hh']
    calc z * (h : GL (Fin d) k) * z⁻¹ = h * z * z⁻¹ := by rw [hzc]
      _ = h := by group)
  rw [this, MulAut.one_apply]

theorem Implements.mul {e e' : MulAut K} {x y : GL (Fin d) k} (hx : Implements π e x)
    (hy : Implements π e' y) : Implements π (e * e') (x * y) := by
  intro h h' hh'
  let m : LargeEvenSLGroup (Fin d) k := ⟨y * h * y⁻¹, conj_mem_sl y h.2⟩
  rw [MulAut.mul_apply, hy h m rfl]
  apply hx m h'
  change (h' : GL (Fin d) k) = x * (y * h * y⁻¹) * x⁻¹
  rw [hh']
  group

theorem Implements.inv {e : MulAut K} {x : GL (Fin d) k} (hx : Implements π e x) :
    Implements π e⁻¹ x⁻¹ := by
  intro h h' hh'
  have h1 : e (π h') = π h := hx h' h (by rw [hh']; group)
  rw [← h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem Implements.pow {e : MulAut K} {x : GL (Fin d) k} (hx : Implements π e x) (n : ℕ) :
    Implements π (e ^ n) (x ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact implements_one_of_scalar ⟨1, map_one _⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul hx

theorem mem_scalars_of_implements_one (hd : 3 ≤ d)
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) {x : GL (Fin d) k}
    (hx : Implements π 1 x) : x ∈ LargeEvenScalars (Fin d) k := by
  have h := implements_unique hd hker hx (implements_one_of_scalar (π := π) ⟨1, map_one _⟩)
  rwa [inv_one, one_mul] at h

theorem SemilinImpl.conj {γ : MulAut K} {g : GL (Fin d) k} {σ : k ≃+* k}
    (hγ : SemilinImpl π γ g σ) {e : MulAut K} {x : GL (Fin d) k} (hx : Implements π e x) :
    Implements π (γ * e * γ⁻¹) (g * Matrix.GeneralLinearGroup.map σ.toRingHom x * g⁻¹) := by
  intro h h' hh'
  set σM := Matrix.GeneralLinearGroup.map (n := Fin d) σ.toRingHom with hσM
  set σM' := Matrix.GeneralLinearGroup.map (n := Fin d) σ⁻¹.toRingHom with hσM'
  have hσσ : ∀ y : GL (Fin d) k, σM (σM' y) = y := fun y => by
    rw [hσM, hσM', ← YS09Field.glMap_mul, mul_inv_cancel, YS09Field.glMap_one]
  have hmem : σM' (g⁻¹ * h * g) ∈ LargeEvenSLGroup (Fin d) k := by
    refine map_mem_sl σ⁻¹ ?_
    have := conj_mem_sl g⁻¹ h.2
    rwa [inv_inv] at this
  let h₁ : LargeEvenSLGroup (Fin d) k := ⟨σM' (g⁻¹ * h * g), hmem⟩
  have hh₁ : γ (π h₁) = π h := hγ h₁ h (by
    change (h : GL (Fin d) k) = g * σM (σM' (g⁻¹ * h * g)) * g⁻¹
    rw [hσσ]
    group)
  let m : LargeEvenSLGroup (Fin d) k := ⟨x * h₁ * x⁻¹, conj_mem_sl x h₁.2⟩
  have hm : e (π h₁) = π m := hx h₁ m rfl
  have hγm : γ (π m) = π h' := hγ m h' (by
    rw [hh']
    change g * σM x * g⁻¹ * (h : GL (Fin d) k) * (g * σM x * g⁻¹)⁻¹ =
      g * σM (x * σM' (g⁻¹ * h * g) * x⁻¹) * g⁻¹
    rw [map_mul, map_mul, map_inv, hσσ]
    group)
  rw [MulAut.mul_apply, MulAut.mul_apply, ← hh₁, MulAut.inv_apply, MulEquiv.symm_apply_apply,
    hm, hγm]

theorem coe_scalar_mul (c : kˣ) (x : GL (Fin d) k) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c * x : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
      (c : k) • (x : Matrix (Fin d) (Fin d) k) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_eq_diagonal_mul]

theorem map_scalar (σ : k ≃+* k) (c : kˣ) :
    Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map σ.toRingHom.toMonoidHom c) := by
  ext i j
  simp only [YS09Field.coe_glMap, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem scalar_injective (hd : 1 ≤ d) :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin d) (R := k)) := by
  intro a b h
  have := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k) ⟨0, hd⟩ ⟨0, hd⟩) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at this
  exact Units.ext this

structure LinSetting (p q₀ d : ℕ) (k : Type) [Field k] [Finite k] (K : Type) [Group K]
    (ψ : MulAut K) (E : Subgroup (MulAut K)) where
  π : LargeEvenSLGroup (Fin d) k →* K
  surj : Function.Surjective π
  ker_le : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k
  τ : k ≃+* k
  τ_apply : ∀ a, τ a = a ^ q₀
  hp : p.Prime
  hp2 : p ≠ 2
  char_two : CharP k 2
  card_k : Nat.card k = q₀ ^ p
  dvd_q₀ : (p : ℤ) ∣ (q₀ : ℤ) - 1
  dvd_d : p ∣ d
  three_le : 3 ≤ d
  ψ_impl : SemilinImpl π ψ 1 τ
  E_impl : ∀ e ∈ E, ∃ x : GL (Fin d) k, Implements π e x
  semilin : ∀ γ : MulAut K, GGL45IsPElt p γ →
    ∃ (g : GL (Fin d) k) (σ : k ≃+* k) (m : ℕ), σ ^ p ^ m = 1 ∧ SemilinImpl π γ g σ
  ψ_pow : ψ ^ p = 1
  elem : IsElemAbelian p E
  card_E : p ^ 2 ≤ Nat.card E
  comm : ∀ e ∈ E, e * ψ = ψ * e
  sat : ∀ x : K, x ^ p = 1 → (∀ e ∈ E, e x = x) → ψ x = x → MulAut.conj x ∈ E
  rk : ∀ R₀ Q : Subgroup K, IsElemAbelian p R₀ → (∀ r ∈ R₀, ψ r = r) → IsPGroup 2 Q →
    Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) → R₀ ≤ Subgroup.normalizer (Q : Set K) →
    Nat.card R₀ * p ≤ Nat.card E * p ^ 2
  pik : ∃ P : Subgroup (MulAut K), P ≤ E ∧ Nat.card E ≤ p * Nat.card P ∧ ∀ e ∈ P,
    ∃ γ : MulAut K, GGL45IsPElt p γ ∧ (∀ e' ∈ E, γ * e' = e' * γ) ∧ e = γ * ψ⁻¹ * γ⁻¹ * ψ
  a2 : d = 3 → p ∣ Nat.card (Subgroup.center K)

namespace LinSetting

variable {p q₀ : ℕ} [Finite k] {ψ : MulAut K} {E : Subgroup (MulAut K)}

@[expose] def IsLift (S : LinSetting p q₀ d k K ψ E) (x : GL (Fin d) k) : Prop :=
  x ^ p = 1 ∧ ∃ e ∈ E, Implements S.π e x

theorem conj_ψ (S : LinSetting p q₀ d k K ψ E) {e : MulAut K} (he : e ∈ E) : ψ * e * ψ⁻¹ = e := by
  rw [← S.comm e he, mul_inv_cancel_right]

theorem exists_map_tau_eq (S : LinSetting p q₀ d k K ψ E) {e : MulAut K} (he : e ∈ E)
    {x : GL (Fin d) k} (hx : Implements S.π e x) :
    ∃ c : kˣ, Matrix.GeneralLinearGroup.map S.τ.toRingHom x =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * x := by
  have h1 := S.ψ_impl.conj hx
  rw [S.conj_ψ he, one_mul, inv_one, mul_one] at h1
  obtain ⟨c, hc⟩ := implements_unique S.three_le S.ker_le h1 hx
  refine ⟨c, ?_⟩
  have hc' : x⁻¹ * Matrix.GeneralLinearGroup.map S.τ.toRingHom x =
      Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
  have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨c, rfl⟩)
  calc Matrix.GeneralLinearGroup.map S.τ.toRingHom x
      = x * (x⁻¹ * Matrix.GeneralLinearGroup.map S.τ.toRingHom x) := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * x := by rw [hc', hcen x]

theorem card_units (S : LinSetting p q₀ d k K ψ E) :
    (Nat.card kˣ : ℤ) = (q₀ : ℤ) ^ p - 1 := by
  have h1 : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [Nat.card_units, Nat.cast_sub h1, S.card_k]
  push_cast
  ring

theorem exists_lift (S : LinSetting p q₀ d k K ψ E) {e : MulAut K} (he : e ∈ E) :
    ∃ x : GL (Fin d) k, x ^ p = 1 ∧ Implements S.π e x := by
  obtain ⟨x, hx⟩ := S.E_impl e he
  obtain ⟨c, hc⟩ := S.exists_map_tau_eq he hx
  have hd1 : 1 ≤ d := le_trans (by norm_num) S.three_le
  haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
  obtain ⟨μ, B, hB⟩ := exists_descend_of_map_eq_smul S.τ x c (by rw [hc, coe_scalar_mul])
  set x' : GL (Fin d) k := Matrix.GeneralLinearGroup.map (FQ.fixF S.τ).subtype B with hx'def
  have hx'eq : x' = Matrix.GeneralLinearGroup.scalar (Fin d) μ * x :=
    Units.ext (by rw [coe_scalar_mul]; exact hB)
  have hx'impl : Implements S.π e x' := by rw [hx'eq]; exact hx.scalar_mul ⟨μ, rfl⟩
  have hx'fix : Matrix.GeneralLinearGroup.map S.τ.toRingHom x' = x' := FQ.glMap_subtype_fixed S.τ B
  have hpow : Implements S.π 1 (x' ^ p) := by
    have h := hx'impl.pow p
    rwa [S.elem.2 e he] at h
  obtain ⟨ν, hν⟩ := mem_scalars_of_implements_one S.three_le S.ker_le hpow
  have hντ : Units.map S.τ.toRingHom.toMonoidHom ν = ν := by
    apply scalar_injective hd1
    rw [← map_scalar, hν, map_pow, hx'fix]
  have hνq : ν ^ ((1 : ℤ) * q₀) = ν := by
    apply Units.ext
    have h := congrArg Units.val hντ
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, S.τ_apply] at h
    rw [one_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    exact h
  obtain ⟨ν', hν'⟩ := ggL45TA_exists_pow_eq_of_fixed (C := kˣ) S.hp S.hp2 (Or.inl rfl)
    S.card_units (by simpa using S.dvd_q₀) ν hνq
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin d) ν'⁻¹ * x', ?_, hx'impl.scalar_mul ⟨ν'⁻¹, rfl⟩⟩
  have hcen := Subgroup.mem_center_iff.mp (scalar_mem_center (d := d) (k := k) ⟨ν'⁻¹, rfl⟩)
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) ν'⁻¹) x' := (hcen x').symm
  rw [hcomm.mul_pow, ← map_pow, ← hν, ← map_mul, hν', inv_pow, inv_mul_cancel, map_one]

end LinSetting

end CFSG.StandardType.GGL45TA
