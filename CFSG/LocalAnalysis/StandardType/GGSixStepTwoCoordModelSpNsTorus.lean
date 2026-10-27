module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusElt

public section

open Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace CoordSpNs

section Twist

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D] {p : ℕ}

@[expose] def IsTwist (β : LinearMap.BilinForm K D) (c : D ≃ₗ[K] D) (u : (ZMod p)ˣ)
    (T : D ≃ₗ[K] D) : Prop :=
  (∀ x y, β (T x) (T y) = β x y) ∧ ∀ x, T ((c ^ (u : ZMod p).val) x) = c (T x)

theorem pow_apply_succ (c : D ≃ₗ[K] D) (m : ℕ) (x : D) : (c ^ (m + 1)) x = c ((c ^ m) x) := by
  rw [pow_succ', LinearEquiv.mul_apply]

theorem apply_pow_of_conj {c : D ≃ₗ[K] D} (hc : c ^ p = 1) {u : (ZMod p)ˣ} {T : D ≃ₗ[K] D}
    (h : ∀ x, T ((c ^ (u : ZMod p).val) x) = c (T x)) (a : ZMod p) (x : D) :
    T ((c ^ ((u : ZMod p) * a).val) x) = (c ^ a.val) (T x) := by
  rw [← CoordSL.pow_val_pow_val hc]
  generalize a.val = m
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, h, ih, pow_apply_succ]

theorem IsTwist.apply_pow {β : LinearMap.BilinForm K D} {c : D ≃ₗ[K] D} (hc : c ^ p = 1)
    {u : (ZMod p)ˣ} {T : D ≃ₗ[K] D} (h : IsTwist β c u T) (a : ZMod p) (x : D) :
    T ((c ^ ((u : ZMod p) * a).val) x) = (c ^ a.val) (T x) :=
  apply_pow_of_conj hc h.2 a x

theorem apply_pow_of_comm {c : D ≃ₗ[K] D} {T : D →ₗ[K] D} (h : ∀ x, T (c x) = c (T x))
    (m : ℕ) (x : D) : T ((c ^ m) x) = (c ^ m) (T x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, h, ih, pow_apply_succ]

theorem pow_isom {β : LinearMap.BilinForm K D} {c : D ≃ₗ[K] D}
    (hcβ : ∀ x y, β (c x) (c y) = β x y) (m : ℕ) (x y : D) :
    β ((c ^ m) x) ((c ^ m) y) = β x y := by
  induction m generalizing x y with
  | zero => simp
  | succ m ih => rw [pow_apply_succ, pow_apply_succ, hcβ, ih]

@[expose] def twistGroup [NeZero p] (β : LinearMap.BilinForm K D) (c : D ≃ₗ[K] D)
    (hc : c ^ p = 1) : Subgroup (ZMod p)ˣ where
  carrier := {u | ∃ T : D ≃ₗ[K] D, IsTwist β c u T}
  one_mem' := ⟨LinearEquiv.refl K D, fun _ _ => rfl, fun x => by
    rw [Units.val_one, CoordSL.pow_val_one hc]
    rfl⟩
  mul_mem' := by
    rintro u v ⟨T, hT⟩ ⟨T', hT'⟩
    refine ⟨T'.trans T, fun x y => ?_, fun x => ?_⟩
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hT.1, hT'.1]
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, Units.val_mul, mul_comm,
        hT'.apply_pow hc, hT.2]
  inv_mem' := by
    rintro u ⟨T, hT⟩
    refine ⟨T.symm, fun x y => ?_, fun x => ?_⟩
    · rw [← hT.1, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    · apply T.injective
      rw [LinearEquiv.apply_symm_apply]
      have h1 := hT.apply_pow hc ((u⁻¹ : (ZMod p)ˣ) : ZMod p) (T.symm x)
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, CoordSL.pow_val_one hc,
        LinearEquiv.apply_symm_apply] at h1
      rw [h1]

theorem mem_twistGroup [NeZero p] {β : LinearMap.BilinForm K D} {c : D ≃ₗ[K] D}
    {hc : c ^ p = 1} {u : (ZMod p)ˣ} :
    u ∈ twistGroup β c hc ↔ ∃ T : D ≃ₗ[K] D, IsTwist β c u T :=
  Iff.rfl

end Twist

section Torus

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D] {s : ℕ} {κ : Type}
  {p : ℕ}

@[expose] def torD (c : D ≃ₗ[K] D) (t : Fin s → ZMod p) :
    ((Fin s → D) × (κ → K)) ≃ₗ[K] ((Fin s → D) × (κ → K)) :=
  SpNS.monoEquiv 1 fun i => c ^ (t i).val

theorem torD_apply (c : D ≃ₗ[K] D) (t : Fin s → ZMod p) (d : Fin s → D) (w : κ → K) :
    torD (κ := κ) c t (d, w) = (fun i => (c ^ (t i).val) (d i), w) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}
  {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K D} {c : D ≃ₗ[K] D}

theorem torD_isom
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hcβ : ∀ x y, β (c x) (c y) = β x y) (t : Fin s → ZMod p)
    (x y : (Fin s → D) × (κ → K)) :
    B (Φ (torD c t x)) (Φ (torD c t y)) = B (Φ x) (Φ y) :=
  SpNS.monoEquiv_isom hdec 1 (fun _ u v => pow_isom hcβ _ u v) x y

variable [NeZero p]

@[expose] noncomputable def torHomD (hc : c ^ p = 1)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hcβ : ∀ x y, β (c x) (c y) = β x y) :
    Multiplicative (Fin s → ZMod p) →* ↥(sesqUnitaryGroup B) where
  toFun t := ⟨SpNS.frameUnit Φ (torD c (toAdd t)),
    SpNS.frameUnit_mem Φ (torD_isom hdec hcβ (toAdd t))⟩
  map_one' := by
    apply Subtype.ext
    change SpNS.frameUnit Φ (torD c 0) = 1
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [SpNS.frameUnit_apply, torD_apply, Units.val_one, Module.End.one_apply]
    congr 2
    funext i
    simp
  map_mul' a b := by
    apply Subtype.ext
    change SpNS.frameUnit Φ (torD c (toAdd (a * b))) =
      SpNS.frameUnit Φ (torD c (toAdd a)) * SpNS.frameUnit Φ (torD c (toAdd b))
    rw [SpNS.frameUnit_mul]
    congr 1
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨d, w⟩ := x
    rw [LinearEquiv.trans_apply, torD_apply, torD_apply, torD_apply]
    congr 2
    funext i
    rw [toAdd_mul, Pi.add_apply, CoordSL.pow_val_add hc, LinearEquiv.mul_apply]

theorem coe_torHomD (hc : c ^ p = 1)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hcβ : ∀ x y, β (c x) (c y) = β x y) (t : Fin s → ZMod p) :
    ((torHomD hc hdec hcβ (ofAdd t) : ↥(sesqUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V) = SpNS.frameUnit Φ (torD c t) := rfl

theorem torHomD_injective [Nontrivial D] (hp : p.Prime) (hc : c ^ p = 1)
    (hfix : ∀ x, c x = x → x = 0)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hcβ : ∀ x y, β (c x) (c y) = β x y) :
    Function.Injective (torHomD (κ := κ) hc hdec hcβ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : SpNS.frameUnit Φ (torD c (toAdd a)) = SpNS.frameUnit Φ (LinearEquiv.refl K _) := by
    have := congrArg Subtype.val ha
    rw [← ofAdd_toAdd a, coe_torHomD] at this
    rw [this]
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := Φ.surjective v
    rw [SpNS.frameUnit_apply]
    rfl
  rw [SpNS.frameUnit_eq_iff] at h1
  rw [← ofAdd_toAdd a]
  convert ofAdd_zero (α := Fin s → ZMod p)
  funext i
  have hfixi : ∀ x : D, (c ^ (toAdd a i).val) x = x := fun x => by
    have h2 := congrArg (fun y : (Fin s → D) × (κ → K) => y.1 i)
      (LinearEquiv.congr_fun h1 (Pi.single i x, 0))
    simpa [torD_apply] using h2
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : D)
  apply hy
  apply hfix
  have hj : (toAdd a i) * (toAdd a i)⁻¹ = 1 := mul_inv_cancel₀ hne
  have h3 : ∀ m : ℕ, ((c ^ (toAdd a i).val) ^ m) y = y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_apply_succ, ih, hfixi]
  have h4 := h3 ((toAdd a i)⁻¹).val
  rwa [CoordSL.pow_val_pow_val hc, hj, CoordSL.pow_val_one hc] at h4

theorem torHomD_move (hc : c ^ p = 1)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hcβ : ∀ x y, β (c x) (c y) = β x y) (π : Equiv.Perm (Fin s))
    (η : Fin s → (ZMod p)ˣ) (T : Fin s → (D ≃ₗ[K] D))
    (hT : ∀ i, IsTwist β c (η (π.symm i)) (T i)) :
    ∃ w : ↥(sesqUnitaryGroup B), ∀ t : Fin s → ZMod p,
      w⁻¹ * torHomD (κ := κ) hc hdec hcβ (ofAdd t) * w =
        torHomD hc hdec hcβ (ofAdd fun i => (η i : ZMod p) * t (π i)) := by
  set M := SpNS.monoEquiv (κ := κ) π.symm T with hM
  have hMB : ∀ x y, B (Φ (M x)) (Φ (M y)) = B (Φ x) (Φ y) :=
    SpNS.monoEquiv_isom hdec π.symm fun i => (hT i).1
  refine ⟨⟨SpNS.frameUnit Φ M, SpNS.frameUnit_mem Φ hMB⟩, fun t => ?_⟩
  set t' : Fin s → ZMod p := fun i => (η i : ZMod p) * t (π i) with ht'
  have hconj : SpNS.frameUnit Φ M * SpNS.frameUnit Φ (torD c t') * (SpNS.frameUnit Φ M)⁻¹ =
      SpNS.frameUnit Φ (torD c t) := by
    refine SpNS.frameUnit_conj Φ fun x => ?_
    obtain ⟨d, w⟩ := x
    rw [hM, torD_apply, SpNS.monoEquiv_apply, SpNS.monoEquiv_apply, torD_apply]
    congr 2
    funext i
    rw [ht']
    simp only [Equiv.apply_symm_apply]
    exact (hT i).apply_pow hc (t i) _
  apply Subtype.ext
  change (SpNS.frameUnit Φ M)⁻¹ * SpNS.frameUnit Φ (torD c t) * SpNS.frameUnit Φ M =
    SpNS.frameUnit Φ (torD c t')
  rw [← hconj]
  group

end Torus

end CoordSpNs

end CFSG.StandardType
