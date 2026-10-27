module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusElt

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace SpNS

section Fix

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def fixSet (T : LinearMap.GeneralLinearGroup K V) : Set V :=
  {v | (T : V →ₗ[K] V) v = v}

theorem card_fixSet_conj (h T : LinearMap.GeneralLinearGroup K V) :
    Nat.card (fixSet (h * T * h⁻¹)) = Nat.card (fixSet T) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v, ?_⟩
      invFun := fun v => ⟨(h : V →ₗ[K] V) v, ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun v => Subtype.ext ?_ }
  · have hv := v.2
    change ((h * T * h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = v at hv
    change (T : V →ₗ[K] V) (((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) =
      ((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v
    have e : h⁻¹ * (h * T * h⁻¹) = T * h⁻¹ := by group
    calc (T : V →ₗ[K] V) (((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)
        = ((T * h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v := by
          rw [Units.val_mul, Module.End.mul_apply]
      _ = ((h⁻¹ * (h * T * h⁻¹) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v := by rw [e]
      _ = ((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
            (((h * T * h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) := by
          rw [Units.val_mul _ (h * T * h⁻¹), Module.End.mul_apply]
      _ = ((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v := by rw [hv]
  · have hv := v.2
    change (T : V →ₗ[K] V) v = v at hv
    change ((h * T * h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((h : V →ₗ[K] V) v) =
      (h : V →ₗ[K] V) v
    have e : h * T * h⁻¹ * h = h * T := by group
    calc ((h * T * h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((h : V →ₗ[K] V) v)
        = ((h * T * h⁻¹ * h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v := by
          rw [Units.val_mul _ h, Module.End.mul_apply]
      _ = ((h * T : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v := by rw [e]
      _ = (h : V →ₗ[K] V) v := by rw [Units.val_mul, Module.End.mul_apply, hv]
  · change ((h : V →ₗ[K] V) (((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)) = v
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  · change (((h⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((h : V →ₗ[K] V) v)) = v
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]

end Fix

section TorusFix

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {p : ℕ} [NeZero p] {ζ : L} (hζ : ζ ^ p = 1)
  {V : Type} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

include hζ in
theorem torEquiv_eq_self_iff (hζo : IsPrimitiveRoot ζ p) (f : Fin s → Multiplicative (ZMod p))
    (x : (Fin s → L) × (κ → K)) :
    torEquiv (K := K) hζ f x = x ↔ ∀ i, f i ≠ 1 → x.1 i = 0 := by
  obtain ⟨d, w⟩ := x
  rw [torEquiv_apply, Prod.mk.injEq]
  simp only [and_true]
  constructor
  · intro h i hi
    have h1 := congrFun h i
    have hv : ζ ^ (toAdd (f i)).val ≠ 1 := by
      intro h1'
      apply hi
      have h3 := (hζo.pow_eq_one_iff_dvd _).mp h1'
      rw [← ofAdd_toAdd (f i), ← ZMod.natCast_zmod_val (toAdd (f i)),
        (ZMod.natCast_eq_zero_iff _ _).mpr h3, ofAdd_zero]
    have h2 : (ζ ^ (toAdd (f i)).val - 1) * d i = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hv)
  · intro h
    funext i
    by_cases hi : f i = 1
    · rw [hi, toAdd_one, ZMod.val_zero, pow_zero, one_mul]
    · rw [h i hi, mul_zero]

theorem card_fixSet_torHom [Fintype κ]
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (hζo : IsPrimitiveRoot ζ p)
    (f : Fin s → Multiplicative (ZMod p)) :
    Nat.card (fixSet ((torHom hζ hdec hζβ f : ↥(sesqUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V)) =
      Nat.card L ^ (Finset.univ.filter fun i => f i = 1).card * Nat.card (κ → K) := by
  classical
  have hmem : ∀ x : (Fin s → L) × (κ → K), Φ x ∈ fixSet ((torHom hζ hdec hζβ f :
      ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) ↔
        ∀ i, f i ≠ 1 → x.1 i = 0 := by
    intro x
    change ((frameUnit Φ (torEquiv hζ f) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (Φ x) = Φ x ↔ _
    rw [frameUnit_apply, Φ.injective.eq_iff, torEquiv_eq_self_iff hζ hζo]
  have e1 : ↥(fixSet ((torHom hζ hdec hζβ f : ↥(sesqUnitaryGroup B)) :
      LinearMap.GeneralLinearGroup K V)) ≃
      {x : (Fin s → L) × (κ → K) // ∀ i, f i ≠ 1 → x.1 i = 0} :=
    { toFun := fun v => ⟨Φ.symm v, (hmem _).mp (by rw [LinearEquiv.apply_symm_apply]; exact v.2)⟩
      invFun := fun x => ⟨Φ x, (hmem x).mpr x.2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have e2 : {x : (Fin s → L) × (κ → K) // ∀ i, f i ≠ 1 → x.1 i = 0} ≃
      ({i // f i = 1} → L) × (κ → K) :=
    { toFun := fun x => (fun i => x.1.1 i.1, x.1.2)
      invFun := fun y => ⟨(fun i => if h : f i = 1 then y.1 ⟨i, h⟩ else 0, y.2),
        fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
        by_cases hi : f i = 1
        · simp [hi]
        · simp [hi, x.2 i hi]
      right_inv := fun y => by
        refine Prod.ext (funext fun i => ?_) rfl
        simp [i.2] }
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card
    (α := {i // f i = 1}), Fintype.card_subtype]

include hζ in
theorem torEquiv_single (f : Fin s → Multiplicative (ZMod p)) (j : Fin s) (v : L) :
    torEquiv (K := K) (κ := κ) hζ f (Pi.single j v, 0) =
      (Pi.single j (ζ ^ (toAdd (f j)).val * v), 0) := by
  rw [torEquiv_apply]
  congr 1
  funext j'
  by_cases hj : j' = j
  · subst hj
    simp
  · simp [Pi.single_eq_of_ne hj]

include hζ in
theorem torEquiv_sub_self_of_single {f : Fin s → Multiplicative (ZMod p)} {j : Fin s}
    (hf : ∀ j', j' ≠ j → f j' = 1) (x : (Fin s → L) × (κ → K)) :
    torEquiv (K := K) hζ f x - x =
      (Pi.single j ((ζ ^ (toAdd (f j)).val - 1) * x.1 j), 0) := by
  obtain ⟨d, w⟩ := x
  rw [torEquiv_apply, Prod.mk_sub_mk, sub_self]
  congr 1
  funext j'
  by_cases hj : j' = j
  · subst hj
    simp [sub_mul]
  · rw [Pi.single_eq_of_ne hj, Pi.sub_apply, hf j' hj, toAdd_one, ZMod.val_zero, pow_zero,
      one_mul, sub_self]

omit [NeZero p] in
theorem filter_ne_one_card_mulSingle_mul [Fact (1 < p)] {i i' : Fin s} (hii : i ≠ i') :
    (Finset.univ.filter fun j => ((Pi.mulSingle i (ofAdd (1 : ZMod p)) *
      Pi.mulSingle i' (ofAdd (1 : ZMod p)) : Fin s → Multiplicative (ZMod p))) j ≠ 1).card = 2 := by
  classical
  have h1 : (ofAdd (1 : ZMod p)) ≠ 1 := by
    rw [Ne, ofAdd_eq_one]
    exact one_ne_zero
  have : (Finset.univ.filter fun j => ((Pi.mulSingle i (ofAdd (1 : ZMod p)) *
      Pi.mulSingle i' (ofAdd (1 : ZMod p)) : Fin s → Multiplicative (ZMod p))) j ≠ 1) =
      {i, i'} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      simp [Pi.mulSingle_eq_of_ne hii, h1]
    · by_cases hj' : j = i'
      · subst hj'
        simp [Pi.mulSingle_eq_of_ne hj, h1]
      · simp [hj, hj']
  rw [this, Finset.card_pair hii]

theorem torHom_normalizer [Finite K] [Finite L] [Fintype κ] (hp : p.Prime)
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (hζo : IsPrimitiveRoot ζ p)
    (hroots : ∀ (a : ZMod p) (θ : L →ₗ[K] L), Function.Injective θ →
      (∀ u, θ (ζ * u) = ζ ^ a.val * θ u) → a = 1 ∨ a = -1)
    (h : ↥(sesqUnitaryGroup B))
    (hh : ∀ f, ∃ f', h * torHom hζ hdec hζβ f * h⁻¹ = torHom hζ hdec hζβ f') :
    ∃ (π : Equiv.Perm (Fin s)) (ε : Fin s → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', h * torHom hζ hdec hζβ f * h⁻¹ = torHom hζ hdec hζβ f' →
        ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  set τ := torHom hζ hdec hζβ with hτ
  have hτinj : Function.Injective τ := torHom_injective hζ hdec hζβ hζo
  choose α hα using hh
  have hαuniq : ∀ f f', h * τ f * h⁻¹ = τ f' → f' = α f := fun f f' hf =>
    hτinj (hf.symm.trans (hα f))
  have hαmul : ∀ f g, α (f * g) = α f * α g := fun f g => hτinj (by
    rw [← hα, map_mul, map_mul, ← hα, ← hα]
    group)
  have hα1 : α 1 = 1 := (hαuniq 1 1 (by rw [map_one]; group)).symm
  let αh : (Fin s → Multiplicative (ZMod p)) →* (Fin s → Multiplicative (ZMod p)) :=
    { toFun := α, map_one' := hα1, map_mul' := hαmul }
  have hL : 1 < Nat.card L := Finite.one_lt_card
  have hκpos : 0 < Nat.card (κ → K) := Nat.card_pos
  have hsupp : ∀ f, (Finset.univ.filter fun j => α f j ≠ 1).card =
      (Finset.univ.filter fun j => f j ≠ 1).card := by
    intro f
    have h1 := card_fixSet_conj ((h : LinearMap.GeneralLinearGroup K V))
      ((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V)
    have h2 : ((h : LinearMap.GeneralLinearGroup K V) *
        ((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) *
        (h : LinearMap.GeneralLinearGroup K V)⁻¹) =
        ((τ (α f) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) := by
      rw [← hα f]
      rfl
    rw [h2, card_fixSet_torHom hζ hdec hζβ hζo, card_fixSet_torHom hζ hdec hζβ hζo] at h1
    have h3 : (Finset.univ.filter fun j => α f j = 1).card =
        (Finset.univ.filter fun j => f j = 1).card :=
      Nat.pow_right_injective hL (Nat.eq_of_mul_eq_mul_right hκpos h1)
    have h4 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => α f j = 1)
    have h5 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => f j = 1)
    simp only [ne_eq]
    omega
  have hδ1 : ofAdd (1 : ZMod p) ≠ 1 := by
    rw [Ne, ofAdd_eq_one]
    exact one_ne_zero
  set δ : Fin s → Fin s → Multiplicative (ZMod p) := fun i => Pi.mulSingle i (ofAdd (1 : ZMod p))
    with hδ
  have hδsupp : ∀ i, (Finset.univ.filter fun j => δ i j ≠ 1).card = 1 := by
    intro i
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.ext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp [hδ, hδ1]
    · simp [hδ, hj]
  have hone : ∀ i, ∃ j, ∀ j', α (δ i) j' ≠ 1 ↔ j' = j := by
    intro i
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp ((hsupp (δ i)).trans (hδsupp i))
    exact ⟨j, fun j' => by simpa using Finset.ext_iff.mp hj j'⟩
  choose π₀ hπ₀ using hone
  set a : Fin s → ZMod p := fun i => toAdd (α (δ i) (π₀ i)) with ha
  have hαδ : ∀ i, α (δ i) = Pi.mulSingle (π₀ i) (ofAdd (a i)) := by
    intro i
    funext j
    by_cases hj : j = π₀ i
    · subst hj
      simp [ha]
    · rw [Pi.mulSingle_eq_of_ne hj]
      by_contra hne
      exact hj ((hπ₀ i j).mp hne)
  have hπinj : Function.Injective π₀ := by
    intro i i' hii
    by_contra hne
    have h1 := hsupp (δ i * δ i')
    rw [filter_ne_one_card_mulSingle_mul hne, hαmul, hαδ, hαδ, ← hii, ← Pi.mulSingle_mul] at h1
    have h2 : (Finset.univ.filter fun j => (Pi.mulSingle (π₀ i) (ofAdd (a i) * ofAdd (a i')) :
        Fin s → Multiplicative (ZMod p)) j ≠ 1) ⊆ {π₀ i} := by
      intro x hx
      rw [Finset.mem_singleton]
      by_contra hxne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx (Pi.mulSingle_eq_of_ne hxne _)
    have h3 := (Finset.card_le_card h2).trans (Finset.card_singleton _).le
    omega
  set H : V →ₗ[K] V := ((h : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) with hH
  have hτapp : ∀ f x, (((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) (Φ x) = Φ (torEquiv hζ f x) := fun f x => frameUnit_apply Φ _ x
  have hHτ : ∀ f v, H ((((τ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) v) = (((τ (α f) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) (H v) := by
    intro f v
    have h1 : h * τ f = τ (α f) * h := by rw [← hα f]; group
    have h2 := congrArg (fun y : ↥(sesqUnitaryGroup B) =>
      (((y : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply] at h2
    exact h2
  have hHinj : Function.Injective H := by
    intro v v' hvv
    have h1 := congrArg (((h⁻¹ : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) :
      V →ₗ[K] V) hvv
    simp only [hH, ← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, Module.End.one_apply] at h1
    exact h1
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζo.ne_one hp.one_lt)
  have hval1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have hblock : ∀ i (u : L), ∃ c : L,
      H (Φ (Pi.single i u, 0)) = Φ (Pi.single (π₀ i) c, 0) := by
    intro i u
    set u' := (ζ - 1)⁻¹ * u with hu'
    have e1 : Φ (Pi.single i u, 0) =
        (((τ (δ i) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
          (Φ (Pi.single i u', 0)) - Φ (Pi.single i u', 0) := by
      rw [hτapp, torEquiv_single, ← map_sub, Prod.mk_sub_mk, sub_zero, ← Pi.single_sub]
      congr 3
      simp only [hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
      rw [← sub_one_mul, hu', ← mul_assoc, mul_inv_cancel₀ hζ1, one_mul]
    obtain ⟨⟨d', w'⟩, hdw⟩ := Φ.surjective (H (Φ (Pi.single i u', 0)))
    have hf1 : ∀ j', j' ≠ π₀ i → α (δ i) j' = 1 := fun j' hj' => by
      rw [hαδ, Pi.mulSingle_eq_of_ne hj']
    refine ⟨(ζ ^ (toAdd (α (δ i) (π₀ i))).val - 1) * d' (π₀ i), ?_⟩
    rw [e1, map_sub, hHτ, ← hdw, hτapp, ← map_sub, torEquiv_sub_self_of_single hζ hf1]
  choose c hc using hblock
  set θ : Fin s → (L →ₗ[K] L) := fun i =>
    (LinearMap.proj (π₀ i)) ∘ₗ (LinearMap.fst K (Fin s → L) (κ → K)) ∘ₗ Φ.symm.toLinearMap ∘ₗ
      H ∘ₗ Φ.toLinearMap ∘ₗ (LinearMap.inl K (Fin s → L) (κ → K)) ∘ₗ
        (LinearMap.single K (fun _ => L) i) with hθ
  have hθc : ∀ i u, H (Φ (Pi.single i u, 0)) = Φ (Pi.single (π₀ i) (θ i u), 0) := by
    intro i u
    have e : θ i u = c i u := by
      change (Φ.symm (H (Φ (Pi.single i u, 0)))).1 (π₀ i) = c i u
      rw [hc, LinearEquiv.symm_apply_apply]
      simp
    rw [e, hc]
  have hθζ : ∀ i u, θ i (ζ * u) = ζ ^ (a i).val * θ i u := by
    intro i u
    have e1 : Φ (Pi.single i (ζ * u), 0) =
        (((τ (δ i) : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
          (Φ (Pi.single i u, 0)) := by
      rw [hτapp, torEquiv_single]
      simp only [hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, hval1, pow_one]
    have e2 := hθc i (ζ * u)
    rw [e1, hHτ, hθc, hτapp, torEquiv_single] at e2
    have e3 := congrArg (fun x : (Fin s → L) × (κ → K) => x.1 (π₀ i)) (Φ.injective e2)
    simp only [Pi.single_eq_same] at e3
    exact e3.symm
  have hθinj : ∀ i, Function.Injective (θ i) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 := hθc i u
    rw [hu, Pi.single_zero, Prod.mk_zero_zero, map_zero] at h1
    have h2 : Φ (Pi.single i u, 0) = 0 := hHinj (h1.trans (map_zero H).symm)
    have h3 : ((Pi.single i u : Fin s → L), (0 : κ → K)) = 0 :=
      Φ.injective (h2.trans (map_zero Φ).symm)
    have h4 := congrArg (fun x : (Fin s → L) × (κ → K) => x.1 i) h3
    simpa using h4
  have ha1 : ∀ i, a i = 1 ∨ a i = -1 := fun i => hroots (a i) (θ i) (hθinj i) (hθζ i)
  refine ⟨Equiv.ofBijective π₀ hπinj.bijective_of_finite, a, ha1, fun f f' hff' i => ?_⟩
  have hf' : f' = α f := hαuniq f f' hff'
  subst hf'
  have hfprod : f = ∏ j, δ j ^ (toAdd (f j)).val := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle f]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hδ]
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val,
      ofAdd_toAdd]
  have hαf : α f = ∏ j, (Pi.mulSingle (π₀ j) (ofAdd (a j))) ^ (toAdd (f j)).val := by
    have e : α f = αh f := rfl
    rw [e]
    conv_lhs => rw [hfprod]
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow]
    congr 1
    exact hαδ j
  rw [Equiv.ofBijective_apply, hαf, Finset.prod_apply, Finset.prod_eq_single i]
  · rw [Pi.pow_apply, Pi.mulSingle_eq_same, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
      ZMod.natCast_zmod_val, mul_comm]
  · intro j _ hji
    rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne (fun h' => hji (hπinj h').symm), one_pow]
  · intro h'
    exact absurd (Finset.mem_univ i) h'

end TorusFix

end SpNS

end CFSG.StandardType
