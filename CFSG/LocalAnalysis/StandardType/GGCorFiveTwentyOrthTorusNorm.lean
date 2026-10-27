module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusBasic

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

section Fix

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem card_fix_conj (g x : V ≃ₗ[K] V) :
    Nat.card {v : V // (g * x * g⁻¹) v = v} = Nat.card {v : V // x v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv g.symm.toEquiv fun v => ?_)
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_toEquiv]
  constructor
  · intro h
    have h1 := congrArg g.symm h
    rwa [LinearEquiv.symm_apply_apply] at h1
  · intro h
    have h1 : x (g⁻¹ v) = g⁻¹ v := h
    rw [h1]
    exact LinearEquiv.apply_symm_apply g v

end Fix

section Torus

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s r p : ℕ} [NeZero p] {κ : Type} (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V)
  {cE : D ≃ₗ[K] D} (hcp : cE ^ p = 1) {a : Fin r → Fin s}

@[expose] noncomputable def coordTorus (a : Fin r → Fin s) :
    (Fin r → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V) :=
  (OmMv.coordHom Φ a hcp).comp (piMul r p).toMonoidHom

theorem coordTorus_apply (f : Fin r → Multiplicative (ZMod p)) (d : Fin s → D) (w : κ → K) :
    coordTorus Φ hcp a f (Φ (d, w)) =
      Φ (fun i => (cE ^ (OmMv.extC a (fun j => toAdd (f j)) i).val) (d i), w) :=
  OmMv.coordHom_apply Φ a hcp _ d w

theorem coordTorus_eq (f : Fin r → Multiplicative (ZMod p)) :
    coordTorus Φ hcp a f = OmMv.coordHom Φ a hcp (piMul r p f) :=
  rfl

theorem coordTorus_single (ha : Function.Injective a) (f : Fin r → Multiplicative (ZMod p))
    (j : Fin r) (y : D) :
    coordTorus Φ hcp a f (Φ (Pi.single (a j) y, 0)) =
      Φ (Pi.single (a j) ((cE ^ (toAdd (f j)).val) y), 0) :=
  OmMv.coordHom_single Φ ha hcp _ j y

variable [Fact p.Prime]

theorem coordTorus_apply_eq_self_iff (hfix : ∀ x, cE x = x → x = 0)
    (ha : Function.Injective a) (f : Fin r → Multiplicative (ZMod p)) (d : Fin s → D)
    (w : κ → K) :
    coordTorus Φ hcp a f (Φ (d, w)) = Φ (d, w) ↔ ∀ j, f j ≠ 1 → d (a j) = 0 := by
  rw [coordTorus_apply, Φ.injective.eq_iff, Prod.mk.injEq, and_iff_left rfl, funext_iff]
  constructor
  · intro h j hj
    have h1 := h (a j)
    rw [OmMv.extC_apply_self ha] at h1
    refine OmMv.pow_fix_eq_zero hcp hfix (m := toAdd (f j)) ?_ h1
    rwa [Ne, toAdd_eq_zero]
  · intro h i
    by_cases hi : ∃ j, a j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [OmMv.extC_apply_self ha]
      by_cases hj : f j = 1
      · rw [hj, toAdd_one, ZMod.val_zero, pow_zero]
        rfl
      · rw [h j hj, map_zero]
    · push Not at hi
      rw [OmMv.extC_apply_of_forall_ne _ hi, ZMod.val_zero, pow_zero]
      rfl

theorem card_fix_coordTorus [Finite D] [Finite K] [Fintype κ] (hfix : ∀ x, cE x = x → x = 0)
    (ha : Function.Injective a) (f : Fin r → Multiplicative (ZMod p)) :
    Nat.card {v : V // coordTorus Φ hcp a f v = v} =
      Nat.card D ^ (s - (Finset.univ.filter fun j => f j ≠ 1).card) * Nat.card (κ → K) := by
  classical
  set S := Finset.univ.filter fun j => f j ≠ 1 with hS
  set T : Finset (Fin s) := S.image a with hT
  have hTc : T.card = S.card := Finset.card_image_of_injective _ ha
  have hmem : ∀ x : (Fin s → D) × (κ → K), coordTorus Φ hcp a f (Φ x) = Φ x ↔
      ∀ i ∈ T, x.1 i = 0 := by
    rintro ⟨d, w⟩
    rw [coordTorus_apply_eq_self_iff Φ hcp hfix ha]
    constructor
    · intro h i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact h j (Finset.mem_filter.mp hj).2
    · intro h j hj
      exact h (a j) (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
  have e1 : {v : V // coordTorus Φ hcp a f v = v} ≃
      {x : (Fin s → D) × (κ → K) // ∀ i ∈ T, x.1 i = 0} :=
    { toFun := fun v => ⟨Φ.symm v, (hmem _).mp (by rw [LinearEquiv.apply_symm_apply]; exact v.2)⟩
      invFun := fun x => ⟨Φ x, (hmem x).mpr x.2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have e2 : {x : (Fin s → D) × (κ → K) // ∀ i ∈ T, x.1 i = 0} ≃
      ({i // i ∉ T} → D) × (κ → K) :=
    { toFun := fun x => (fun i => x.1.1 i.1, x.1.2)
      invFun := fun y => ⟨(fun i => if h : i ∈ T then 0 else y.1 ⟨i, h⟩, y.2),
        fun i hi => by simp [hi]⟩
      left_inv := fun x => by
        refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
        by_cases hi : i ∈ T
        · simp [hi, x.2 i hi]
        · simp [hi]
      right_inv := fun y => by
        refine Prod.ext (funext fun i => ?_) rfl
        simp [i.2] }
  rw [Nat.card_congr (e1.trans e2), Nat.card_prod, Nat.card_fun,
    Nat.card_eq_fintype_card (α := {i // i ∉ T}), Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_coe, hTc]

theorem coordTorus_normalizer [Finite D] [Finite K] [Fintype κ] [Nontrivial D]
    (hfix : ∀ x, cE x = x → x = 0) (hc1 : ∀ u, ∃ u₀, cE u₀ - u₀ = u) (ha : Function.Injective a)
    (hinj : Function.Injective (coordTorus Φ hcp a))
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (cE x) = (cE ^ e.val) (θ x)) → e = 1 ∨ e = -1)
    (g : V ≃ₗ[K] V) (hg : ∀ f, ∃ f', g * coordTorus Φ hcp a f * g⁻¹ = coordTorus Φ hcp a f') :
    ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * coordTorus Φ hcp a f * g⁻¹ = coordTorus Φ hcp a f' →
        ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  set τ := coordTorus Φ hcp a with hτ
  choose α hα using hg
  have hαuniq : ∀ f f', g * τ f * g⁻¹ = τ f' → f' = α f := fun f f' hf =>
    hinj (hf.symm.trans (hα f))
  have hαmul : ∀ f f', α (f * f') = α f * α f' := fun f f' => hinj (by
    rw [← hα, map_mul, map_mul, ← hα, ← hα]
    group)
  have hα1 : α 1 = 1 := (hαuniq 1 1 (by rw [map_one]; group)).symm
  let αh : (Fin r → Multiplicative (ZMod p)) →* (Fin r → Multiplicative (ZMod p)) :=
    { toFun := α, map_one' := hα1, map_mul' := hαmul }
  have hD : 1 < Nat.card D := Finite.one_lt_card
  have hκpos : 0 < Nat.card (κ → K) := Nat.card_pos
  have hrs : r ≤ s := by simpa using Fintype.card_le_of_injective a ha
  have hsupp : ∀ f, (Finset.univ.filter fun j => α f j ≠ 1).card =
      (Finset.univ.filter fun j => f j ≠ 1).card := by
    intro f
    have h1 := card_fix_conj g (τ f)
    rw [hα f, card_fix_coordTorus Φ hcp hfix ha, card_fix_coordTorus Φ hcp hfix ha] at h1
    have h2 := Nat.pow_right_injective hD (Nat.eq_of_mul_eq_mul_right hκpos h1)
    have h3 := Finset.card_le_univ (Finset.univ.filter fun j => α f j ≠ 1)
    have h4 := Finset.card_le_univ (Finset.univ.filter fun j => f j ≠ 1)
    rw [Fintype.card_fin] at h3 h4
    omega
  have hδ1 : ofAdd (1 : ZMod p) ≠ 1 := by
    rw [Ne, ofAdd_eq_one]
    exact one_ne_zero
  set δ : Fin r → Fin r → Multiplicative (ZMod p) := fun i => Pi.mulSingle i (ofAdd (1 : ZMod p))
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
  set ex : Fin r → ZMod p := fun i => toAdd (α (δ i) (π₀ i)) with hex
  have hαδ : ∀ i, α (δ i) = Pi.mulSingle (π₀ i) (ofAdd (ex i)) := by
    intro i
    funext j
    by_cases hj : j = π₀ i
    · subst hj
      simp [hex]
    · rw [Pi.mulSingle_eq_of_ne hj]
      by_contra hne
      exact hj ((hπ₀ i j).mp hne)
  have hπinj : Function.Injective π₀ := by
    intro i i' hii
    by_contra hne
    have h1 := hsupp (δ i * δ i')
    rw [SpNS.filter_ne_one_card_mulSingle_mul hne, hαmul, hαδ, hαδ, ← hii,
      ← Pi.mulSingle_mul] at h1
    have h2 : (Finset.univ.filter fun j => (Pi.mulSingle (π₀ i) (ofAdd (ex i) * ofAdd (ex i')) :
        Fin r → Multiplicative (ZMod p)) j ≠ 1) ⊆ {π₀ i} := by
      intro x hx
      rw [Finset.mem_singleton]
      by_contra hxne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx (Pi.mulSingle_eq_of_ne hxne _)
    have h3 := (Finset.card_le_card h2).trans (Finset.card_singleton _).le
    omega
  have hτδ : ∀ i (y : D), τ (δ i) (Φ (Pi.single (a i) y, 0)) = Φ (Pi.single (a i) (cE y), 0) := by
    intro i y
    rw [coordTorus_single Φ hcp ha]
    simp only [hδ, Pi.mulSingle_eq_same, toAdd_ofAdd, ZMod.val_one, pow_one]
  have hτsub : ∀ (j : Fin r) (e : ZMod p) (x : (Fin s → D) × (κ → K)),
      τ (Pi.mulSingle j (ofAdd e)) (Φ x) - Φ x =
        Φ (Pi.single (a j) ((cE ^ e.val) (x.1 (a j)) - x.1 (a j)), 0) := by
    rintro j e ⟨d, w⟩
    rw [coordTorus_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
    congr 2
    funext i
    by_cases hi : i = a j
    · subst hi
      simp only [Pi.sub_apply, Pi.single_eq_same]
      rw [OmMv.extC_apply_self ha, Pi.mulSingle_eq_same, toAdd_ofAdd]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hi]
      have h0 : OmMv.extC a (fun k => toAdd ((Pi.mulSingle j (ofAdd e) :
          Fin r → Multiplicative (ZMod p)) k)) i = 0 := by
        by_cases hi' : ∃ k, a k = i
        · obtain ⟨k, rfl⟩ := hi'
          rw [OmMv.extC_apply_self ha]
          have hkj : k ≠ j := fun h => hi (h ▸ rfl)
          rw [Pi.mulSingle_eq_of_ne hkj, toAdd_one]
        · push Not at hi'
          exact OmMv.extC_apply_of_forall_ne _ hi'
      rw [h0, ZMod.val_zero, pow_zero]
      exact sub_self _
  have hgτ : ∀ i v, g (τ (δ i) v) = τ (α (δ i)) (g v) := by
    intro i v
    have h1 : g * τ (δ i) = τ (α (δ i)) * g := by rw [← hα (δ i)]; group
    exact LinearEquiv.congr_fun h1 v
  have hblock : ∀ i (y : D), ∃ z : D,
      g (Φ (Pi.single (a i) y, 0)) = Φ (Pi.single (a (π₀ i)) z, 0) := by
    intro i y
    obtain ⟨y₀, hy₀⟩ := hc1 y
    have e1 : Φ (Pi.single (a i) y, 0) =
        τ (δ i) (Φ (Pi.single (a i) y₀, 0)) - Φ (Pi.single (a i) y₀, 0) := by
      rw [hτδ, ← map_sub, Prod.mk_sub_mk, sub_zero, ← Pi.single_sub, hy₀]
    obtain ⟨x, hx⟩ := Φ.surjective (g (Φ (Pi.single (a i) y₀, 0)))
    refine ⟨(cE ^ (ex i).val) (x.1 (a (π₀ i))) - x.1 (a (π₀ i)), ?_⟩
    rw [e1, map_sub, hgτ, ← hx, hαδ, hτsub]
  choose z hz using hblock
  set θ : Fin r → (D →ₗ[K] D) := fun i =>
    (LinearMap.proj (a (π₀ i))) ∘ₗ (LinearMap.fst K (Fin s → D) (κ → K)) ∘ₗ
      Φ.symm.toLinearMap ∘ₗ g.toLinearMap ∘ₗ Φ.toLinearMap ∘ₗ
        (LinearMap.inl K (Fin s → D) (κ → K)) ∘ₗ (LinearMap.single K (fun _ => D) (a i)) with hθ
  have hθz : ∀ i y, g (Φ (Pi.single (a i) y, 0)) = Φ (Pi.single (a (π₀ i)) (θ i y), 0) := by
    intro i y
    have e : θ i y = z i y := by
      change (Φ.symm (g (Φ (Pi.single (a i) y, 0)))).1 (a (π₀ i)) = z i y
      rw [hz, LinearEquiv.symm_apply_apply]
      simp
    rw [e, hz]
  have hθc : ∀ i y, θ i (cE y) = (cE ^ (ex i).val) (θ i y) := by
    intro i y
    have e2 := hθz i (cE y)
    rw [← hτδ, hgτ, hθz, hαδ, coordTorus_single Φ hcp ha, Pi.mulSingle_eq_same,
      toAdd_ofAdd] at e2
    have e3 := congrArg (fun x : (Fin s → D) × (κ → K) => x.1 (a (π₀ i))) (Φ.injective e2)
    simp only [Pi.single_eq_same] at e3
    exact e3.symm
  have hθinj : ∀ i, Function.Injective (θ i) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 := hθz i u
    rw [hu, Pi.single_zero, Prod.mk_zero_zero, map_zero] at h1
    have h2 : Φ (Pi.single (a i) u, 0) = 0 := g.injective (h1.trans (map_zero g).symm)
    have h3 : ((Pi.single (a i) u : Fin s → D), (0 : κ → K)) = 0 :=
      Φ.injective (h2.trans (map_zero Φ).symm)
    have h4 := congrArg (fun x : (Fin s → D) × (κ → K) => x.1 (a i)) h3
    simpa using h4
  have hex1 : ∀ i, ex i = 1 ∨ ex i = -1 := fun i => hroots (ex i) (θ i) (hθinj i) (hθc i)
  refine ⟨Equiv.ofBijective π₀ hπinj.bijective_of_finite, ex, hex1, fun f f' hff' i => ?_⟩
  have hf' : f' = α f := hαuniq f f' hff'
  subst hf'
  have hfprod : f = ∏ j, δ j ^ (toAdd (f j)).val := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle f]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hδ]
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val,
      ofAdd_toAdd]
  have hαf : α f = ∏ j, (Pi.mulSingle (π₀ j) (ofAdd (ex j))) ^ (toAdd (f j)).val := by
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

end Torus

end OrthTorus

end CFSG.StandardType

end
