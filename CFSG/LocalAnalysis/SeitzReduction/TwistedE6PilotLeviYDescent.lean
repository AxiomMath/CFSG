module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYTwist
public import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer mem_semilinCentralizer
  descentField mem_descentField fixSpace mem_fixSpace descentForm coe_descentForm)

section IndexTwo

variable {A B : Type*} [Group A] [Group B]

theorem map_eq_of_index_two (e : A ≃* B) {X : Subgroup A} {E : Subgroup B}
    (hE : E = commutator B) (hidx : E.index = 2) (hX : commutator A ≤ X) {r : A} (hr : r ∉ X)
    (her : e r ∉ E) : X.map e.toMonoidHom = E := by
  have hcomm : (commutator A).map e.toMonoidHom = commutator B := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hpre : ∀ a : A, e a ∈ E → a ∈ X := by
    intro a ha
    rw [hE, ← hcomm] at ha
    obtain ⟨a', ha', he⟩ := ha
    rw [MulEquiv.coe_toMonoidHom] at he
    exact e.injective he ▸ hX ha'
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hex
    have hmul : e x * e r ∈ E := (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false hex her)
    rw [← map_mul] at hmul
    have hxr := hpre _ hmul
    exact hr (by simpa using X.mul_mem (X.inv_mem hx) hxr)
  · intro b hb
    exact ⟨e.symm b, hpre _ (by rwa [MulEquiv.apply_symm_apply]), e.apply_symm_apply b⟩

end IndexTwo

section MinusForm

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem add_self_mem_descentField (hσσ : ∀ c, σ (σ c) = c) (ω : K) :
    ω + σ ω ∈ descentField σ := by
  rw [mem_descentField, map_add, hσσ, add_comm]

theorem mul_self_mem_descentField (hσσ : ∀ c, σ (σ c) = c) (ω : K) :
    ω * σ ω ∈ descentField σ := by
  rw [mem_descentField, map_mul, hσσ, mul_comm]

@[expose] noncomputable def d4MinusB (hσσ : ∀ c, σ (σ c) = c) (ω : K) : descentField σ :=
  ⟨ω + σ ω, add_self_mem_descentField hσσ ω⟩

@[expose] noncomputable def d4MinusC (hσσ : ∀ c, σ (σ c) = c) (ω : K) : descentField σ :=
  ⟨ω * σ ω, mul_self_mem_descentField hσσ ω⟩

theorem d4Minus_irr [CharP K 2] (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    ∀ s : descentField σ, s ^ 2 + d4MinusB hσσ ω * s + d4MinusC hσσ ω ≠ 0 := by
  intro s h
  have hs : σ (s : K) = s := mem_descentField.1 s.2
  have h' : ((s : K) + ω) * ((s : K) + σ ω) = 0 := by
    have h1 := congrArg (fun x : descentField σ => (x : K)) h
    simp only [d4MinusB, d4MinusC, Subfield.coe_add, Subfield.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero] at h1
    linear_combination h1
  rcases mul_eq_zero.1 h' with h1 | h1
  · have hωs : ω = s := by
      have := eq_neg_of_add_eq_zero_right h1
      rwa [CharTwo.neg_eq] at this
    exact hω (by rw [hωs, hs])
  · have hωs : σ ω = s := by
      have := eq_neg_of_add_eq_zero_right h1
      rwa [CharTwo.neg_eq] at this
    apply hω
    have h2 := congrArg σ hωs
    rw [hσσ, hs] at h2
    rw [hωs, h2]

@[expose] noncomputable def d4IotaFun (σ : K ≃+* K) (ω : K)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) : Fin 4 ⊕ Fin 4 → K
  | .inl i => if h : (i : ℕ) < 4 - 1 then (v (.inl ⟨i, h⟩) : K)
      else (v (.inr (.inr 0)) : K) + (v (.inr (.inr 1)) : K) * ω
  | .inr i => if h : (i : ℕ) < 4 - 1 then (v (.inr (.inl ⟨i, h⟩)) : K)
      else (v (.inr (.inr 0)) : K) + (v (.inr (.inr 1)) : K) * σ ω

@[expose] noncomputable def d4Iota (σ : K ≃+* K) (ω : K) :
    (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →ₗ[descentField σ]
      (Fin 4 ⊕ Fin 4 → K) where
  toFun := d4IotaFun σ ω
  map_add' v w := by
    funext s
    rcases s with i | i <;> simp only [d4IotaFun, Pi.add_apply, Subfield.coe_add] <;>
      split_ifs <;> ring
  map_smul' a v := by
    funext s
    rcases s with i | i <;>
      simp only [d4IotaFun, Pi.smul_apply, smul_eq_mul, Subfield.coe_mul, RingHom.id_apply,
        Subfield.smul_def] <;> split_ifs <;> ring

theorem d4Iota_apply (σ : K ≃+* K) (ω : K) (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    d4Iota σ ω v = d4IotaFun σ ω v :=
  rfl

end MinusForm

section Iota

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem swap43_inl_of_lt {i : Fin 4} (h : (i : ℕ) < 4 - 1) :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inl i) = Sum.inl i :=
  Equiv.swap_apply_of_ne_of_ne (fun h' => by cases h'; simp at h)
    (fun h' => by cases h')

theorem swap43_inr_of_lt {i : Fin 4} (h : (i : ℕ) < 4 - 1) :
    Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inr i) = Sum.inr i :=
  Equiv.swap_apply_of_ne_of_ne (fun h' => by cases h') (fun h' => by cases h'; simp at h)

theorem eq_three_of_not_lt {i : Fin 4} (h : ¬ (i : ℕ) < 4 - 1) : i = 3 := by
  apply Fin.ext
  have := i.2
  change (i : ℕ) = 3
  omega

theorem d4Iota_mem_fixSpace (hσσ : ∀ c, σ (σ c) = c) (ω : K)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    d4Iota σ ω v ∈ fixSpace (d4Tau σ) := by
  rw [mem_fixSpace]
  funext s
  rw [d4Tau_apply, d4Iota_apply]
  rcases s with i | i
  · by_cases h : (i : ℕ) < 4 - 1
    · rw [swap43_inl_of_lt h]
      simp only [d4IotaFun, h, dite_true]
      exact mem_descentField.1 (v _).2
    · obtain rfl := eq_three_of_not_lt h
      rw [Equiv.swap_apply_left]
      simp only [d4IotaFun]
      rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h), map_add, map_mul, hσσ, mem_descentField.1 (v _).2,
        mem_descentField.1 (v _).2]
  · by_cases h : (i : ℕ) < 4 - 1
    · rw [swap43_inr_of_lt h]
      simp only [d4IotaFun, h, dite_true]
      exact mem_descentField.1 (v _).2
    · obtain rfl := eq_three_of_not_lt h
      rw [Equiv.swap_apply_right]
      simp only [d4IotaFun]
      rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h), map_add, map_mul, mem_descentField.1 (v _).2,
        mem_descentField.1 (v _).2]

theorem eq_zero_of_add_mul_eq_zero {ω : K} (hω : σ ω ≠ ω)
    {u v : descentField σ} (h : (u : K) + (v : K) * ω = 0) : u = 0 ∧ v = 0 := by
  have hu : σ (u : K) = u := mem_descentField.1 u.2
  have hv : σ (v : K) = v := mem_descentField.1 v.2
  have h2 : (u : K) + (v : K) * σ ω = 0 := by
    have := congrArg σ h
    rwa [map_add, map_mul, hu, hv, map_zero] at this
  have h3 : (v : K) * (ω - σ ω) = 0 := by linear_combination h - h2
  have hv0 : (v : K) = 0 := (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 (Ne.symm hω))
  have hu0 : (u : K) = 0 := by rw [hv0, zero_mul, add_zero] at h; exact h
  exact ⟨Subtype.ext hu0, Subtype.ext hv0⟩

theorem d4Iota_injective {ω : K} (hω : σ ω ≠ ω) :
    Function.Injective (d4Iota σ ω) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hcoord : ∀ s, d4IotaFun σ ω v s = 0 := fun s => congrFun hv s
  have huv := eq_zero_of_add_mul_eq_zero hω (u := v (.inr (.inr 0))) (v := v (.inr (.inr 1)))
    (by have := hcoord (.inl 3); simpa [d4IotaFun] using this)
  funext s
  rcases s with i | i | j
  · have := hcoord (.inl i.castSucc)
    simp only [d4IotaFun, Fin.val_castSucc, i.2, dite_true] at this
    exact Subtype.ext this
  · have := hcoord (.inr i.castSucc)
    simp only [d4IotaFun, Fin.val_castSucc, i.2, dite_true] at this
    exact Subtype.ext this
  · fin_cases j
    · exact huv.1
    · exact huv.2

end Iota

section IotaEquiv

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem finrank_fixSpace_d4Tau (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    Module.finrank (descentField σ) (fixSpace (d4Tau σ)) = 8 := by
  rw [CFSG.ComponentClassification.UnbalancedCatalog.finrank_fixSpace hσσ (d4Tau_d4Tau hσσ) hω,
    Module.finrank_fintype_fun_eq_card]
  rfl

@[expose] noncomputable def d4IotaW (hσσ : ∀ c, σ (σ c) = c) (ω : K) :
    (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →ₗ[descentField σ]
      fixSpace (d4Tau σ) :=
  (d4Iota σ ω).codRestrict (fixSpace (d4Tau σ)) (d4Iota_mem_fixSpace hσσ ω)

theorem d4IotaW_bijective (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    Function.Bijective (d4IotaW hσσ ω) := by
  have : Module.Finite (descentField σ) (fixSpace (d4Tau σ)) :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_fixSpace
  have hinj : Function.Injective (d4IotaW hσσ ω) := fun v w h =>
    d4Iota_injective hω (congrArg Subtype.val h)
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_fixSpace_d4Tau hσσ hω, Module.finrank_fintype_fun_eq_card]
  rfl

@[expose] noncomputable def d4IotaEquiv (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ]
      fixSpace (d4Tau σ) :=
  LinearEquiv.ofBijective (d4IotaW hσσ ω) (d4IotaW_bijective hσσ hω)

theorem coe_d4IotaEquiv (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    ((d4IotaEquiv hσσ hω v : fixSpace (d4Tau σ)) : Fin 4 ⊕ Fin 4 → K) = d4Iota σ ω v :=
  rfl

omit [Finite K] in
theorem quadPlus_d4Iota (hσσ : ∀ c, σ (σ c) = c) (ω : K)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    quadPlus 4 K (d4Iota σ ω v) =
      (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) v : K) := by
  rw [quadPlus_apply, quadMinus_apply, d4Iota_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, d4IotaFun]
  push_cast
  simp [d4MinusB, d4MinusC]
  ring

variable [CharP K 2]

@[expose] noncomputable def d4IotaIsometry (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)).IsometryEquiv
      (descentForm (quadPlus_d4Tau σ)) where
  toLinearEquiv := d4IotaEquiv hσσ hω
  map_app' v := Subtype.ext (by
    rw [coe_descentForm]
    exact quadPlus_d4Iota hσσ ω v)

end IotaEquiv

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

omit [Finite K] [CharP K 2] in
theorem d4_sigma_mul_self (hσσ : ∀ c, σ (σ c) = c) : σ * σ = 1 :=
  RingEquiv.ext hσσ

omit [Finite K] [CharP K 2] in
theorem d4_sigma_ne_one {ω : K} (hω : σ ω ≠ ω) : σ ≠ 1 := fun h => hω (by rw [h]; rfl)

theorem d4_mem_commutator_subtype_iff {G : Type*} [Group G] {H : Subgroup G} {g : H} :
    g ∈ commutator H ↔ (g : G) ∈ ⁅H, H⁆ := by
  have h : H.subtype g ∈ (commutator H).map H.subtype ↔ g ∈ commutator H :=
    Subgroup.mem_map_iff_mem H.subtype_injective
  rw [Subgroup.map_subtype_commutator] at h
  exact h.symm

omit [CharP K 2] in
theorem d4_descent_exists (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    ∃ e : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) ≃*
        ↥(TauCeti.QuadraticMap.orthogonalGroup (descentForm (quadPlus_d4Tau σ))),
      ∀ g w, (((e g : fixSpace (d4Tau σ) ≃ₗ[descentField σ] fixSpace (d4Tau σ)) w :
        fixSpace (d4Tau σ)) : Fin 4 ⊕ Fin 4 → K) = (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) w :=
  (CFSG.ComponentClassification.UnbalancedCatalog.even_quadratic_semilinear_involution_descent
    (d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω) (nondegenerate_polarBilin_quadPlus 4 K)
    (d4Tau_d4Tau hσσ) (quadPlus_d4Tau σ)).2.2.2.2.2.2.2

@[expose] noncomputable def d4DescentEquiv (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) :=
  (d4_descent_exists hσσ hω).choose.trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr (d4IotaIsometry hσσ hω).symm)

omit [CharP K 2] in
theorem d4Iota_d4DescentEquiv (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)))
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    d4Iota σ ω ((d4DescentEquiv hσσ hω g : _ ≃ₗ[descentField σ] _) v) =
      (g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) (d4Iota σ ω v) := by
  rw [d4DescentEquiv, MulEquiv.trans_apply, TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
  have h1 := (d4_descent_exists hσσ hω).choose_spec g (d4IotaEquiv hσσ hω v)
  rw [← coe_d4IotaEquiv hσσ hω, ← coe_d4IotaEquiv hσσ hω]
  change (((d4IotaEquiv hσσ hω) ((d4IotaEquiv hσσ hω).symm
    (((d4_descent_exists hσσ hω).choose g : fixSpace (d4Tau σ) ≃ₗ[descentField σ] _)
      ((d4IotaEquiv hσσ hω) v))) : fixSpace (d4Tau σ)) : Fin 4 ⊕ Fin 4 → K) = _
  rw [LinearEquiv.apply_symm_apply]
  exact h1

omit [CharP K 2] in
theorem d4Iota_d4DescentEquiv_inj (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
    {g : ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)))}
    {x : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ))}
    (h : ∀ v, d4Iota σ ω ((g : _ ≃ₗ[descentField σ] _) v) =
      (x : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) (d4Iota σ ω v)) :
    d4DescentEquiv hσσ hω x = g := by
  refine Subtype.ext (LinearEquiv.ext fun v => d4Iota_injective hω ?_)
  rw [d4Iota_d4DescentEquiv, h]

end Descent

section Elementary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

omit [Finite K] [CharP K 2] in
theorem polar_quadPlus_d4Iota (hσσ : ∀ c, σ (σ c) = c) (ω : K)
    (a b : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) :
    polar (quadPlus 4 K) (d4Iota σ ω a) (d4Iota σ ω b) =
      ((polar (⇑(quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) a b :
        descentField σ) : K) := by
  rw [polar, polar, ← map_add, quadPlus_d4Iota hσσ, quadPlus_d4Iota hσσ, quadPlus_d4Iota hσσ]
  push_cast
  ring

omit [Finite K] [CharP K 2] in
theorem reflect_mem_semilinCentralizer {w : Fin 4 ⊕ Fin 4 → K} (hw : d4Tau σ w = w) :
    reflect (quadPlus 4 K) w ∈ semilinCentralizer (d4Tau σ) := by
  rw [mem_semilinCentralizer]
  intro x
  by_cases hQ : quadPlus 4 K w = 0
  · rw [reflect_of_map_eq_zero hQ]
    rfl
  · have hQ' : quadPlus 4 K w = σ (quadPlus 4 K w) := by
      conv_lhs => rw [← hw]
      exact quadPlus_d4Tau σ w
    have hB : polar (quadPlus 4 K) w (d4Tau σ x) = σ (polar (quadPlus 4 K) w x) := by
      conv_lhs => rw [← hw]
      exact CFSG.ComponentClassification.UnbalancedCatalog.polar_semilinear (quadPlus_d4Tau σ) w x
    rw [reflect_apply hQ, reflect_apply hQ, map_sub, LinearMap.map_smulₛₗ, hw, hB,
      RingEquiv.coe_toRingHom, map_div₀, ← hQ']

variable (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
include hσσ hω

theorem elementary_subgroupOf_eq_commutator :
    (elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup
          (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) := by
  ext x
  rw [Subgroup.mem_subgroupOf, d4_mem_commutator_subtype_iff,
    commutator_orthogonalGroup_quadMinus (by norm_num) (d4Minus_irr hσσ hω)]

theorem index_elementary_subgroupOf :
    ((elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup
        (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)))).index = 2 := by
  set b := d4MinusB hσσ ω
  set c := d4MinusC hσσ ω
  have hirr := d4Minus_irr hσσ hω
  have hn0 : 0 < 4 - 1 := by norm_num
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 4 (descentField σ) hirr
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
    (minusPair_orth (K := descentField σ) (b := b) (c := c) (i := ⟨0, by norm_num⟩)
      (j := ⟨1, by norm_num⟩) (by simp))
    (regular_quadMinus (by norm_num) hirr).2
    (orthogonalGroup_le_closure_of_two_eq_zero (minusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx hQ => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hx hQ)
      (fun x hx hx0 y hy hxy => exists_eq_smul_of_mem_tailSpace_minusFamily
        CharTwo.two_eq_zero hirr hn0 hx hx0 hy hxy) (by norm_num))
  have hEO := elementaryGroup_le_orthogonalGroup (quadMinus 4 (descentField σ) b c)
  have hmul := ((elementaryGroup (quadMinus 4 (descentField σ) b c)).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (descentField σ) b c))).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEO).toEquiv, hcard] at hmul
  have : Finite ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ)) :=
    Finite.of_injective (fun g => (g : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) →
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ))) (fun a b h => LinearEquiv.ext
        (congrFun h))
  have hpos : 0 < Nat.card (elementaryGroup (quadMinus 4 (descentField σ) b c)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

end Elementary

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

@[expose] noncomputable def d4V0 (σ : K ≃+* K) (b c : descentField σ) :
    Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ :=
  (minusPair (descentField σ) b c (n := 4) ⟨0, by norm_num⟩).e +
    (minusPair (descentField σ) b c (n := 4) ⟨0, by norm_num⟩).f

omit [Finite K] [CharP K 2] in
theorem quadMinus_d4V0 (b c : descentField σ) : quadMinus 4 (descentField σ) b c (d4V0 σ b c) = 1 :=
  CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair _

variable (hσσ : ∀ c, σ (σ c) = c) {ω : K} (hω : σ ω ≠ ω)
include hσσ hω

theorem map_d4DescentEquiv_elementary :
    ((orthElementaryGroup (quadPlus 4 K)).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ))).map
        (d4DescentEquiv hσσ hω).toMonoidHom =
      (elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup
          (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω))) := by
  set b := d4MinusB hσσ ω
  set c := d4MinusC hσσ ω
  set Qm := quadMinus 4 (descentField σ) b c
  set v₀ := d4V0 σ b c
  set w₀ := d4Iota σ ω v₀
  have hQv₀ : Qm v₀ = 1 := quadMinus_d4V0 b c
  have hQw₀ : quadPlus 4 K w₀ = 1 := by
    rw [quadPlus_d4Iota hσσ, hQv₀]
    rfl
  have hw₀ : d4Tau σ w₀ = w₀ := mem_fixSpace.1 (d4Iota_mem_fixSpace hσσ ω v₀)
  set r : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)) :=
    ⟨reflect (quadPlus 4 K) w₀, reflect_mem_orthogonalGroup _ _,
      reflect_mem_semilinCentralizer hw₀⟩ with hr
  have her : d4DescentEquiv hσσ hω r = ⟨reflect Qm v₀, reflect_mem_orthogonalGroup _ _⟩ := by
    apply d4Iota_d4DescentEquiv_inj
    intro v
    change d4Iota σ ω (reflect Qm v₀ v) = reflect (quadPlus 4 K) w₀ (d4Iota σ ω v)
    rw [reflect_apply (by rw [hQv₀]; exact one_ne_zero), reflect_apply
      (by rw [hQw₀]; exact one_ne_zero), map_sub, LinearMap.map_smul_of_tower, hQw₀, hQv₀,
      div_one, div_one, polar_quadPlus_d4Iota hσσ]
    rfl
  refine map_eq_of_index_two (d4DescentEquiv hσσ hω) (r := r)
    (elementary_subgroupOf_eq_commutator hσσ hω) (index_elementary_subgroupOf hσσ hω) ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have h1 := d4_mem_commutator_subtype_iff.1 hx
    have h2 : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) ⊓ semilinCentralizer (d4Tau σ)⁆ ≤
        ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
          TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ :=
      Subgroup.commutator_mono inf_le_left inf_le_left
    rw [commutator_orthogonalGroup_quadPlus (by norm_num)] at h2
    exact h2 h1
  · rw [Subgroup.mem_subgroupOf]
    obtain ⟨-, -, -, hsep⟩ := OrthogonalTail.orthogonal_geometry_char_two_reflection_separation
      (regular_quadPlus (n := 4) (K := K) (by norm_num)).1
      (regular_quadPlus (n := 4) (K := K) (by norm_num)).2
    exact hsep w₀ (by rw [hQw₀]; exact one_ne_zero)
  · rw [her, Subgroup.mem_subgroupOf]
    obtain ⟨-, -, -, hsep⟩ := OrthogonalTail.orthogonal_geometry_char_two_reflection_separation
      (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).1
      (regular_quadMinus (n := 4) (K := descentField σ) (by norm_num) (d4Minus_irr hσσ hω)).2
    exact hsep v₀ (by rw [hQv₀]; exact one_ne_zero)

end Main

end CFSG.SeitzReduction.TwistedE6Pilot
