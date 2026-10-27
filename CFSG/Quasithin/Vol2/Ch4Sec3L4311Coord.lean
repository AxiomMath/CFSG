module

public import CFSG.Quasithin.Background.FFC9B
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.Ch4.L4311

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

section FieldMap

variable {F F₀ : Type} [Field F] [Field F₀]

@[expose] noncomputable def slMap (ε : F₀ ≃+* F) : ↥(StatedSL 3 F₀) →* ↥(StatedSL 3 F) :=
  (specialLinearGroupEquivStatedSL 3 F).toMonoidHom.comp
    ((SpecialLinearGroup.map (ε : F₀ →+* F)).comp
      (specialLinearGroupEquivStatedSL 3 F₀).symm.toMonoidHom)

theorem coe_slMap (ε : F₀ ≃+* F) (s : ↥(StatedSL 3 F₀)) :
    ((slMap ε s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((s : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀).map ε := by
  have h := specialLinearGroupEquivStatedSL_coe 3 F₀
    ((specialLinearGroupEquivStatedSL 3 F₀).symm s)
  rw [MulEquiv.apply_symm_apply] at h
  rw [slMap, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    specialLinearGroupEquivStatedSL_coe, SpecialLinearGroup.map_apply_coe, h]
  rfl

theorem slMap_surjective (ε : F₀ ≃+* F) : Function.Surjective (slMap ε) := by
  intro s
  refine ⟨slMap ε.symm s, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_slMap, coe_slMap, Matrix.map_map]
  have : (ε ∘ ε.symm : F → F) = id := by
    funext x
    exact ε.apply_symm_apply x
  rw [this, Matrix.map_id]

end FieldMap

section Natural

variable {G : Type} [Group G] {K U : Subgroup G}

theorem exists_subspace_of_natural {F F₀ : Type} [Field F] [Fintype F] [Field F₀] [Fintype F₀]
    (hcard : Fintype.card F₀ = Fintype.card F) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    {β : ↥U →* Multiplicative (Fin 3 → F)} (hβ : Function.Bijective β)
    (hβa : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β u))
    {α₀ : ↥K →* ↥(StatedSL 3 F₀)} (hα₀ : Function.Surjective α₀)
    {β₀ : ↥U →* Multiplicative (Fin 3 → F₀)} (hβ₀ : Function.Bijective β₀)
    (hβ₀a : ∀ (k : ↥K) (u v : ↥U), (v : G) = k * u * k⁻¹ →
      Multiplicative.toAdd (β₀ v) =
        ((α₀ k : GL (Fin 3) F₀) : Matrix (Fin 3) (Fin 3) F₀) *ᵥ Multiplicative.toAdd (β₀ u))
    (W₀ : Submodule F₀ (Fin 3 → F₀)) :
    ∃ W₁ : Submodule F (Fin 3 → F), Module.finrank F W₁ = Module.finrank F₀ W₀ ∧
      ∀ u : ↥U, Multiplicative.toAdd (β₀ u) ∈ W₀ ↔ Multiplicative.toAdd (β u) ∈ W₁ := by
  classical
  let ε : F₀ ≃+* F := FiniteField.ringEquivOfCardEq hcard
  let eβ : ↥U ≃* Multiplicative (Fin 3 → F) := MulEquiv.ofBijective β hβ
  let eβ₀ : ↥U ≃* Multiplicative (Fin 3 → F₀) := MulEquiv.ofBijective β₀ hβ₀
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun v i =>
    ε (Multiplicative.toAdd (eβ₀ (eβ.symm (Multiplicative.ofAdd v))) i)
  let ψ : (Fin 3 → F) → (Fin 3 → F) := fun w =>
    Multiplicative.toAdd (eβ (eβ₀.symm (Multiplicative.ofAdd (fun i => ε.symm (w i)))))
  have hφψ : ∀ w, φ (ψ w) = w := by
    intro w
    funext i
    simp [φ, ψ]
  have hψφ : ∀ v, ψ (φ v) = v := by
    intro v
    simp [φ, ψ]
  let fe : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      map_add' := by
        intro v w
        funext i
        simp only [φ, Pi.add_apply]
        rw [show Multiplicative.ofAdd (v + w) = Multiplicative.ofAdd v * Multiplicative.ofAdd w
          from rfl, map_mul, map_mul, toAdd_mul, Pi.add_apply, map_add] }
  have hfe : ∀ v, fe v = φ v := fun _ => rfl
  have hfeβ : ∀ u : ↥U, fe (Multiplicative.toAdd (β u)) =
      fun i => ε (Multiplicative.toAdd (β₀ u) i) := by
    intro u
    rw [hfe]
    funext i
    simp only [φ]
    have : eβ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (β u))) = u := by
      rw [ofAdd_toAdd]
      exact eβ.symm_apply_apply u
    rw [this]
    rfl
  have hrel : ∀ k : ↥K, FFC.SumNat.RelPair fe (α k) (slMap ε (α₀ k)) := by
    intro k x
    obtain ⟨u, hu⟩ := hβ.2 (Multiplicative.ofAdd x)
    have hux : Multiplicative.toAdd (β u) = x := by rw [hu, toAdd_ofAdd]
    let w : ↥U := ⟨k * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩
    have h1 := hβa k u w rfl
    have h2 := hβ₀a k u w rfl
    rw [hux] at h1
    rw [← h1, hfeβ, h2, coe_slMap, ← hux, hfeβ]
    funext i
    exact RingHom.map_mulVec (ε : F₀ →+* F) _ _ i
  obtain ⟨σ, hσ⟩ := FFC.SumNat.exists_semilinear_of_rel fe
    (fun s => by
      obtain ⟨k, rfl⟩ := hα s
      exact ⟨_, hrel k⟩)
    (fun s' => by
      obtain ⟨s₀, rfl⟩ := slMap_surjective ε s'
      obtain ⟨k, rfl⟩ := hα₀ s₀
      exact ⟨_, hrel k⟩)
  let W₁ : Submodule F (Fin 3 → F) :=
    { carrier := {v | (fun i => ε.symm (fe v i)) ∈ W₀}
      add_mem' := by
        intro v w hv hw
        simp only [Set.mem_ofPred_eq, map_add, Pi.add_apply] at hv hw ⊢
        have : (fun i => ε.symm (fe v i) + ε.symm (fe w i)) =
            (fun i => ε.symm (fe v i)) + (fun i => ε.symm (fe w i)) := rfl
        rw [this]
        exact W₀.add_mem hv hw
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, Pi.zero_apply]
        exact W₀.zero_mem
      smul_mem' := by
        intro c v hv
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [hσ]
        have : (fun i => ε.symm ((σ c • fe v) i)) = ε.symm (σ c) • (fun i => ε.symm (fe v i)) := by
          funext i
          simp
        rw [this]
        exact W₀.smul_mem _ hv }
  have hW₁ : ∀ v, v ∈ W₁ ↔ (fun i => ε.symm (fe v i)) ∈ W₀ := fun _ => Iff.rfl
  refine ⟨W₁, ?_, fun u => ?_⟩
  ·
    have hbij : Nat.card ↥W₁ = Nat.card ↥W₀ := by
      refine Nat.card_congr
        { toFun := fun v => ⟨fun i => ε.symm (fe v i), v.2⟩
          invFun := fun w => ⟨fe.symm (fun i => ε ((w : Fin 3 → F₀) i)), by
            rw [hW₁]
            simp only [AddEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
            exact w.2⟩
          left_inv := fun v => by
            apply Subtype.ext
            show fe.symm (fun i => ε (ε.symm (fe (v : Fin 3 → F) i))) = v
            simp only [RingEquiv.apply_symm_apply]
            exact fe.symm_apply_apply _
          right_inv := fun w => by
            apply Subtype.ext
            show (fun i => ε.symm (fe (fe.symm (fun i => ε ((w : Fin 3 → F₀) i))) i)) = w
            simp only [AddEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] }
    have h1 : Nat.card ↥W₁ = Nat.card F ^ Module.finrank F ↥W₁ := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    have h2 : Nat.card ↥W₀ = Nat.card F₀ ^ Module.finrank F₀ ↥W₀ := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    have hF : Nat.card F₀ = Nat.card F := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard]
    rw [hbij, h2, hF] at h1
    exact Nat.pow_right_injective (Finite.one_lt_card (α := F)) h1.symm
  · rw [hW₁, hfeβ]
    simp

end Natural

section Conj

variable {G : Type} [Group G]

theorem moduleAct_mul {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] (dual : Bool)
    (g h : Matrix.GeneralLinearGroup ι F) :
    moduleAct dual (g * h) = moduleAct dual g * moduleAct dual h := by
  cases dual
  · simp [moduleAct]
  · simp [moduleAct, _root_.mul_inv_rev, Matrix.transpose_mul]

theorem moduleAct_one {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] (dual : Bool) :
    moduleAct dual (1 : Matrix.GeneralLinearGroup ι F) = 1 := by
  cases dual <;> simp [moduleAct]

theorem isSumOfNaturalModulesVia_conj {A V Z : Subgroup G} {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia A V Z α dual k)
    (g : ↥Γ) :
    IsSumOfNaturalModulesVia A V Z ((MulAut.conj g).toMonoidHom.comp α) dual k := by
  obtain ⟨hAV, hZV, β, hβs, hβk, hβa⟩ := h
  set Mg := moduleAct dual (g : Matrix.GeneralLinearGroup ι F) with hMg
  set Mg' := moduleAct dual ((g⁻¹ : ↥Γ) : Matrix.GeneralLinearGroup ι F) with hMg'
  have hMM : Mg' * Mg = 1 := by
    rw [hMg, hMg', ← moduleAct_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      moduleAct_one]
  have hMM' : Mg * Mg' = 1 := by
    rw [hMg, hMg', ← moduleAct_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      moduleAct_one]
  let τ : Multiplicative (Fin k → ι → F) →* Multiplicative (Fin k → ι → F) :=
    { toFun := fun x => Multiplicative.ofAdd (fun i => Mg *ᵥ (Multiplicative.toAdd x i))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        simp
      map_mul' := by
        intro x y
        apply Multiplicative.toAdd.injective
        funext i
        simp [Matrix.mulVec_add] }
  have hτinj : Function.Injective τ := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    funext i
    have h1 := congrFun (congrArg Multiplicative.toAdd hxy) i
    simp only [τ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h1
    have h2 := congrArg (fun v => Mg' *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec] at h2
    exact h2
  have hτsurj : Function.Surjective τ := by
    intro y
    refine ⟨Multiplicative.ofAdd (fun i => Mg' *ᵥ (Multiplicative.toAdd y i)), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    simp [τ, Matrix.mulVec_mulVec, hMM']
  refine ⟨hAV, hZV, τ.comp β, hτsurj.comp hβs, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ hτinj, hβk]
  · intro a u v huv i
    have hinv : moduleAct dual ((g : Matrix.GeneralLinearGroup ι F))⁻¹ * Mg = 1 := by
      rw [hMg, ← moduleAct_mul, inv_mul_cancel, moduleAct_one]
    simp only [MonoidHom.comp_apply, τ, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hβa a u v huv i, moduleAct_mul, moduleAct_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ _ Mg, hinv, Matrix.mul_one]

end Conj

end CFSG.Quasithin.H13.Ch4.L4311
