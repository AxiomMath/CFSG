module

public import CFSG.Quasithin.Background.F2Amalgam
public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.Quasithin

universe u v w w'

namespace Amalgam

variable {D : Type u} [Preorder D] {α : Amalgam.{u, v} D}

namespace Completion

variable {G : Type w} {H : Type w'} [Group G] [Group H]

@[ext] theorem ext {μ η : Completion α G} (h : ∀ d (x : α.X d), μ.toHom d x = η.toHom d x) :
    μ = η := by
  cases μ with | mk μ _ _ =>
  cases η with | mk η _ _ =>
  have : μ = η := funext fun d => MonoidHom.ext (h d)
  subst this
  rfl

noncomputable def hat (μ : Completion α G) : gp α →* G := lift μ.toHom μ.comm

@[simp] theorem hat_ξ (μ : Completion α G) (d : D) (x : α.X d) :
    μ.hat (ξ α d x) = μ.toHom d x := lift_ξ _ _ d x

theorem hat_surjective (μ : Completion α G) : Function.Surjective μ.hat := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← μ.gen]
  refine iSup_le fun d => ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨ξ α d x, hat_ξ μ d x⟩

theorem hat_unique (μ : Completion α G) (ψ : gp α →* G)
    (hψ : ∀ d (x : α.X d), ψ (ξ α d x) = μ.toHom d x) : ψ = μ.hat :=
  lift_unique _ _ ψ hψ

@[simp] theorem hat_univ : (univ α).hat = MonoidHom.id (gp α) :=
  (hat_unique _ _ fun _ _ => rfl).symm

@[expose] def IsEquivalent (μ : Completion α G) (η : Completion α H) : Prop :=
  ∃ φ : G ≃* H, ∀ d (x : α.X d), φ (μ.toHom d x) = η.toHom d x

theorem IsEquivalent.refl (μ : Completion α G) : IsEquivalent μ μ := ⟨MulEquiv.refl G, fun _ _ => rfl⟩

theorem IsEquivalent.symm {μ : Completion α G} {η : Completion α H} (h : IsEquivalent μ η) :
    IsEquivalent η μ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.symm, fun d x => by rw [← hφ d x]; simp⟩

theorem IsEquivalent.trans {K : Type*} [Group K] {μ : Completion α G} {η : Completion α H}
    {ζ : Completion α K} (h₁ : IsEquivalent μ η) (h₂ : IsEquivalent η ζ) : IsEquivalent μ ζ := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨φ.trans ψ, fun d x => by simp [hφ d x, hψ d x]⟩

theorem equiv_iff_comp_hat (μ : Completion α G) (η : Completion α H) (φ : G ≃* H) :
    (∀ d (x : α.X d), φ (μ.toHom d x) = η.toHom d x) ↔ φ.toMonoidHom.comp μ.hat = η.hat := by
  constructor
  · intro h
    exact hom_ext fun d x => by simp [h d x]
  · intro h d x
    have := congrArg (fun f => f (ξ α d x)) h
    simpa using this

theorem isEquivalent_iff_ker_hat_eq (μ : Completion α G) (η : Completion α H) :
    IsEquivalent μ η ↔ μ.hat.ker = η.hat.ker := by
  constructor
  · rintro ⟨φ, hφ⟩
    have h := (equiv_iff_comp_hat μ η φ).mp hφ
    rw [← h, MonoidHom.ker_comp_of_injective _ _ φ.injective]
  · intro hk
    let e₁ : gp α ⧸ μ.hat.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective μ.hat μ.hat_surjective
    let e₂ : gp α ⧸ η.hat.ker ≃* H := QuotientGroup.quotientKerEquivOfSurjective η.hat η.hat_surjective
    refine ⟨e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hk).trans e₂), fun d x => ?_⟩
    have h1 : e₁.symm (μ.toHom d x) = (QuotientGroup.mk (ξ α d x) : gp α ⧸ μ.hat.ker) := by
      rw [MulEquiv.symm_apply_eq]
      exact (hat_ξ μ d x).symm
    simp only [MulEquiv.trans_apply]
    rw [h1]
    exact hat_ξ η d x

@[expose] def act (a : Aut α) (μ : Completion α G) : Completion α G where
  toHom d := (μ.toHom d).comp ((a⁻¹).1 d).toMonoidHom
  comm {d e} h x := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← (a⁻¹).comm h x, μ.comm]
  gen := by
    rw [eq_top_iff, ← μ.gen]
    refine iSup_le fun d => ?_
    rintro _ ⟨x, rfl⟩
    refine le_iSup (fun d => ((μ.toHom d).comp ((a⁻¹).1 d).toMonoidHom).range) d ?_
    exact ⟨((a⁻¹).1 d).symm x, by simp⟩

@[simp] theorem act_apply (a : Aut α) (μ : Completion α G) (d : D) (x : α.X d) :
    (act a μ).toHom d x = μ.toHom d ((a⁻¹).1 d x) := rfl

@[simp] theorem act_one (μ : Completion α G) : act 1 μ = μ := by
  ext d x
  simp

theorem act_mul (a b : Aut α) (μ : Completion α G) : act (a * b) μ = act a (act b μ) := by
  ext d x
  simp [mul_inv_rev]

theorem IsEquivalent.act {μ : Completion α G} {η : Completion α H} (h : IsEquivalent μ η)
    (a : Aut α) : IsEquivalent (act a μ) (act a η) := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun d x => by simp [hφ]⟩

theorem act_inv_act (a : Aut α) (μ : Completion α G) : act a⁻¹ (act a μ) = μ := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[expose] def IsQuasiEquivalent {γ : Amalgam.{u, v} D} (μ : Completion α G) (η : Completion γ H) :
    Prop :=
  ∃ (φ : G ≃* H) (ψ : Iso α γ), ∀ d (x : α.X d), φ (μ.toHom d x) = η.toHom d (ψ.toEquiv d x)

@[expose] def _root_.CFSG.Quasithin.Amalgam.Aut.toIso (a : Aut α) : Iso α α where
  toEquiv := a.1
  comm h x := a.comm h x

@[expose] def _root_.CFSG.Quasithin.Amalgam.Iso.toAut (ψ : Iso α α) : Aut α :=
  ⟨fun d => ψ.toEquiv d, fun {_ _} h x => ψ.comm h x⟩

theorem isQuasiEquivalent_iff_exists_act (μ : Completion α G) (η : Completion α H) :
    IsQuasiEquivalent μ η ↔ ∃ a : Aut α, IsEquivalent (act a μ) η := by
  constructor
  · rintro ⟨φ, ψ, hφ⟩
    refine ⟨ψ.toAut, φ, fun d x => ?_⟩
    have := hφ d (((ψ.toAut)⁻¹).1 d x)
    simp [Iso.toAut] at this
    exact this
  · rintro ⟨a, φ, hφ⟩
    refine ⟨φ, a.toIso, fun d x => ?_⟩
    have := hφ d (a.1 d x)
    simpa [Aut.toIso] using this

end Completion

theorem hatPiHom_compat (a : Aut α) {d e : D} (h : d ≤ e) (x : α.X d) :
    ((ξ α e).comp (a.1 e).toMonoidHom) (α.map h x) = ((ξ α d).comp (a.1 d).toMonoidHom) x := by
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← a.comm h x, ξ_map]

noncomputable def hatPiHom (a : Aut α) : gp α →* gp α :=
  lift (fun d => (ξ α d).comp (a.1 d).toMonoidHom) (hatPiHom_compat a)

@[simp] theorem hatPiHom_ξ (a : Aut α) (d : D) (x : α.X d) :
    hatPiHom a (ξ α d x) = ξ α d (a.1 d x) :=
  lift_ξ _ (hatPiHom_compat a) d x

theorem hatPiHom_mul (a b : Aut α) : hatPiHom (a * b) = (hatPiHom a).comp (hatPiHom b) :=
  hom_ext fun d x => by simp

@[simp] theorem hatPiHom_one : hatPiHom (1 : Aut α) = MonoidHom.id (gp α) :=
  hom_ext fun d x => by simp

@[expose] noncomputable def hatPi : Aut α →* MulAut (gp α) where
  toFun a :=
    { toFun := hatPiHom a
      invFun := hatPiHom a⁻¹
      left_inv := fun g => by
        have : (hatPiHom a⁻¹).comp (hatPiHom a) = MonoidHom.id _ := by
          rw [← hatPiHom_mul, inv_mul_cancel, hatPiHom_one]
        exact congrArg (fun f => f g) this
      right_inv := fun g => by
        have : (hatPiHom a).comp (hatPiHom a⁻¹) = MonoidHom.id _ := by
          rw [← hatPiHom_mul, mul_inv_cancel, hatPiHom_one]
        exact congrArg (fun f => f g) this
      map_mul' := map_mul _ }
  map_one' := by
    ext g
    simp
  map_mul' a b := by
    ext g
    simp [hatPiHom_mul]

theorem hatPi_apply (a : Aut α) (g : gp α) : hatPi a g = hatPiHom a g := rfl

@[simp] theorem hatPi_ξ (a : Aut α) (d : D) (x : α.X d) :
    hatPi a (ξ α d x) = ξ α d (a.1 d x) := hatPiHom_ξ a d x

theorem hatPi_ξ_comp (a : Aut α) (d : D) :
    (hatPi a).toMonoidHom.comp (ξ α d) = (ξ α d).comp (a.1 d).toMonoidHom :=
  MonoidHom.ext fun x => hatPi_ξ a d x

namespace Completion

variable {G : Type w} [Group G]

theorem hat_act (a : Aut α) (μ : Completion α G) :
    (act a μ).hat = μ.hat.comp (hatPi a⁻¹).toMonoidHom :=
  hom_ext fun d x => by
    rw [hat_ξ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hatPi_ξ, hat_ξ]
    rfl

theorem ker_hat_act (a : Aut α) (μ : Completion α G) :
    (act a μ).hat.ker = μ.hat.ker.map (hatPi a).toMonoidHom := by
  have e : hatPi (α := α) a⁻¹ = (hatPi a)⁻¹ := map_inv hatPi a
  ext g
  rw [MonoidHom.mem_ker, hat_act, Subgroup.mem_map]
  constructor
  · intro hg
    refine ⟨hatPi a⁻¹ g, hg, ?_⟩
    show hatPi a (hatPi a⁻¹ g) = g
    rw [e, MulAut.inv_def, MulEquiv.apply_symm_apply]
  · rintro ⟨k, hk, rfl⟩
    show μ.hat (hatPi a⁻¹ (hatPi a k)) = 1
    rw [e, MulAut.inv_def, MulEquiv.symm_apply_apply]
    exact hk

theorem isEquivalent_act_iff (a : Aut α) (μ : Completion α G) :
    IsEquivalent (act a μ) μ ↔ μ.hat.ker.map (hatPi a).toMonoidHom = μ.hat.ker := by
  rw [isEquivalent_iff_ker_hat_eq, ker_hat_act]

theorem mulAut_ext {μ : Completion α G} {b₁ b₂ : MulAut G}
    (h : ∀ d (x : α.X d), b₁ (μ.toHom d x) = b₂ (μ.toHom d x)) : b₁ = b₂ := by
  have hle : (⊤ : Subgroup G) ≤ MonoidHom.eqLocus b₁.toMonoidHom b₂.toMonoidHom := by
    rw [← μ.gen, iSup_le_iff]
    rintro d _ ⟨x, rfl⟩
    exact h d x
  ext g
  exact hle (Subgroup.mem_top g)

@[expose] def stabilizer (μ : Completion α G) : Subgroup (Aut α) where
  carrier := {a | IsEquivalent (act a μ) μ}
  one_mem' := by
    show IsEquivalent (act 1 μ) μ
    rw [act_one]
    exact IsEquivalent.refl μ
  mul_mem' := by
    intro a b ha hb
    show IsEquivalent (act (a * b) μ) μ
    rw [act_mul]
    exact (IsEquivalent.act hb a).trans ha
  inv_mem' := by
    intro a ha
    show IsEquivalent (act a⁻¹ μ) μ
    have := (IsEquivalent.act ha a⁻¹).symm
    rwa [act_inv_act] at this

theorem mem_stabilizer {μ : Completion α G} {a : Aut α} :
    a ∈ stabilizer μ ↔ IsEquivalent (act a μ) μ := Iff.rfl

@[expose] noncomputable def plus (μ : Completion α G) : gp α ⧸ μ.hat.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective μ.hat μ.hat_surjective

theorem plus_mk (μ : Completion α G) (g : gp α) : μ.plus (QuotientGroup.mk g) = μ.hat g := rfl

noncomputable def aPlus (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ) :
    MulAut (gp α ⧸ μ.hat.ker) :=
  QuotientGroup.congr μ.hat.ker μ.hat.ker (hatPi a) ((isEquivalent_act_iff a μ).mp h)

theorem aPlus_mk (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ) (g : gp α) :
    aPlus μ a h (QuotientGroup.mk g) = QuotientGroup.mk (hatPi a g) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem aPlus_mk_ξ (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ) (d : D)
    (x : α.X d) :
    aPlus μ a h (QuotientGroup.mk (ξ α d x)) = QuotientGroup.mk (ξ α d (a.1 d x)) := by
  rw [aPlus_mk, hatPi_ξ]

noncomputable def aMinus (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ) : MulAut G :=
  μ.plus.symm.trans ((aPlus μ a h).trans μ.plus)

theorem aMinus_apply (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ) (d : D)
    (x : α.X d) : aMinus μ a h (μ.toHom d x) = μ.toHom d (a.1 d x) := by
  have h1 : μ.plus.symm (μ.toHom d x) = QuotientGroup.mk (ξ α d x) := by
    rw [MulEquiv.symm_apply_eq]
    exact (hat_ξ μ d x).symm
  simp only [aMinus, MulEquiv.trans_apply]
  rw [h1, aPlus_mk_ξ, plus_mk, hat_ξ]

theorem eq_aMinus_iff (μ : Completion α G) (a : Aut α) (h : a ∈ stabilizer μ)
    (b : MulAut G) : b = aMinus μ a h ↔ ∀ d (x : α.X d), b (μ.toHom d x) = μ.toHom d (a.1 d x) := by
  constructor
  · rintro rfl d x
    exact aMinus_apply μ a h d x
  · intro hb
    exact mulAut_ext fun d x => by rw [hb, aMinus_apply]

noncomputable def piMinus (μ : Completion α G) : stabilizer μ →* MulAut G where
  toFun a := aMinus μ a.1 a.2
  map_one' := by
    refine ((eq_aMinus_iff μ 1 (one_mem (stabilizer μ)) 1).mpr fun d x => rfl).symm
  map_mul' a b := by
    refine ((eq_aMinus_iff μ (a.1 * b.1) (mul_mem a.2 b.2) _).mpr fun d x => ?_).symm
    show aMinus μ a.1 a.2 (aMinus μ b.1 b.2 (μ.toHom d x)) = μ.toHom d (a.1.1 d (b.1.1 d x))
    rw [aMinus_apply, aMinus_apply]

theorem piMinus_apply (μ : Completion α G) (a : stabilizer μ) (d : D) (x : α.X d) :
    piMinus μ a (μ.toHom d x) = μ.toHom d (a.1.1 d x) := aMinus_apply μ a.1 a.2 d x

@[expose] def normAut (μ : Completion α G) : Subgroup (MulAut G) where
  carrier := {b | ∀ d, (μ.toHom d).range.map (b : G →* G) = (μ.toHom d).range}
  one_mem' := by
    intro d
    ext g
    simp
  mul_mem' := by
    intro b c hb hc d
    have : ((b * c : MulAut G) : G →* G) = (b : G →* G).comp (c : G →* G) := rfl
    rw [this, ← Subgroup.map_map, hc d, hb d]
  inv_mem' := by
    intro b hb d
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hmem : y ∈ (μ.toHom d).range.map (b : G →* G) := by rw [hb d]; exact hy
      obtain ⟨z, hz, hzy⟩ := hmem
      have e : b⁻¹ y = z := by
        rw [← hzy]
        simp
      show b⁻¹ y ∈ (μ.toHom d).range
      rw [e]
      exact hz
    · intro hg
      refine ⟨b g, ?_, by simp⟩
      have hmem : b g ∈ (μ.toHom d).range.map (b : G →* G) := ⟨g, hg, rfl⟩
      rwa [hb d] at hmem

theorem mem_normAut {μ : Completion α G} {b : MulAut G} :
    b ∈ normAut μ ↔ ∀ d, (μ.toHom d).range.map (b : G →* G) = (μ.toHom d).range := Iff.rfl

theorem apply_mem_range_of_mem_normAut {μ : Completion α G} {b : MulAut G} (hb : b ∈ normAut μ)
    (d : D) (x : α.X d) : b (μ.toHom d x) ∈ (μ.toHom d).range := by
  have hmem : b (μ.toHom d x) ∈ (μ.toHom d).range.map (b : G →* G) := ⟨μ.toHom d x, ⟨x, rfl⟩, rfl⟩
  rwa [hb d] at hmem

@[expose] noncomputable def sigmaApp (μ : Completion α G) (hμ : μ.IsFaithful) (b : MulAut G)
    (hb : b ∈ normAut μ) (d : D) : MulAut (α.X d) :=
  (MonoidHom.ofInjective (hμ d)).trans
    (((MulEquiv.subgroupMap b (μ.toHom d).range).trans (MulEquiv.subgroupCongr (mem_normAut.mp hb d))).trans
      (MonoidHom.ofInjective (hμ d)).symm)

theorem sigmaApp_spec (μ : Completion α G) (hμ : μ.IsFaithful) (b : MulAut G) (hb : b ∈ normAut μ)
    (d : D) (x : α.X d) : μ.toHom d (sigmaApp μ hμ b hb d x) = b (μ.toHom d x) := by
  have h1 : ∀ y : α.X d, μ.toHom d y = (((MonoidHom.ofInjective (hμ d)) y : (μ.toHom d).range) : G) :=
    fun y => (MonoidHom.ofInjective_apply (hμ d)).symm
  unfold sigmaApp
  simp only [MulEquiv.trans_apply]
  rw [h1, MulEquiv.apply_symm_apply, MulEquiv.subgroupCongr_apply]
  rw [h1 x]
  rfl

theorem sigmaApp_eq_iff (μ : Completion α G) (hμ : μ.IsFaithful) (b : MulAut G) (hb : b ∈ normAut μ)
    (d : D) (x y : α.X d) : sigmaApp μ hμ b hb d x = y ↔ μ.toHom d y = b (μ.toHom d x) := by
  rw [← sigmaApp_spec μ hμ b hb d x]
  exact ⟨fun h => by rw [h], fun h => (hμ d h).symm⟩

theorem sigmaApp_comm (μ : Completion α G) (hμ : μ.IsFaithful) (b : MulAut G) (hb : b ∈ normAut μ)
    {d e : D} (h : d ≤ e) (x : α.X d) :
    α.map h (sigmaApp μ hμ b hb d x) = sigmaApp μ hμ b hb e (α.map h x) := by
  apply hμ e
  rw [μ.comm, sigmaApp_spec, sigmaApp_spec, μ.comm]

@[expose] noncomputable def sigmaAut (μ : Completion α G) (hμ : μ.IsFaithful) (b : normAut μ) :
    Aut α :=
  ⟨fun d => sigmaApp μ hμ b.1 b.2 d, fun {_ _} h x => sigmaApp_comm μ hμ b.1 b.2 h x⟩

theorem sigmaAut_apply (μ : Completion α G) (hμ : μ.IsFaithful) (b : normAut μ) (d : D)
    (x : α.X d) : (sigmaAut μ hμ b).1 d x = sigmaApp μ hμ b.1 b.2 d x := rfl

noncomputable def sigma (μ : Completion α G) (hμ : μ.IsFaithful) : normAut μ →* Aut α where
  toFun := sigmaAut μ hμ
  map_one' := by
    apply Subtype.ext
    funext d
    ext x
    show sigmaApp μ hμ (1 : normAut μ).1 (1 : normAut μ).2 d x = x
    rw [sigmaApp_eq_iff]
    rfl
  map_mul' b c := by
    apply Subtype.ext
    funext d
    ext x
    show sigmaApp μ hμ (b * c : normAut μ).1 (b * c : normAut μ).2 d x =
      sigmaApp μ hμ b.1 b.2 d (sigmaApp μ hμ c.1 c.2 d x)
    rw [sigmaApp_eq_iff, sigmaApp_spec, sigmaApp_spec]
    rfl

theorem sigma_mem_stabilizer (μ : Completion α G) (hμ : μ.IsFaithful) (b : normAut μ) :
    sigma μ hμ b ∈ stabilizer μ := by
  show IsEquivalent (act (sigma μ hμ b) μ) μ
  refine ⟨b.1, fun d x => ?_⟩
  rw [act_apply]
  have h1 : (sigma μ hμ b)⁻¹ = sigma μ hμ b⁻¹ := (map_inv (sigma μ hμ) b).symm
  rw [h1]
  show b.1 (μ.toHom d (sigmaApp μ hμ (b⁻¹ : normAut μ).1 (b⁻¹ : normAut μ).2 d x)) = μ.toHom d x
  rw [sigmaApp_spec]
  show b.1 ((b.1)⁻¹ (μ.toHom d x)) = μ.toHom d x
  simp

theorem piMinus_sigma (μ : Completion α G) (hμ : μ.IsFaithful) (b : normAut μ) :
    piMinus μ ⟨sigma μ hμ b, sigma_mem_stabilizer μ hμ b⟩ = b.1 := by
  apply mulAut_ext (μ := μ)
  intro d x
  rw [piMinus_apply]
  show μ.toHom d (sigmaApp μ hμ b.1 b.2 d x) = b.1 (μ.toHom d x)
  exact sigmaApp_spec μ hμ b.1 b.2 d x

theorem piMinus_mem_normAut (μ : Completion α G) (a : stabilizer μ) : piMinus μ a ∈ normAut μ := by
  intro d
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨a.1.1 d x, (piMinus_apply μ a d x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨μ.toHom d ((a.1⁻¹).1 d y), ⟨_, rfl⟩, ?_⟩
    show piMinus μ a (μ.toHom d ((a.1⁻¹).1 d y)) = μ.toHom d y
    rw [piMinus_apply, Aut.apply_inv_apply]

theorem sigma_piMinus (μ : Completion α G) (hμ : μ.IsFaithful) (a : stabilizer μ) :
    sigma μ hμ ⟨piMinus μ a, piMinus_mem_normAut μ a⟩ = a.1 := by
  apply Subtype.ext
  funext d
  ext x
  show sigmaApp μ hμ (piMinus μ a) (piMinus_mem_normAut μ a) d x = a.1.1 d x
  rw [sigmaApp_eq_iff, piMinus_apply]

theorem range_sigma (μ : Completion α G) (hμ : μ.IsFaithful) :
    (sigma μ hμ).range = stabilizer μ := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact sigma_mem_stabilizer μ hμ b
  · intro ha
    exact ⟨⟨piMinus μ ⟨a, ha⟩, piMinus_mem_normAut μ ⟨a, ha⟩⟩, sigma_piMinus μ hμ ⟨a, ha⟩⟩

end Completion

end Amalgam

end CFSG.Quasithin
