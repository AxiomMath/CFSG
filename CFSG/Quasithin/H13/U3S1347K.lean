module

public import CFSG.Quasithin.H13.U3S134Defs
public import CFSG.Quasithin.H13.L32AStRec

public section

namespace CFSG.Quasithin.H13.U3

namespace L32Mod

open CFSG.Quasithin.H6 CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem det_eq_one_of_zmod_two (A : GL (Fin 3) (ZMod 2)) :
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

@[expose] noncomputable def stEquiv : ↥(StatedSL 3 (ZMod 2)) ≃* Γ where
  toFun γ := ⟨((γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)),
    det_eq_one_of_zmod_two _⟩
  invFun g := ⟨Matrix.SpecialLinearGroup.toGL g, Subgroup.subset_closure (by
    exact g.2)⟩
  left_inv γ := Subtype.ext (Units.ext rfl)
  right_inv g := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem stEquiv_coe (γ : ↥(StatedSL 3 (ZMod 2))) :
    ((stEquiv γ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      ((γ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem stEquiv_inv_coe (γ : ↥(StatedSL 3 (ZMod 2))) :
    (((stEquiv γ)⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (((γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  rw [← map_inv, stEquiv_coe]

@[expose] def addEnd {V : Type} [CommGroup V] (a : MulAut V) : AddMonoid.End (Additive V) where
  toFun m := Additive.ofMul (a (Additive.toMul m))
  map_zero' := by simp
  map_add' m n := by simp [map_mul]

@[expose] def toAddRep {V : Type} [CommGroup V] (σ : Γ →* MulAut V) :
    Γ →* AddMonoid.End (Additive V) where
  toFun g := addEnd (σ g)
  map_one' := by
    ext m
    simp [addEnd]
    rfl
  map_mul' g h := by
    ext m
    simp [addEnd, map_mul]
    rfl

theorem toAddRep_apply {V : Type} [CommGroup V] (σ : Γ →* MulAut V) (g : Γ) (m : Additive V) :
    toAddRep σ g m = Additive.ofMul (σ g (Additive.toMul m)) := rfl

theorem realizesVia_top_of_equiv {S : Type} [CommGroup S] {D : FFModel} (hker : D.ker = ⊥)
    (hsec : ∀ (γ : D.Gam), ∀ m ∈ D.sec, D.act γ m ∈ D.sec) (hact1 : ∀ γ : D.Gam, D.act γ 1 = 1)
    (H : Subgroup (MulAut S))
    (π : D.Gam →* ↥H) (hπ : Function.Surjective π) (β : S ≃* ↥D.sec)
    (hβ : ∀ (γ : D.Gam) (s : S), (β (((π γ : ↥H) : MulAut S) s) : D.Amb) = D.act γ (β s)) :
    D.RealizesVia H ⊤ ⊥ π := by
  refine ⟨hπ, le_top, hker ▸ bot_le, fun _ u _ => trivial,
    fun _ z hz => by simpa using hz, hsec, fun γ m hm => ?_, ?_⟩
  · rw [hker, Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  refine ⟨(QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
    (β.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom), ?_, ?_, ?_⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨β.symm m, trivial⟩, by simp⟩
  · intro u
    show (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot,
      Subgroup.mem_bot]
    constructor
    · intro h
      have : β (u : S) = 1 := Subtype.ext h
      exact β.injective (by rw [this, map_one])
    · intro h
      rw [h, map_one]
      rfl
  · intro γ u m hu hm hum
    have hu' : (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk m := hum
    have hbm : β (u : S) = m := by
      have := QuotientGroup.eq.1 hu'
      rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at this
      have h2 : ((β (u : S))⁻¹ * m : ↥D.sec) = 1 := Subtype.ext this
      exact inv_mul_eq_one.1 h2
    show (QuotientGroup.mk (β (((π γ : ↥H) : MulAut S) (u : S))) :
      ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    congr 1
    apply Subtype.ext
    rw [hβ γ (u : S), hbm]

theorem realizesVia_sub_of_equiv {V : Type} [CommGroup V] {Γ' : Type} [Group Γ'] {A : Type}
    [CommGroup A] (act : Γ' → A → A) (hact1 : ∀ γ, act γ 1 = 1) {H : Subgroup (MulAut V)}
    {U : Subgroup V} (π : Γ' →* ↥H) (hπ : Function.Surjective π)
    (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U) (e : ↥U ≃* A)
    (he : ∀ (γ : Γ') (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (e u)) :
    (FFModel.mk Γ' A act ⊤ ⊥).RealizesVia H U ⊥ π := by
  refine ⟨hπ, bot_le, bot_le, hHU, ?_, fun _ _ _ => trivial, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    change m ∈ (⊥ : Subgroup A) at hm
    change act γ m ∈ (⊥ : Subgroup A)
    rw [Subgroup.mem_bot] at hm ⊢
    rw [hm, hact1]
  · let β : ↥U →* ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ :=
      (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom.comp e.toMonoidHom)
    have hβ : ∀ u : ↥U,
        β u = ((Subgroup.topEquiv.symm (e u) : ↥(⊤ : Subgroup A)) :
          ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤) := fun _ => rfl
    have hinj : ∀ a b : ↥(⊤ : Subgroup A), ((a : ↥(⊤ : Subgroup A) ⧸
        (⊥ : Subgroup A).subgroupOf ⊤) = b) → a = b := by
      intro a b h
      rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h
      exact (inv_mul_eq_one.mp h)
    refine ⟨β, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨⟨m, -⟩, rfl⟩ := QuotientGroup.mk_surjective y
      refine ⟨e.symm m, ?_⟩
      rw [hβ]
      congr 1
      exact Subtype.ext (by simp)
    · intro u
      rw [hβ, QuotientGroup.eq_one_iff, Subgroup.bot_subgroupOf, Subgroup.mem_bot,
        Subgroup.mem_bot]
      constructor
      · intro h
        have h' := congrArg Subtype.val h
        simpa using h'
      · intro h
        have hu1 : u = 1 := Subtype.ext h
        apply Subtype.ext
        simp [hu1]
    · intro γ u m hu hm hum
      rw [hβ] at hum ⊢
      have hm' := hinj _ _ hum
      congr 1
      apply Subtype.ext
      change e ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (m : A)
      rw [he, ← hm']
      rfl

theorem idxOf_zero : idxOf 0 = 0 := by decide

theorem vecOf_zero : vecOf 0 = 0 := by decide

@[expose] def coreFano : Multiplicative Core ≃* ↥fanoCoreSub where
  toFun c := ⟨Multiplicative.ofAdd (fun v => (Multiplicative.toAdd c).1 (idxOf v)), by
    have hc := mem_coreSub.1 (Multiplicative.toAdd c).2
    refine ⟨by show (Multiplicative.toAdd c).1 (idxOf 0) = 0; rw [idxOf_zero]; exact hc.1, ?_⟩
    show ∑ v, (Multiplicative.toAdd c).1 (idxOf v) = 0
    rw [← hc.2]
    exact Equiv.sum_comp vecEquiv.symm _⟩
  invFun F := Multiplicative.ofAdd ⟨fun i => Multiplicative.toAdd (F : Multiplicative
      ((Fin 3 → ZMod 2) → ZMod 2)) (vecOf i), by
    have hF := F.2
    rw [mem_coreSub]
    refine ⟨by rw [vecOf_zero]; exact hF.1, ?_⟩
    rw [← hF.2]
    exact Equiv.sum_comp vecEquiv _⟩
  left_inv c := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    show (Multiplicative.toAdd c).1 (idxOf (vecOf i)) = _
    rw [idxOf_vecOf]
  right_inv F := by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext v
    show Multiplicative.toAdd (F : Multiplicative ((Fin 3 → ZMod 2) → ZMod 2))
      (vecOf (idxOf v)) = _
    rw [vecOf_idxOf]
  map_mul' _ _ := rfl

theorem fanoCore_sec_inv (γ : ↥(StatedSL 3 (ZMod 2)))
    (m : Multiplicative ((Fin 3 → ZMod 2) → ZMod 2)) (hm : m ∈ fanoCoreSub) :
    FFModel.fanoCore.act γ m ∈ fanoCoreSub := by
  obtain ⟨hm0, hms⟩ := hm
  set A := (((γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) with hA
  set B := (((γ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    rfl
  let e : V3 ≃ V3 :=
    { toFun := fun v => A *ᵥ v
      invFun := fun v => B *ᵥ v
      left_inv := fun v => by
        show B *ᵥ (A *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
      right_inv := fun v => by
        show A *ᵥ (B *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec] }
  refine ⟨?_, ?_⟩
  · show Multiplicative.toAdd m (A *ᵥ 0) = 0
    rw [Matrix.mulVec_zero]
    exact hm0
  · show ∑ v, Multiplicative.toAdd m (A *ᵥ v) = 0
    rw [← hms]
    exact Equiv.sum_comp e (Multiplicative.toAdd m)

theorem fanoCore_act_one (γ : ↥(StatedSL 3 (ZMod 2))) :
    FFModel.fanoCore.act γ 1 = 1 := rfl

theorem smul_eq_mulVec_inv (γ : ↥(StatedSL 3 (ZMod 2))) (v : V3) :
    ((stEquiv γ)⁻¹ • v : V3) = (((γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, ← stEquiv_inv_coe]

theorem realizes_fanoCore {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (τ : Γ →* MulAut V)
    (hτ : ∀ g, τ g ∈ H) (hτs : ∀ a ∈ H, ∃ g, τ g = a) (hiso : IsoMod (toAddRep τ) ρCore) :
    FFModel.fanoCore.Realizes H ⊤ ⊥ := by
  obtain ⟨f, hf, hfe⟩ := hiso
  let e₀ : Core ≃+ Additive V := AddEquiv.ofBijective f hf
  have he₀ : ∀ c, e₀ c = f c := fun _ => rfl
  let π : ↥(StatedSL 3 (ZMod 2)) →* ↥H := (τ.codRestrict H hτ).comp stEquiv.toMonoidHom
  have hπ : ∀ γ, ((π γ : ↥H) : MulAut V) = τ (stEquiv γ) := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro a
    obtain ⟨g, hg⟩ := hτs a a.2
    exact ⟨stEquiv.symm g, Subtype.ext (by rw [hπ, MulEquiv.apply_symm_apply, hg])⟩
  let β : V ≃* ↥fanoCoreSub :=
    (MulEquiv.multiplicativeAdditive V).symm.trans (e₀.symm.toMultiplicative.trans coreFano)
  refine ⟨π, realizesVia_top_of_equiv (D := FFModel.fanoCore) rfl fanoCore_sec_inv
    fanoCore_act_one H π hπs β ?_⟩
  intro γ s
  have hc : e₀.symm (Additive.ofMul (τ (stEquiv γ) s)) =
      stEquiv γ • e₀.symm (Additive.ofMul s) := by
    rw [AddEquiv.symm_apply_eq, he₀]
    have h1 := hfe (stEquiv γ) (e₀.symm (Additive.ofMul s))
    rw [show ρCore (stEquiv γ) (e₀.symm (Additive.ofMul s)) =
      stEquiv γ • e₀.symm (Additive.ofMul s) from rfl] at h1
    rw [h1, ← he₀, AddEquiv.apply_symm_apply]
    rfl
  apply Multiplicative.toAdd.injective
  funext v
  show (e₀.symm (Additive.ofMul (τ (stEquiv γ) s))).1 (idxOf v) =
    (e₀.symm (Additive.ofMul s)).1 (idxOf ((((γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) :
      GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v))
  rw [hc, coe_smul_core, permOf_apply, vecOf_idxOf]
  exact congrArg (fun w => (e₀.symm (Additive.ofMul s)).1 (idxOf w)) (smul_eq_mulVec_inv γ v)

@[expose] noncomputable def subEquiv {V : Type} [CommGroup V] {U : AddSubgroup (Additive V)}
    (e : ↥U ≃+ V3) (w : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hw : w * w = 1) :
    ↥(AddSubgroup.toSubgroup' U) ≃* Multiplicative V3 where
  toFun x := Multiplicative.ofAdd (w *ᵥ e ⟨Additive.ofMul (x : V), x.2⟩)
  invFun y := ⟨Additive.toMul (e.symm (w *ᵥ Multiplicative.toAdd y) : Additive V),
    (e.symm (w *ᵥ Multiplicative.toAdd y)).2⟩
  left_inv x := by
    apply Subtype.ext
    show Additive.toMul ((e.symm (w *ᵥ (w *ᵥ e ⟨Additive.ofMul (x : V), x.2⟩)) :
      Additive V)) = (x : V)
    rw [Matrix.mulVec_mulVec, hw, Matrix.one_mulVec, AddEquiv.symm_apply_apply]
    rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    show w *ᵥ e ⟨Additive.ofMul (Additive.toMul ((e.symm (w *ᵥ Multiplicative.toAdd y) :
      Additive V))), _⟩ = Multiplicative.toAdd y
    have h1 : (⟨Additive.ofMul (Additive.toMul ((e.symm (w *ᵥ Multiplicative.toAdd y) :
        Additive V))), (e.symm (w *ᵥ Multiplicative.toAdd y)).2⟩ : ↥U) =
        e.symm (w *ᵥ Multiplicative.toAdd y) := rfl
    rw [h1, AddEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hw, Matrix.one_mulVec]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    show w *ᵥ e ⟨Additive.ofMul ((x : V) * y), _⟩ =
      w *ᵥ e ⟨Additive.ofMul (x : V), x.2⟩ + w *ᵥ e ⟨Additive.ofMul (y : V), y.2⟩
    rw [← Matrix.mulVec_add, ← map_add]
    rfl

theorem sumNatDual_of {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (τ : Γ →* MulAut V)
    (hτ : ∀ g, τ g ∈ H) (hτs : ∀ a ∈ H, ∃ g, τ g = a) {U₁ U₂ : AddSubgroup (Additive V)}
    (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (hinv₁ : ∀ g, ∀ m ∈ U₁, toAddRep τ g m ∈ U₁) (hinv₂ : ∀ g, ∀ m ∈ U₂, toAddRep τ g m ∈ U₂)
    (e₁ : ↥U₁ ≃+ V3) (he₁ : ∀ (g : Γ) (m : Additive V) (hm : m ∈ U₁)
      (hgm : toAddRep τ g m ∈ U₁), e₁ ⟨toAddRep τ g m, hgm⟩ = g • e₁ ⟨m, hm⟩)
    (e₂ : ↥U₂ ≃+ V3) (he₂ : ∀ (g : Γ) (m : Additive V) (hm : m ∈ U₂)
      (hgm : toAddRep τ g m ∈ U₂), e₂ ⟨toAddRep τ g m, hgm⟩ = graph g • e₂ ⟨m, hm⟩) :
    ∃ U₁' U₂' : Subgroup V, U₁' ⊔ U₂' = ⊤ ∧ U₁' ⊓ U₂' = ⊥ ∧
      ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥H,
        (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H U₁' ⊥ π ∧
        (FFModel.dualNat (StatedSL 3 (ZMod 2))).RealizesVia H U₂' ⊥ π := by
  let π : ↥(StatedSL 3 (ZMod 2)) →* ↥H := (τ.codRestrict H hτ).comp stEquiv.toMonoidHom
  have hπ : ∀ γ, ((π γ : ↥H) : MulAut V) = τ (stEquiv γ) := fun _ => rfl
  have hπs : Function.Surjective π := by
    intro a
    obtain ⟨g, hg⟩ := hτs a a.2
    exact ⟨stEquiv.symm g, Subtype.ext (by rw [hπ, MulEquiv.apply_symm_apply, hg])⟩
  have hHU : ∀ U : AddSubgroup (Additive V), (∀ g, ∀ m ∈ U, toAddRep τ g m ∈ U) →
      ∀ h : ↥H, ∀ u ∈ AddSubgroup.toSubgroup' U,
        (h : MulAut V) u ∈ AddSubgroup.toSubgroup' U := by
    intro U hU h u hu
    obtain ⟨g, hg⟩ := hτs h h.2
    rw [← hg]
    exact hU g _ hu
  refine ⟨AddSubgroup.toSubgroup' U₁, AddSubgroup.toSubgroup' U₂,
    by rw [← map_sup, hsup, map_top], by rw [← map_inf, hinf, map_bot], π, ?_, ?_⟩
  · refine realizesVia_sub_of_equiv (natAct (StatedSL 3 (ZMod 2)))
      (fun γ => by
        show Multiplicative.ofAdd (_ *ᵥ (0 : Fin 3 → ZMod 2)) = 1
        rw [Matrix.mulVec_zero]
        rfl) π hπs (hHU U₁ hinv₁)
      (subEquiv e₁ 1 (Matrix.mul_one 1)) (fun γ u hu => ?_)
    apply Multiplicative.toAdd.injective
    have hu₁ : Additive.ofMul (u : V) ∈ U₁ := u.2
    have hu' : toAddRep τ (stEquiv γ) (Additive.ofMul (u : V)) ∈ U₁ := hu
    show 1 *ᵥ e₁ ⟨toAddRep τ (stEquiv γ) (Additive.ofMul (u : V)), hu'⟩ =
      (((γ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (1 *ᵥ e₁ ⟨Additive.ofMul (u : V), hu₁⟩)
    rw [he₁ _ _ hu₁, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.SpecialLinearGroup.smul_def,
      Matrix.smul_eq_mulVec]
    rfl
  · refine realizesVia_sub_of_equiv (dualNatAct (StatedSL 3 (ZMod 2)))
      (fun γ => by
        show Multiplicative.ofAdd (_ *ᵥ (0 : Fin 3 → ZMod 2)) = 1
        rw [Matrix.mulVec_zero]
        rfl) π hπs (hHU U₂ hinv₂)
      (subEquiv e₂ w0m w0m_mul_self) (fun γ u hu => ?_)
    apply Multiplicative.toAdd.injective
    have hu₂ : Additive.ofMul (u : V) ∈ U₂ := u.2
    have hu' : toAddRep τ (stEquiv γ) (Additive.ofMul (u : V)) ∈ U₂ := hu
    show w0m *ᵥ e₂ ⟨toAddRep τ (stEquiv γ) (Additive.ofMul (u : V)), hu'⟩ =
      ((((γ⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) *ᵥ (w0m *ᵥ e₂ ⟨Additive.ofMul (u : V), hu₂⟩)
    rw [he₂ _ _ hu₂, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, graph_apply,
      ← stEquiv_inv_coe]
    show w0m *ᵥ ((w0m * (((stEquiv γ)⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ * w0m) *ᵥ _) = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      w0m_mul_self, Matrix.one_mul]

end L32Mod

end CFSG.Quasithin.H13.U3
