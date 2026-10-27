module

public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.B3Off
public import CFSG.Quasithin.Background.HTransport
public import CFSG.Quasithin.EmptyFaithful.Vocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.GroupTheory.WeirSylow

namespace CFSG.Quasithin.A38c5

open CFSG.Quasithin.B3

section Iso

variable {W : Type} [CommGroup W]

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem quadPolar_one_left (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (y : W) :
    quadPolar q 1 y = 0 := by
  unfold quadPolar
  rw [one_mul, hq.1, add_zero]
  exact CharTwo.add_self_eq_zero _

theorem quadPolar_one_right (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (x : W) :
    quadPolar q x 1 = 0 := by
  unfold quadPolar
  rw [mul_one, hq.1, add_zero]
  exact CharTwo.add_self_eq_zero _

abbrev zmodModOf (hW : ∀ w : W, w ^ 2 = 1) : Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    have : Additive.toMul x ^ 2 = 1 := hW _
    apply Additive.toMul.injective
    simpa using this)

variable [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def polarForm (q : W → ZMod 2) (hq : IsQuadraticFormOn q) :
    LinearMap.BilinForm (ZMod 2) (Additive W) :=
  LinearMap.mk₂ (ZMod 2) (fun x y => quadPolar q (Additive.toMul x) (Additive.toMul y))
    (fun x x' y => hq.2.1 _ _ _)
    (fun c x y => by
      rcases zmod_two_cases c with rfl | rfl
      · simp [quadPolar_one_left q hq]
      · simp)
    (fun x y y' => hq.2.2 _ _ _)
    (fun c x y => by
      rcases zmod_two_cases c with rfl | rfl
      · simp [quadPolar_one_right q hq]
      · simp)

theorem polarForm_apply (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (x y : Additive W) :
    polarForm q hq x y = quadPolar q (Additive.toMul x) (Additive.toMul y) := rfl

@[expose] def qAdd (q : W → ZMod 2) (x : Additive W) : ZMod 2 := q (Additive.toMul x)

theorem qAdd_add (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (x y : Additive W) :
    qAdd q (x + y) = qAdd q x + qAdd q y + polarForm q hq x y := by
  rw [polarForm_apply]
  unfold qAdd quadPolar
  have key : ∀ a b c : ZMod 2, c = a + b + (c + a + b) := by decide
  have : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
  rw [this]
  exact key _ _ _

theorem polarForm_symplectic (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q)
    (hW : ∀ w : W, w ^ 2 = 1) : IsSymplectic (polarForm q hq) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · rw [polarForm_apply]
    unfold quadPolar
    have : Additive.toMul x * Additive.toMul x = 1 := by rw [← pow_two]; exact hW _
    rw [this, hq.1, zero_add]
    exact CharTwo.add_self_eq_zero _
  · apply Additive.toMul.injective
    apply hnd
    intro y
    simpa [polarForm_apply] using hx (Additive.ofMul y)

section Model

variable [Finite W]

theorem finrank_additive_of_card (hW : Nat.card W = 2 ^ 6) :
    Module.finrank (ZMod 2) (Additive W) = 6 := by
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  have e : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  rw [e, hW, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

theorem isPlusType_polar (q : W → ZMod 2) (hq : IsQuadraticFormOn q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hW : Nat.card W = 2 ^ 6) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad (f := polarForm q hq) (q := qAdd q) (qAdd_add q hq)) := by
  refine ⟨AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup E), ?_, ?_⟩
  · have h1 : Module.finrank (ZMod 2) (Additive W) = 6 := finrank_additive_of_card hW
    have : Module.Finite (ZMod 2)
        ↥(AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup E)) := Module.Finite.of_finite
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup E)))
    have e : Nat.card ↥(AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup E)) = Nat.card E :=
      Nat.card_congr (Equiv.subtypeEquiv Additive.toMul (fun x => Iff.rfl))
    rw [e, hE, Nat.card_zmod] at h
    have h3 := (Nat.pow_right_injective (le_refl 2) h).symm
    omega
  · intro x hx
    exact hEq (Additive.toMul x) hx

omit [Module (ZMod 2) (Additive W)] in
theorem exists_isometry_model (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6) :
    ∃ ε : W ≃* Multiplicative p4insporth_V8,
      ∀ w, p4insporth_q8 (Multiplicative.toAdd (ε w)) = q w := by
  let _ : Module (ZMod 2) (Additive W) := zmodModOf hW
  have hsymp := polarForm_symplectic q hq hnd hW
  have hq' := qAdd_add q hq
  have hdim := finrank_additive_of_card hcard
  have hplus := isPlusType_polar q hq E hE hEq hcard
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (n := 3)
    (p4insporth_nondegenerate_quad hsymp hq')
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    (by rw [hdim]) p4insporth_finrank8 (iff_of_true hplus p4insporth_plus8)
  refine ⟨{ toFun := fun w => Multiplicative.ofAdd (e.toLinearEquiv (Additive.ofMul w))
            invFun := fun v => Additive.toMul (e.toLinearEquiv.symm (Multiplicative.toAdd v))
            left_inv := fun w => by simp
            right_inv := fun v => by simp
            map_mul' := fun a b => by
              change Multiplicative.ofAdd (e.toLinearEquiv (Additive.ofMul a + Additive.ofMul b)) = _
              rw [map_add]
              rfl }, fun w => ?_⟩
  exact e.map_app (Additive.ofMul w)

end Model

end Iso

section Cvt

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def cvtEquiv (g : GLV V) : MulAut (Multiplicative V) where
  toFun v := Multiplicative.ofAdd (g (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (g.symm (Multiplicative.toAdd v))
  left_inv v := by simp
  right_inv v := by simp
  map_mul' a b := by
    change Multiplicative.ofAdd (g (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
    rw [map_add]
    rfl

@[expose] def cvt : GLV V →* MulAut (Multiplicative V) where
  toFun := cvtEquiv
  map_one' := by
    ext v
    rfl
  map_mul' a b := by
    ext v
    rfl

theorem cvt_apply (g : GLV V) (v : Multiplicative V) :
    cvt g v = Multiplicative.ofAdd (g (Multiplicative.toAdd v)) := rfl

theorem cvt_surjective : Function.Surjective (cvt (V := V)) := by
  intro φ
  let f : V ≃+ V :=
    { toFun := fun x => Multiplicative.toAdd (φ (Multiplicative.ofAdd x))
      invFun := fun x => Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd x))
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun a b => by
        change Multiplicative.toAdd (φ (Multiplicative.ofAdd a * Multiplicative.ofAdd b)) = _
        rw [map_mul]
        rfl }
  let g : GLV V := f.toLinearEquiv (fun c x => ZMod.map_smul f.toAddMonoidHom c x)
  refine ⟨g, ?_⟩
  ext v
  rfl

end Cvt

section Beta

theorem mem_permCore_of_mem_U0 (w : ↥(U0 8)) : (w : U 8).val ∈ permCore 8 := by
  have h1 : wt 8 (w : U 8) = 1 := w.2
  have h2 : wt 8 (w : U 8) = Multiplicative.ofAdd (∑ i, (w : U 8).val i) := rfl
  rw [h2] at h1
  exact ofAdd_eq_one.1 h1

@[expose] noncomputable def betaHom : ↥(U0 8) →* Multiplicative p4insporth_V8 where
  toFun w := Multiplicative.ofAdd
    (Submodule.Quotient.mk (⟨(w : U 8).val, mem_permCore_of_mem_U0 w⟩ : ↥(permCore 8)))
  map_one' := rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (Submodule.Quotient.mk
      (⟨((a * b : ↥(U0 8)) : U 8).val, _⟩ : ↥(permCore 8))) = _
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
    rfl

theorem betaHom_apply (w : ↥(U0 8)) :
    betaHom w = Multiplicative.ofAdd
      (Submodule.Quotient.mk (⟨(w : U 8).val, mem_permCore_of_mem_U0 w⟩ : ↥(permCore 8))) := rfl

theorem betaHom_apply' (w : ↥(Mod.W 8 Mod.ut0)) :
    betaHom w = Multiplicative.ofAdd
      (Submodule.Quotient.mk (⟨(w : U 8).val, mem_permCore_of_mem_U0 w⟩ : ↥(permCore 8))) := rfl

theorem betaHom_surjective : Function.Surjective betaHom := by
  intro y
  induction y using Multiplicative.rec with
  | ofAdd y =>
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      refine ⟨⟨(⟨x.1⟩ : U 8), ?_⟩, ?_⟩
      · show wt 8 (⟨x.1⟩ : U 8) = 1
        have h1 : wt 8 (⟨x.1⟩ : U 8) = Multiplicative.ofAdd (∑ i, x.1 i) := rfl
        rw [h1]
        have : ∑ i, x.1 i = 0 := x.2
        rw [this]
        rfl
      · rfl

theorem mem_Esub_iff (w : U 8) : w ∈ Esub 8 ↔ w = 1 ∨ w = eVec 8 := by
  unfold Esub
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, zpow_two, eVec_mul_self, one_zpow]
    · right
      rw [hm, zpow_add_one, zpow_mul, zpow_two, eVec_mul_self, one_zpow, one_mul]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem betaHom_eq_one_iff (w : ↥(U0 8)) :
    betaHom w = 1 ↔ w ∈ (Esub 8).subgroupOf (U0 8) := by
  rw [Subgroup.mem_subgroupOf, mem_Esub_iff]
  have h1 : betaHom w = 1 ↔ (Submodule.Quotient.mk
      (⟨(w : U 8).val, mem_permCore_of_mem_U0 w⟩ : ↥(permCore 8)) : p4insporth_V8) = 0 := by
    rw [betaHom_apply]
    exact ofAdd_eq_one
  rw [h1]
  have h2 := p4insporth_ker8 ⟨(w : U 8).val, mem_permCore_of_mem_U0 w⟩
  rw [Submodule.mkQ_apply] at h2
  rw [h2]
  constructor
  · rintro (h | ⟨-, h⟩)
    · left
      apply U.ext
      intro i
      have := congrArg (fun x : ↥(permCore 8) => (x : Fin 8 → ZMod 2) i) h
      simpa using this
    · right
      apply U.ext
      intro i
      exact h i
  · rintro (h | h)
    · left
      apply Subtype.ext
      funext i
      have := congrArg (fun x : U 8 => x.val i) h
      simpa using this
    · right
      refine ⟨by decide, fun i => ?_⟩
      have := congrArg (fun x : U 8 => x.val i) h
      simpa [eVec] using this

theorem ker_betaHom : betaHom.ker = (Esub 8).subgroupOf (U0 8) := by
  ext w
  rw [MonoidHom.mem_ker]
  exact betaHom_eq_one_iff w

@[expose] noncomputable def betaEquiv : Mod.V 8 Mod.ut0 ≃* Multiplicative p4insporth_V8 :=
  (QuotientGroup.quotientMulEquivOfEq ker_betaHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective betaHom betaHom_surjective)

theorem betaEquiv_mk (w : ↥(Mod.W 8 Mod.ut0)) :
    betaEquiv (QuotientGroup.mk w : Mod.V 8 Mod.ut0) = betaHom w := rfl

theorem betaEquiv_act (σ : Equiv.Perm (Fin 8)) (x : Mod.V 8 Mod.ut0) :
    betaEquiv (Mod.act 8 Mod.ut0 σ x) = cvt (p4insporth_perm8Hom σ) (betaEquiv x) := by
  induction x using QuotientGroup.induction_on with
  | H w =>
    rw [act_mk, betaEquiv_mk, betaEquiv_mk, betaHom_apply', betaHom_apply', cvt_apply,
      toAdd_ofAdd, p4insporth_perm8Hom_mk]
    rfl

end Beta

section Main

variable {W : Type} [CommGroup W] [Finite W]

theorem congrHom_apply' {V V' : Type} [CommGroup V] [CommGroup V'] (e : V ≃* V') (g : MulAut V)
    (v : V') : H.congrHom e g v = e (g (e.symm v)) := rfl

theorem exists_model_mulEquiv (hW : ∀ w : W, w ^ 2 = 1) (q : W → ZMod 2)
    (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q) (E : Subgroup W)
    (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0) (hcard : Nat.card W = 2 ^ 6) :
    ∃ ε : W ≃* Mod.V 8 Mod.ut0,
      (orthogonalGroupOf q).map (H.congrHom ε) = (Mod.act 8 Mod.ut0).range := by
  obtain ⟨ε₁, hε₁⟩ := exists_isometry_model hW q hq hnd E hE hEq hcard
  refine ⟨ε₁.trans betaEquiv.symm, ?_⟩
  ext y
  rw [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    set φ : MulAut (Multiplicative p4insporth_V8) := H.congrHom ε₁ g with hφ
    have hφq : ∀ v, p4insporth_q8 (Multiplicative.toAdd (φ v)) = p4insporth_q8 (Multiplicative.toAdd v) := by
      intro v
      rw [hφ, congrHom_apply', hε₁, hg, ← hε₁, MulEquiv.apply_symm_apply]
    obtain ⟨l, hl⟩ := cvt_surjective φ
    have hlo : l ∈ orthSub p4insporth_q8 := by
      intro x
      have := hφq (Multiplicative.ofAdd x)
      rw [← hl, cvt_apply] at this
      simpa using this
    rw [← p4insporth_range_perm8] at hlo
    obtain ⟨σ, hσ⟩ := hlo
    refine ⟨σ, ?_⟩
    ext x
    have h1 : H.congrHom (ε₁.trans betaEquiv.symm) g = H.congrHom betaEquiv.symm φ := by
      ext z
      simp [hφ]
    rw [h1]
    apply betaEquiv.injective
    rw [betaEquiv_act]
    simp only [congrHom_apply', MulEquiv.apply_symm_apply]
    rw [← hl, ← hσ]
    rfl
  · rintro ⟨σ, rfl⟩
    have hε : ∀ w, betaEquiv ((ε₁.trans betaEquiv.symm) w) = ε₁ w := by
      intro w
      simp
    refine ⟨H.congrHom (ε₁.trans betaEquiv.symm).symm (Mod.act 8 Mod.ut0 σ), ?_, ?_⟩
    · intro w
      rw [← hε₁]
      have h1 : ε₁ (H.congrHom (ε₁.trans betaEquiv.symm).symm (Mod.act 8 Mod.ut0 σ) w) =
          cvt (p4insporth_perm8Hom σ) (ε₁ w) := by
        rw [congrHom_apply', MulEquiv.symm_symm]
        have h2 : ε₁ ((ε₁.trans betaEquiv.symm).symm
            (Mod.act 8 Mod.ut0 σ ((ε₁.trans betaEquiv.symm) w))) =
            betaEquiv (Mod.act 8 Mod.ut0 σ ((ε₁.trans betaEquiv.symm) w)) := by
          simp
        rw [h2, betaEquiv_act, hε]
      rw [h1, cvt_apply, toAdd_ofAdd, p4insporth_q8_perm, hε₁]
    · ext z
      simp

end Main

end CFSG.Quasithin.A38c5
