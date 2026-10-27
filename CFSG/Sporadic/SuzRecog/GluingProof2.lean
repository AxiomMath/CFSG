module

public import CFSG.Sporadic.SuzRecog.GluingProof
public import CFSG.Sporadic.SuzRecog.ChartGluing

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81 TitsTwo

@[expose] noncomputable def B0Plus : Subgroup (Equiv.Perm (Fin 1782)) :=
  Model.B0 ⊓ (Subgroup.centralizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) ⊔
    Subgroup.zpowers Model.rho1)

section Agree

variable {G : Type} [Group G] {M : Subgroup G}

@[expose] def B0PlusAgree (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) : Prop :=
  ∀ x ∈ B0Plus, ∀ (hx : x ∈ invE 1) (hxN : x ∈ Model.NR0), ψ ⟨x, hxN⟩ = (σ.symm ⟨x, hx⟩ : G)

@[expose] def B0TwistAgree (σ : M ≃* invE 1) (ψ : Model.NR0 →* G) : Prop :=
  B0PlusAgree σ ψ ∧ ∀ x (hxN : x ∈ Model.NR0), x ∈ invE 1 → x ∉ B0Plus →
    ∀ hxt : x * suzInv 1 ∈ invE 1, ψ ⟨x, hxN⟩ = (σ.symm ⟨x * suzInv 1, hxt⟩ : G)

theorem B0Agree.plus {σ : M ≃* invE 1} {ψ : Model.NR0 →* G} (h : B0Agree σ ψ) :
    B0PlusAgree σ ψ := fun x _ hx hxN => h x hx hxN

end Agree

section Cover

variable {F : Type*} [Group F] {V : Type*} [MulAction F V] {Γ : SimpleGraph V}
  {T : Set V → Prop} {ι κ : Type*}

@[expose] def MixedCellDichotomy (D : TitsDataTwo Γ T F ι κ) (π : F →* Model.Crho1)
    (w : Equiv.Perm (Fin 1782)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    SuzLeafHyp S → ∀ (σ : S.M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ₀ : centM w →* G),
    B0Agree σ ψ → ChartAgree σ ζ₀ → ∃ (σ' : S.M ≃* invE 1) (ζ : centM w →* G),
      (B0Agree σ' ψ ∨ B0TwistAgree σ' ψ) ∧ ChartAgree σ' ζ ∧ CellRel D π σ' ψ ζ

@[expose] def RootTwistTrivial' (D : TitsDataTwo Γ T F ι κ) (π : F →* Model.Crho1) (d : F)
    (w : Equiv.Perm (Fin 1782)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    SuzLeafHyp S → ∀ (σ : S.M ≃* invE 1) (ψ : Model.NR0 →* G) (ζ : centM w →* G),
    B0PlusAgree σ ψ → ChartAgree σ ζ → CellRel D π σ ψ ζ → ∀ Φ : F →* G,
    (∀ x ∈ D.Xp, ∀ h : (π x : Equiv.Perm (Fin 1782)) ∈ invE 1, Φ x = (σ.symm ⟨_, h⟩ : G)) →
    (∀ x ∈ D.Xq, ∀ h : (π x : Equiv.Perm (Fin 1782)) ∈ Model.NR0, Φ x = ψ ⟨_, h⟩) →
    (∀ x ∈ D.Xe, ∀ h : (π x : Equiv.Perm (Fin 1782)) ∈ centM w, Φ x = ζ ⟨_, h⟩) → Φ d = 1

end Cover

@[expose] def B0TwistExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    SuzLeafHyp S → ∀ (σ : S.M ≃* invE 1) (ψ : Model.NR0 →* G) (Φ₂ : Model.Crho1 →* G),
    B0TwistAgree σ ψ →
    (∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G)) →
    (∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩) → False

section Cover2

variable {F : Type*} [Group F] {V : Type*} [MulAction F V] {Γ : SimpleGraph V}
  {T : Set V → Prop} {ι κ : Type*}

theorem suzLevelTwoGluing_of_cover₂ [IsEmpty ι] (D : TitsDataTwo Γ T F ι κ)
    (π : F →* Model.Crho1) (hsurj : Function.Surjective π) (d : F) (hker : π.ker = zpowers d)
    (hp : ∀ x ∈ D.Xp, (π x : Equiv.Perm (Fin 1782)) ∈ invE 1)
    (hp' : ∀ y (hy : y ∈ Model.Crho1), y ∈ invE 1 → ∃ x ∈ D.Xp, π x = ⟨y, hy⟩)
    (hq : ∀ x ∈ D.Xq, (π x : Equiv.Perm (Fin 1782)) ∈ Model.NR0)
    (hq' : ∀ y (hy : y ∈ Model.Crho1), y ∈ Model.NR0 → ∃ x ∈ D.Xq, π x = ⟨y, hy⟩)
    (hplus : ∀ x ∈ D.Xp, x ∈ D.Xq → (π x : Equiv.Perm (Fin 1782)) ∈ B0Plus)
    {w : Equiv.Perm (Fin 1782)} (he : ∀ x ∈ D.Xe, (π x : Equiv.Perm (Fin 1782)) ∈ centM w)
    (hG4 : SuzB0Gluing) (hchart : SuzChartTransfer w) (hdich : MixedCellDichotomy D π w)
    (hroot : RootTwistTrivial' D π d w) (hex : B0TwistExcluded) : SuzLevelTwoGluing := by
  intro G _ _ _ S hw hE hΩ hNWC hL34 hσ
  have hS : SuzLeafHyp S := ⟨hw, hE, hΩ, hNWC, hL34⟩
  obtain ⟨σ₀, ψ, hB₀⟩ := hG4 G S hS hσ
  obtain ⟨ζ₀, hζ₀⟩ := hchart G S hS σ₀
  obtain ⟨σ, ζ, hor, hζ, hcell⟩ := hdich G S hS σ₀ ψ ζ₀ hB₀ hζ₀
  have hBp : B0PlusAgree σ ψ := hor.elim B0Agree.plus And.left
  let φp : D.Xp →* G := (S.M.subtype.comp σ.symm.toMonoidHom).comp
    (((Model.Crho1.subtype.comp π).comp D.Xp.subtype).codRestrict (invE 1) fun x => hp x x.2)
  let φq : D.Xq →* G := ψ.comp
    (((Model.Crho1.subtype.comp π).comp D.Xq.subtype).codRestrict Model.NR0 fun x => hq x x.2)
  let φe : D.Xe →* G := ζ.comp
    (((Model.Crho1.subtype.comp π).comp D.Xe.subtype).codRestrict (centM w) fun x => he x x.2)
  obtain ⟨Φ, ⟨hΦp, hΦq, hΦe, -⟩, -⟩ := D.existsUnique_hom φp φq φe (fun j => isEmptyElim j)
    (fun a ha hb => (hBp _ (hplus a ha hb) (hp a ha) (hq a hb)).symm)
    (fun a ha hb => (hζ _ (hp a ha) (he a hb)).symm)
    (fun j => isEmptyElim j) (fun j => isEmptyElim j)
    (fun k => hcell k (hq _ (D.cell_mem k)) (hp _ (D.hc k)) (he _ D.s_mem) (hp _ (D.hc' k)))
  have hd : Φ d = 1 := hroot G S hS σ ψ ζ hBp hζ hcell Φ
    (fun x hx _ => hΦp ⟨x, hx⟩) (fun x hx _ => hΦq ⟨x, hx⟩) (fun x hx _ => hΦe ⟨x, hx⟩)
  have hle : π.ker ≤ Φ.ker := by
    rw [hker, zpowers_le]
    exact hd
  let e := QuotientGroup.quotientKerEquivOfSurjective π hsurj
  let Φ₂ : Model.Crho1 →* G := (QuotientGroup.lift π.ker Φ hle).comp e.symm.toMonoidHom
  have hΦ₂ : ∀ x : F, Φ₂ (π x) = Φ x := fun x => by
    have h₁ : e.symm (π x) = (x : F ⧸ π.ker) := (MulEquiv.symm_apply_eq e).2 rfl
    change QuotientGroup.lift π.ker Φ hle (e.symm (π x)) = Φ x
    rw [h₁, QuotientGroup.lift_mk]
  have hA : ∀ x (hx : x ∈ invE 1) (hxC : x ∈ Model.Crho1),
      Φ₂ ⟨x, hxC⟩ = (σ.symm ⟨x, hx⟩ : G) := by
    intro x hx hxC
    obtain ⟨y, hy, hyx⟩ := hp' x hxC hx
    have h0 : (π y : Equiv.Perm (Fin 1782)) = x := congrArg Subtype.val hyx
    have hyx' : (⟨_, hp y hy⟩ : ↥(invE 1)) = ⟨x, hx⟩ := Subtype.ext h0
    rw [← hyx, hΦ₂, ← hyx']
    exact hΦp ⟨y, hy⟩
  have hB : ∀ x (hxN : x ∈ Model.NR0) (hxC : x ∈ Model.Crho1), Φ₂ ⟨x, hxC⟩ = ψ ⟨x, hxN⟩ := by
    intro x hxN hxC
    obtain ⟨y, hy, hyx⟩ := hq' x hxC hxN
    have h0 : (π y : Equiv.Perm (Fin 1782)) = x := congrArg Subtype.val hyx
    have hyx' : (⟨_, hq y hy⟩ : ↥Model.NR0) = ⟨x, hxN⟩ := Subtype.ext h0
    rw [← hyx, hΦ₂, ← hyx']
    exact hΦq ⟨y, hy⟩
  rcases hor with hgood | hbad
  · exact ⟨σ, ψ, Φ₂, hgood, hA, hB⟩
  · exact (hex G S hS σ ψ Φ₂ hbad hA hB).elim

end Cover2

end CFSG.Sporadic.SuzRecog
