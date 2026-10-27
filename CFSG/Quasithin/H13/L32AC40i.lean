module

public import CFSG.Quasithin.H13.L32AC40h
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.Quasithin.Background.InternalSecBasic
public import CFSG.Quasithin.H13.L32A768b

public section

namespace CFSG.Quasithin.H13.L32A.C.A5Mod

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Layer
open CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup
open CFSG.Quasithin.RuType
open scoped MatrixGroups LinearAlgebra.Projectivization

theorem card_sl24 : Nat.card SL(2, F4) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide

variable {U : Type} [CommGroup U] [Finite U]

theorem exists_natural_of_fixed (hU2 : ∀ u : U, u * u = 1) {X : Subgroup (MulAut U)}
    (e : ↥X ≃* SL(2, F4)) (hcomm : XMod.commOf ↥X (⊤ : Subgroup U) = ⊤)
    (hirr : XMod.IsIrrSec ↥X (XMod.fixed ↥X (⊤ : Subgroup U)) ⊤)
    (hXC : X ≤ stabSub (XMod.fixed ↥X (⊤ : Subgroup U)))
    {P : Subgroup (MulAut U)} (hPX : P ≤ X) (hP4 : Nat.card P = 4)
    {D : Subgroup U} (hD4 : Nat.card D = 4) (hDC : D ⊓ XMod.fixed ↥X ⊤ = ⊥)
    (hPD : ∀ p ∈ P, ∀ d ∈ D, p d = d) :
    ∃ φ : Sec (⊤ : Subgroup U) (XMod.fixed ↥X ⊤) ≃* Multiplicative (Fin 2 → F4),
      ∀ (x : ↥X) (q : Sec (⊤ : Subgroup U) (XMod.fixed ↥X ⊤)),
        φ (B5.secHom X (InternalSec.le_stabSub_top X) hXC x q) =
          Multiplicative.ofAdd (((e x : SL(2, F4)) : Matrix (Fin 2) (Fin 2) F4).mulVec
            (Multiplicative.toAdd (φ q))) := by
  classical
  set C := XMod.fixed ↥X (⊤ : Subgroup U) with hC
  have hXW : X ≤ stabSub (⊤ : Subgroup U) := InternalSec.le_stabSub_top X
  set σ := B5.secHom X hXW hXC with hσ
  have : IsSimpleGroup SL(2, F4) := L32A.isSimpleGroup_sl24
  have : IsSimpleGroup ↥X := e.isSimpleGroup
  have hker : σ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with h | h
    · exact h
    · exfalso
      have hle : XMod.commOf ↥X (⊤ : Subgroup U) ≤ C := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨a, w, -, rfl⟩
        have ha : a ∈ σ.ker := by rw [h]; exact Subgroup.mem_top a
        rw [B5.mem_ker_secHom] at ha
        exact ha.2 w trivial
      rw [hcomm] at hle
      exact (ne_of_lt hirr.1) (le_antisymm le_top hle)
  have hfaith : X ⊓ centSec (⊤ : Subgroup U) C = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgX, hgc⟩
    have : (⟨g, hgX⟩ : ↥X) ∈ σ.ker := (B5.mem_ker_secHom X hXW hXC _).mpr hgc
    rw [hker, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  let eΓ : ↥X ≃* ↥(autSec X ⊤ C) := B5.secEquiv X hXW hXC hfaith
  let θL : ↥(autSec X ⊤ C) ≃* SL(2, F4) := eΓ.symm.trans e
  have hθL : ∀ x : ↥X, θL (eΓ x) = e x := fun x => by simp [θL]
  have hirrΓ : XMod.IsIrrSec ↥(autSec X ⊤ C) (⊥ : Subgroup (Sec (⊤ : Subgroup U) C)) ⊤ :=
    B5.isIrrSec_autSec hirr.1 (fun J hJ hCJ hJW => hirr.2 J (fun a w hw => hJ a a.2 w hw) hCJ hJW)
      hXW hXC
  have hS2 : ∀ q : Sec (⊤ : Subgroup U) C, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, show w * w = 1 from Subtype.ext (hU2 w), QuotientGroup.mk_one]
  obtain ⟨W', _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hS2
  set ρ := B45L2.repOf θ θL with hρdef
  have hρirr := B45L2.repOf_isIrreducible θ θL hirrΓ
  have hρ : ∀ (x : ↥X) (q : Sec (⊤ : Subgroup U) C),
      Multiplicative.toAdd (θ (σ x q)) = ρ (e x) (Multiplicative.toAdd (θ q)) := by
    intro x q
    have h1 := B45L2.toAdd_act θ θL (eΓ x) q
    rw [hθL] at h1
    rw [← h1]
    rfl
  have : Fintype (ℙ F4 (Fin 2 → F4)) := Fintype.ofFinite _
  obtain ⟨hcases, -⟩ := irreducible_binary_SL2_four_module_production F4.card ρ hρirr
  rcases hcases with ⟨φ, hφ⟩ | ⟨φ₀, hφ₀⟩ | ⟨φ', hφ'⟩
  ·
    exfalso
    have hall : ∀ g : SL(2, F4), g = 1 := by
      intro g
      apply B45L2.repOf_injective θ θL
      rw [map_one]
      exact LinearMap.ext fun w => φ.injective (by rw [hφ]; rfl)
    have h1 := hall (uElt 1)
    exact absurd (uElt_injective (h1.trans (by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> rfl) : uElt (1 : F4) = uElt 0)) (by decide)
  ·
    refine ⟨θ.trans (AddEquiv.toMultiplicative φ₀), fun x q => ?_⟩
    show Multiplicative.ofAdd (φ₀ (Multiplicative.toAdd (θ (σ x q)))) = _
    rw [hρ, hφ₀]
    rfl
  ·
    exfalso
    set P' := (P.subgroupOf X).map e.toMonoidHom with hP'
    have hP'4 : Nat.card P' = 4 := by
      rw [hP', Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hP4]
    have h2 := card_fix_le_two F4.card card_sl24 hP'4
    let f : ↥D → {w : ↥(evenWeight (ℙ F4 (Fin 2 → F4))) // ∀ g ∈ P',
        SL2Modules.permAct (MulAction.toPerm g) (w : ℙ F4 (Fin 2 → F4) → ZMod 2) = w} := fun d =>
      ⟨φ' (Multiplicative.toAdd (θ (QuotientGroup.mk ⟨(d : U), Subgroup.mem_top _⟩))), by
        rintro _ ⟨p, hp, rfl⟩
        refine (hφ' _ _).symm.trans ?_
        rw [MulEquiv.coe_toMonoidHom, ← hρ]
        congr 3
        rw [hσ, B5.secHom_mk]
        congr 2
        exact Subtype.ext (hPD p (Subgroup.mem_subgroupOf.mp hp) d d.2)⟩
    have hf : Function.Injective f := by
      intro d₁ d₂ h
      have h1 := congrArg (fun z => (z.1 : ↥(evenWeight (ℙ F4 (Fin 2 → F4))))) h
      have h2 := Multiplicative.toAdd.injective (φ'.injective h1)
      have h3 := θ.injective (Multiplicative.toAdd.injective h2)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h3
      have h4 : (d₁ : U)⁻¹ * (d₂ : U) ∈ D ⊓ C :=
        ⟨D.mul_mem (D.inv_mem d₁.2) d₂.2, by simpa using h3⟩
      rw [hDC, Subgroup.mem_bot, inv_mul_eq_one] at h4
      exact Subtype.ext h4
    have := Nat.card_le_card_of_injective f hf
    omega

end CFSG.Quasithin.H13.L32A.C.A5Mod
