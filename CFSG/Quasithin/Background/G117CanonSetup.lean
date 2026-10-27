module

public import CFSG.Quasithin.Background.G117CanonDefs
public import CFSG.Quasithin.Background.G117Setup
public import CFSG.Quasithin.Background.G118Hyp
public import CFSG.Quasithin.Background.G93ApplyStmt
public import CFSG.Quasithin.Background.SzG11SConf

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Quasithin.G11.SzG11S

abbrev ConclPred : Type 1 :=
  ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V],
    LinearMap.BilinForm (ZMod 2) V → Subgroup (GLV V) → Subgroup (GLV V) → Prop

structure QSetup (Q : ConclPred) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  conf : Conf B Γ v₁ W X X₀ L
  notConcl : ¬ Q B Γ X

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure QCtx (Q : ConclPred) (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V))
    (v₁ : V) (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (m : ℕ) : Prop where
  setup : QSetup Q B Γ v₁ W X X₀ L
  props : G116Props B Γ v₁ X L I
  faithful : FaithfulOn X I
  card : Nat.card X = 2 ^ m

namespace QCtx

variable {Q : ConclPred} {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {m : ℕ}
  (c : QCtx Q B Γ v₁ W X X₀ L I m)

include c

theorem h108 : G108Hyp B Γ v₁ W X X₀ L := c.setup.conf.h108

theorem invariantH : Invariant (normalClosure Γ L) I := c.props.1.1

theorem invariantX : Invariant X I := props_invariantX c.props

theorem invariantK : Invariant (normalClosure Γ L ⊔ X) I :=
  c.invariantH.sup_subgroup c.invariantX

theorem isIrr : IsIrr (normalClosure Γ L) I :=
  (props_irrPlus c.props).isIrr c.h108.fixedSpace_H

theorem finrank_V_le : Module.finrank (ZMod 2) V ≤ 2 * (m + 1) := by
  have h := c.h108.toG101Hyp.dim_le_two_mul
  have hdvd : X₀.relIndex X ∣ 2 ^ m := by
    rw [← c.card]
    exact Subgroup.relIndex_dvd_card X₀ X
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hlog : Nat.log 2 (X₀.relIndex X) ≤ m := by
    rw [hjeq, Nat.log_pow Nat.one_lt_two]
    exact hj
  omega

theorem finrank_I_le : Module.finrank (ZMod 2) ↥I ≤ 2 * (m + 1) :=
  (Submodule.finrank_le I).trans c.finrank_V_le

theorem two_mul_finrank_le (hne : I ≠ ⊤) :
    2 * Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V := by
  have h108 := c.h108
  obtain ⟨U', hU'inv, hcompl⟩ := exists_invariant_compl h108.sSup_isIrr c.invariantH
  have hU'ne : U' ≠ ⊥ := by
    intro h
    rw [h] at hcompl
    apply hne
    simpa using hcompl.sup_eq_top
  obtain ⟨J, hJU, hJirr⟩ := exists_isIrr_le hU'inv hU'ne
  have hJplus : IrrPlus (normalClosure Γ L) J := hJirr.irrPlus h108.fixedSpace_H
  obtain ⟨φ, -⟩ := props_homogeneous c.props I J (props_irrPlus c.props) hJplus
  have h1 : Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) ↥J := LinearEquiv.finrank_eq φ
  have h2 : Module.finrank (ZMod 2) ↥J ≤ Module.finrank (ZMod 2) ↥U' := Submodule.finrank_mono hJU
  have h3 := Submodule.finrank_add_eq_of_isCompl hcompl
  omega

theorem g93 (hApply : G93ApplyStmt) :
    G93ConclDimensionOnly (restrictRange (normalClosure Γ L ⊔ X) I c.invariantK)
      (restrictRange (normalClosure Γ L) I c.invariantH) m := by
  have h108 := c.h108
  have hHΓ : normalClosure Γ L ≤ Γ := h108.H_le
  refine hApply V Γ (normalClosure Γ L ⊔ X) (normalClosure Γ L) L X I m c.invariantK c.invariantH
    c.setup.conf.sqtk (sup_le hHΓ h108.X_le) le_sup_left (fun k hk h hh => ?_) c.isIrr
    (props_faithful c.props) le_sup_right h108.toG101Hyp.X_isElemAbelian c.card c.faithful
    c.finrank_I_le h108.component (le_normalClosure Γ L) h108.noncomm
    (g118_hEq h108.component c.setup.conf.numConj h108.fixedSpace_H (props_homogeneous c.props)
      (props_irrPlus c.props) (props_faithful c.props))
  exact normalClosure_normal Γ L k ((sup_le hHΓ h108.X_le : normalClosure Γ L ⊔ X ≤ Γ) hk) h hh

end QCtx

structure QContains (Q : ConclPred) : Prop where
  c2 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card ↥Γ ∨ 18 ∣ Nat.card ↥Γ)) → Q B Γ X
  c4 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), G112Concl4 Γ → Q B Γ X
  c5 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), G112Concl5 B Γ → Q B Γ X
  c6 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))) →
      Q B Γ X
  c6' : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 6 ∧
      IsG2NaturalModule Γ ⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆) →
      Q B Γ X
  c7 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 8 ∧
      IsNaturalMatrixModule ((genFittingFStar ↥Γ).map Γ.subtype)
        (CFSG.Assembly.LowTwoRank.StatedOmega
          (CFSG.Assembly.LowTwoRank.StatedQuadPlus 2 (GaloisField 2 2))) ∧
      ¬ X ≤ (genFittingFStar ↥Γ).map Γ.subtype) → Q B Γ X
  c10 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), IsG112Ten Γ X → Q B Γ X
  c11 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 8 ∧
      IsL28TwistedTensorModule ((genFittingFStar ↥Γ).map Γ.subtype)) → Q B Γ X
  c13 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)),
    (Module.finrank (ZMod 2) V = 12 ∧
      ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22) →
      Q B Γ X

end Canon

end G11

end CFSG.Quasithin
