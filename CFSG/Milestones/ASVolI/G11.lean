module

public import CFSG.Milestones.ASVolI.G9
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Fifteen
public import CFSG.Quasithin.Background.G116II
public import CFSG.Quasithin.Background.G116III
public import CFSG.Quasithin.Background.G12Four
public import CFSG.Quasithin.Background.G12FourB
public import CFSG.Quasithin.Background.G12Main
public import CFSG.Quasithin.Background.P4GLMain
public import CFSG.Quasithin.Background.P4InspectFinal
public import CFSG.Quasithin.Background.P4SL34
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.SzG11B49Main
public import CFSG.Quasithin.Background.G117CanonFinal
import CFSG.Quasithin.Background.SzG11G94Final
import CFSG.Quasithin.Background.G118CanonFinal
import CFSG.Quasithin.Background.G118CanonNineF4
import CFSG.Quasithin.Background.SzG11G64Nat
import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
import CFSG.Milestones.ASVolI.G10
import CFSG.Quasithin.Background.SzG11B5b2
import CFSG.Quasithin.Background.SzG11B5c
import CFSG.Quasithin.Background.G119Fix
import CFSG.Quasithin.Background.G119Index
import CFSG.Quasithin.Background.G119Transv

public section

namespace CFSG.ASVolI.ChG

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsTensorD3Core5 (Γ₀ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ₀ ≃* (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 5))))
    (ψ : V ≃ₗ[ZMod 2] (↥(permCore 3) ⊗[ZMod 2] ↥(permCore 5))),
    ∀ (γ : ↥Γ₀) (a a' : ↥(permCore 3)) (b b' : ↥(permCore 5)),
      (a' : Fin 3 → ZMod 2) = permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      (b' : Fin 5 → ZMod 2) = permAct ((φ γ).2 : Equiv.Perm (Fin 5)) (b : Fin 5 → ZMod 2) →
        ψ ((γ : GLV V) (ψ.symm (a ⊗ₜ b))) = a' ⊗ₜ b'

@[expose] def IsTensorD3Nat24 (Γ₀ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ₀ ≃* (Equiv.Perm (Fin 3) × ↥(StatedSL 2 (GaloisField 2 2))))
    (ψ : V ≃ₗ[ZMod 2] (↥(permCore 3) ⊗[ZMod 2] (Fin 2 → GaloisField 2 2))),
    ∀ (γ : ↥Γ₀) (a a' : ↥(permCore 3)) (b b' : Fin 2 → GaloisField 2 2),
      (a' : Fin 3 → ZMod 2) = permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      b' = ((((φ γ).2 : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec b →
        ψ ((γ : GLV V) (ψ.symm (a ⊗ₜ b))) = a' ⊗ₜ b'

@[expose] def IsG112NinePartial (Γ : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    (Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ∨
      Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 5))))) ∧
    ∃ Γ₀ : Subgroup (GLV V), Γ₀ ≤ Γ ∧ Γ₀.relIndex Γ ≤ 2 ∧ (IsTensorD3Core5 Γ₀ ∨ IsTensorD3Nat24 Γ₀)

@[expose] def IsTensorD3Perm5 (Γ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)))
    (ψ : V ≃ₗ[ZMod 2] (↥(permCore 3) ⊗[ZMod 2] ↥(permCore 5))),
    ∀ (γ : ↥Γ) (first first' : ↥(permCore 3)) (second second' : ↥(permCore 5)),
      (first' : Fin 3 → ZMod 2) = permAct (φ γ).1 (first : Fin 3 → ZMod 2) →
      (second' : Fin 5 → ZMod 2) = permAct (φ γ).2 (second : Fin 5 → ZMod 2) →
        ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ second'

@[expose] def IsTensorD3Semilin24 (Γ : Subgroup (GLV V)) : Prop :=
  ∃ ψ : V ≃ₗ[ZMod 2] (↥(permCore 3) ⊗[ZMod 2] (Fin 2 → GaloisField 2 2)),
    (∀ γ : ↥Γ, ∃ (σ : Equiv.Perm (Fin 3))
      (matrix : ↥(StatedSL 2 (GaloisField 2 2))) (twisted : Bool),
      ∀ (first first' : ↥(permCore 3)) (second : Fin 2 → GaloisField 2 2),
        (first' : Fin 3 → ZMod 2) = permAct σ (first : Fin 3 → ZMod 2) →
          ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ
            ((((matrix : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec
                (fun coordinate => if twisted then second coordinate ^ 2 else second coordinate))) ∧
    (∀ (σ : Equiv.Perm (Fin 3)) (matrix : ↥(StatedSL 2 (GaloisField 2 2))) (twisted : Bool),
      ∃ γ : ↥Γ, ∀ (first first' : ↥(permCore 3)) (second : Fin 2 → GaloisField 2 2),
        (first' : Fin 3 → ZMod 2) = permAct σ (first : Fin 3 → ZMod 2) →
          ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ
            ((((matrix : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec
                (fun coordinate => if twisted then second coordinate ^ 2 else second coordinate)))

@[expose] def IsG112Nine (Γ : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ((Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ∧
      (IsTensorD3Perm5 Γ ∨ IsTensorD3Semilin24 Γ)) ∨
      IsTensorD3Core5 Γ ∨ IsTensorD3Nat24 Γ)

@[expose] def onesCore6 : ↥(permCore 6) :=
  ⟨fun _ => 1, by show (∑ _i : Fin 6, (1 : ZMod 2)) = 0; decide⟩

@[expose] def TensorA6Z3WithMarking (E P : Subgroup (GLV V))
    (φ : ↥E ≃* ↥(alternatingGroup (Fin 6))) : Prop :=
  ∃ (θ : ↥P ≃* (GaloisField 2 2)ˣ)
    (β : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V),
    Function.Surjective β ∧
    (∀ t, β t = 0 ↔ ∃ b : GaloisField 2 2, t = onesCore6 ⊗ₜ b) ∧
    (∀ (e : ↥E) (a a' : ↥(permCore 6)) (b : GaloisField 2 2),
      (a' : Fin 6 → ZMod 2) = permAct ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (a : Fin 6 → ZMod 2) → β (a' ⊗ₜ b) = (e : GLV V) (β (a ⊗ₜ b))) ∧
    (∀ (p : ↥P) (a : ↥(permCore 6)) (b : GaloisField 2 2),
      β (a ⊗ₜ (((θ p : (GaloisField 2 2)ˣ) : GaloisField 2 2) * b)) = (p : GLV V) (β (a ⊗ₜ b)))

@[expose] def IsTensorA6Z3 (E P : Subgroup (GLV V)) : Prop :=
  ∃ φ : ↥E ≃* ↥(alternatingGroup (Fin 6)), TensorA6Z3WithMarking E P φ

@[expose] def IsG112Ten (Γ X : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ∃ (E P : Subgroup (GLV V)) (x : GLV V),
      E = (genFittingLayer ↥Γ).map Γ.subtype ∧ P = (CFSG.pCore 3 ↥Γ).map Γ.subtype ∧
      Nat.card P = 3 ∧ E ⊓ P = ⊥ ∧ (∀ e ∈ E, ∀ p ∈ P, e * p = p * e) ∧
      (genFittingFStar ↥Γ).map Γ.subtype = E ⊔ P ∧
      x ∈ X ∧ x ∈ Γ ∧ Γ = (E ⊔ P) ⊔ Subgroup.zpowers x ∧ (∀ p ∈ P, x * p * x⁻¹ = p⁻¹) ∧
      (∃ (φ : ↥E ≃* ↥(alternatingGroup (Fin 6))) (τ : Equiv.Perm (Fin 6)),
        τ.IsSwap ∧ TensorA6Z3WithMarking E P φ ∧
        ∀ e e' : ↥E, x * (e : GLV V) * x⁻¹ = (e' : GLV V) →
          ((φ e' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
            τ * ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * τ⁻¹)

@[expose] def IsG112TenLegacy (Γ X : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ∃ (E P : Subgroup (GLV V)) (x : GLV V),
      E = (genFittingLayer ↥Γ).map Γ.subtype ∧ P = (CFSG.pCore 3 ↥Γ).map Γ.subtype ∧
      Nat.card P = 3 ∧ E ⊓ P = ⊥ ∧ (∀ e ∈ E, ∀ p ∈ P, e * p = p * e) ∧
      (genFittingFStar ↥Γ).map Γ.subtype = E ⊔ P ∧
      x ∈ X ∧ x ∈ Γ ∧ Γ = (E ⊔ P) ⊔ Subgroup.zpowers x ∧ (∀ p ∈ P, x * p * x⁻¹ = p⁻¹) ∧
      (∃ (φ : ↥E ≃* ↥(alternatingGroup (Fin 6))) (τ : Equiv.Perm (Fin 6)),
        τ.IsSwap ∧ ∀ e e' : ↥E, x * (e : GLV V) * x⁻¹ = (e' : GLV V) →
          ((φ e' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
            τ * ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * τ⁻¹) ∧
      IsTensorA6Z3 E P

@[expose] def fStarIn (Γ : Subgroup (GLV V)) : Subgroup (GLV V) :=
  (genFittingFStar ↥Γ).map Γ.subtype

@[expose] def G112Faithful (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) : Prop :=
  (Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))) ∨
  (Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card ↥Γ ∨ 18 ∣ Nat.card ↥Γ)) ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsSubSD16Heis Γ) ∨
  G112Concl4 Γ ∨
  G112Concl5 B Γ ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))) ∨
  (Module.finrank (ZMod 2) V = 8 ∧
    IsNaturalMatrixModule (fStarIn Γ) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) ∧
    ¬ X ≤ fStarIn Γ) ∨
  G112Concl8 B Γ X ∨ G112Concl8S8 B Γ X ∨
  IsG112Nine Γ ∨
  IsG112Ten Γ X ∨
  (Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule (fStarIn Γ)) ∨
  G112Concl12 Γ X ∨
  (Module.finrank (ZMod 2) V = 12 ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22)

@[expose] def G112FaithfulLegacy (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) : Prop :=
  (Module.finrank (ZMod 2) V = 2 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 3))) ∨
  (Module.finrank (ZMod 2) V = 4 ∧ (10 ∣ Nat.card ↥Γ ∨ 18 ∣ Nat.card ↥Γ)) ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsSubSD16Heis Γ) ∨
  G112Concl4 Γ ∨
  G112Concl5 B Γ ∨
  (Module.finrank (ZMod 2) V = 6 ∧ IsG2NaturalModule Γ (CFSG.Open.quasithinG2 (ZMod 2))) ∨
  (Module.finrank (ZMod 2) V = 8 ∧
    IsNaturalMatrixModule (fStarIn Γ) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) ∧
    ¬ X ≤ fStarIn Γ) ∨
  G112Concl8 B Γ X ∨ G112Concl8S8 B Γ X ∨
  IsG112NinePartial Γ ∨
  IsG112TenLegacy Γ X ∨
  (Module.finrank (ZMod 2) V = 8 ∧ IsL28TwistedTensorModule (fStarIn Γ)) ∨
  G112Concl12 Γ X ∨
  (Module.finrank (ZMod 2) V = 12 ∧
    ∃ N : Subgroup ↥Γ, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥CFSG.Blueprint.NativeSporadic.M22)

@[expose] def G112ProposedU33 (Γ : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧
    IsG2NaturalModule Γ ⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆

@[expose] def G112FaithfulWithU33 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (GLV V)) : Prop :=
  G112Faithful B Γ X ∨ G112ProposedU33 Γ

@[expose] def G112FaithfulLegacyWithU33 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ X : Subgroup (GLV V)) : Prop :=
  G112FaithfulLegacy B Γ X ∨ G112ProposedU33 Γ

section Counterexample

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure G11CxF (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  notConcl : ¬ G112FaithfulLegacyWithU33 B Γ X

structure G11SetupF (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  cx : G11CxF B Γ v₁ W X X₀
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

structure G11CanonicalCx (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  notConcl : ¬ G112FaithfulWithU33 B Γ X

structure G11CanonicalSetup (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  cx : G11CanonicalCx B Γ v₁ W X X₀
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

end Counterexample

end CFSG.ASVolI.ChG

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.G11 CFSG.ASVolI.ChG

@[expose] def G_11_2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112FaithfulWithU33 B Γ X

@[expose] def G_11_4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G11CxF B Γ v₁ W X X₀ → IsIrr Γ ⊤

theorem as_G_11_4 : G_11_4 := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have h4 := CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49
  have h5 : CFSG.Quasithin.G11.G1005Stmt := CFSG.Quasithin.g10_5 CFSG.Quasithin.G11.g10_3 h4
  rcases h5 V B Γ v₁ W X X₀ cx.hyp.toG101Hyp with h | ⟨hd, h18⟩
  · exact h
  · exact (cx.notConcl (Or.inl (Or.inr (Or.inl ⟨hd, Or.inr h18⟩)))).elim

@[expose] def G_11_5 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)), G11CxF B Γ v₁ W X X₀ →
      ∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x

theorem as_G_11_5 : G_11_5 := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have hirr : IsIrr Γ ⊤ := as_G_11_4 V B Γ v₁ W X X₀ cx
  by_contra hcon
  have hfaith : ∀ x ∈ X, (∀ f ∈ fittingOf Γ, x * f = f * x) → x = 1 := by
    intro x hx hc
    by_contra hx1
    exact hcon ⟨x, hx, hx1, hc⟩
  have h101 := cx.hyp.toG101Hyp
  obtain ⟨k, hk⟩ := h101.exists_card_X
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    have hX1 : ∀ x ∈ X, x = 1 := by
      intro x hx
      have hsub : Subsingleton ↥X := Nat.card_eq_one_iff_unique.1 hk |>.1
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥X) 1)
    rcases cx.hyp.three with h | ⟨a, ha, -, hv⟩
    ·
      obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h101.point (h101.nondegenerate v₁ hall)
      rcases h w (fun x hx => by rw [hX1 x hx]; rfl) with hw0 | hw1
      · exact hw (by rw [hw0, map_zero])
      · exact hw (by rw [hw1]; exact h101.alt v₁)
    · have : a = 1 := hX1 a ha
      subst this
      have : v₁ = 0 := by
        obtain ⟨u, hu⟩ := hv
        rw [← hu]
        simp
      exact h101.point this
  have hbound : Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by
    refine h101.dim_le_two_mul.trans (Nat.mul_le_mul_left 2 (Nat.succ_le_succ ?_))
    have hdvd : X₀.relIndex X ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.relIndex_dvd_card X₀ X
    calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 (2 ^ k) :=
          Nat.log_mono_right (Nat.le_of_dvd (by positivity) hdvd)
      _ = k := Nat.log_pow Nat.one_lt_two k
  have hyp94 : G94Hyp Γ X k :=
    { quotient := cx.sqtk
      A_le := h101.X_le
      A_elem := h101.X_isElemAbelian
      A_card := hk
      A_ne := hk1
      bound := hbound
      irreducible := hirr
      faithful := hfaith }
  have hconcl := (CFSG.Quasithin.SzG11.g94Stmt_proved V Γ X k hyp94).toG112
  rcases hconcl with h | h | h
  · exact cx.notConcl (Or.inl (Or.inl h))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inl h)))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inr (Or.inl h))))

@[expose] def G_11_6 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11SetupF B Γ v₁ W X X₀ L →
      Homogeneous (normalClosure Γ L) ∧
      ∃ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ∧ v₁ ∈ I ∧ Invariant X I ∧
        (∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J → J = I) ∧
        (I = ⊤ ∨ Isotropic B I) ∧ SelfDual (normalClosure Γ L) I ∧
        FaithfulOn (normalClosure Γ L) I ∧ ¬ AutAll (normalClosure Γ L) I

section G11_6

theorem as_G_11_6
    : G_11_6 := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs
  have h3 := CFSG.Quasithin.G11.g10_3
  have h4 := CFSG.Quasithin.g10_4 h3 CFSG.Quasithin.G11.SzG11S.b49
  have h10 := CFSG.Quasithin.G11.g10_10_of_g10_4 h4
  have h11 := CFSG.Quasithin.G11.g10_11 h10
  have h12 := CFSG.Quasithin.G11.g10_12 h11
  have h13 := CFSG.Quasithin.G11.g10_13 h10 h11
  have h1212 := CFSG.Quasithin.G11.g12_12_of_four
    (CFSG.Quasithin.G11.g12_1_of_four CFSG.Quasithin.G11.g12_four_fact)
    CFSG.Quasithin.G11.g12_part_four_fact
  have h15 : CFSG.Quasithin.G11.G1015Stmt :=
    CFSG.Quasithin.G11.g10_15 h10 h11 h12 h13 h1212 CFSG.Quasithin.G11.outerGLInput
      CFSG.Quasithin.G11.inspect_simple CFSG.Quasithin.G11.inspect_outer
      CFSG.Quasithin.G11.inspect_sylow
      (CFSG.Quasithin.SzG11.sectionSQTInput_of_asA21 CFSG.Quasithin.asA21SQTKSection)
  have hII : CFSG.Quasithin.G11.G116IIStmt :=
    CFSG.Quasithin.G11.g116_II CFSG.Quasithin.G11.Harris.g93StmtDimensionOnly_holds
      CFSG.Quasithin.G11.outerSL34Input
  have hIII : CFSG.Quasithin.G11.G116IIIStmt := CFSG.Quasithin.G11.g116_III
  have h108 := hs.h108
  have hirrH : ∀ I : Submodule (ZMod 2) V,
      IrrPlus (normalClosure Γ L) I → IsIrr (normalClosure Γ L) I :=
    fun I hI => hI.isIrr h108.fixedSpace_H
  have hG : ∃ I : Submodule (ZMod 2) V, CFSG.Quasithin.G11.G116Props B Γ v₁ X L I := by
    obtain ⟨I, hI, hone, htwo, hthree⟩ :=
      (CFSG.Quasithin.G11.G1015Concl_iff B Γ v₁ W X L).1 (h15 V B Γ v₁ W X X₀ L h108 hs.cx.sqtk)
    rcases htwo with h2I | h2II | h2III
    · have hone_i : CFSG.Quasithin.G11.G1015One_i B Γ v₁ W X L I := by
        rcases hone with h | ⟨x, hx, hxI, -, hno, -⟩
        · exact h
        · exfalso
          have hconj : IrrPlus (normalClosure Γ L) (conjSub x I) :=
            ((hirrH I hI).conj_of_normal (normalClosure_normal Γ L) (h108.X_le hx)).irrPlus
              h108.fixedSpace_H
          exact hno (h2I.1 I (conjSub x I) hI hconj)
      have hnot : ¬ AutAll (normalClosure Γ L) I :=
        CFSG.Quasithin.G11.not_autAll_of_selfDual (h108.two_lt_finrank (hirrH I hI)) h2I.2.1
      refine ⟨I, hI, hone_i.2.2.1, hone_i.2.1, hone_i.2.2.2, hone_i.1, ?_, h2I.2.1, h2I.2.2.1,
        hnot⟩
      rcases h2I.2.2.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2II.1
        · exact h
      rcases hII V B Γ v₁ W X X₀ L h108 hs.numConj hs.cx.sqtk I hI hone_ii h2II hthree with
        h | h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2III.1
        · exact h
      have h12' := hIII V B Γ v₁ W X X₀ L h108 hs.cx.sqtk I hI hone_ii h2III hthree
      exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h12'
  obtain ⟨I, hI⟩ := hG
  exact ⟨hI.2.2.2.2.1, I, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.2.1,
    hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2.2⟩

end G11_6

@[expose] def G_11_7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ¬ FaithfulOn X I ∧ ¬ IsIrr (normalClosure Γ L) ⊤

section G11_7

theorem as_G_11_7
    : G_11_7 := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  suffices h : ¬ FaithfulOn X I ∧ I ≠ ⊤ by
    refine ⟨h.1, fun hirr => h.2 ?_⟩
    have hne : I ≠ ⊥ := fun hbot => by
      have hlt := hI.1.2.2.1
      rw [hbot, inf_bot_eq] at hlt
      exact lt_irrefl _ hlt
    rcases hirr.2.2 I hI.1.1 bot_le le_top with h0 | h0
    · exact absurd h0 hne
    · exact h0
  refine CFSG.Quasithin.G11.Canon.g11_7_canon
    (Q := fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) => G112FaithfulWithU33 B Γ X)
    ?_ V B Γ v₁ W X X₀ L ⟨⟨cs.cx.hyp, cs.cx.sqtk, cs.h108, cs.numConj⟩, cs.cx.notConcl⟩ I hI
  exact
    { c2 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 1 refine Or.inr ?_
        exact Or.inl h
      c4 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 3 refine Or.inr ?_
        exact Or.inl h
      c5 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 4 refine Or.inr ?_
        exact Or.inl h
      c6 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 5 refine Or.inr ?_
        exact Or.inl h
      c6' := fun _ _ _ h => Or.inr h
      c7 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 6 refine Or.inr ?_
        exact Or.inl h
      c10 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 10 refine Or.inr ?_
        exact Or.inl h
      c11 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 11 refine Or.inr ?_
        exact Or.inl h
      c13 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 13 refine Or.inr ?_
        exact h }

end G11_7

@[expose] def G_11_8Legacy : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11SetupF B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∃ k : ℕ, Module.finrank (ZMod 2) V = k * Module.finrank (ZMod 2) I ∧ 2 < k) ∧
          fixedSpace X = Submodule.span (ZMod 2) {v₁}

@[expose] def G_11_8 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∃ k : ℕ, Module.finrank (ZMod 2) V = k * Module.finrank (ZMod 2) I ∧ 2 < k) ∧
          fixedSpace X = Submodule.span (ZMod 2) {v₁}

section G11_8

theorem as_G_11_8
    : G_11_8 := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  have hQ : CFSG.Quasithin.G11.Canon.QContains
      (fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) =>
          G112FaithfulWithU33 B Γ X) :=
    { c2 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 1 refine Or.inr ?_
        exact Or.inl h
      c4 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 3 refine Or.inr ?_
        exact Or.inl h
      c5 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 4 refine Or.inr ?_
        exact Or.inl h
      c6 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 5 refine Or.inr ?_
        exact Or.inl h
      c6' := fun _ _ _ h => Or.inr h
      c7 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 6 refine Or.inr ?_
        exact Or.inl h
      c10 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 10 refine Or.inr ?_
        exact Or.inl h
      c11 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 11 refine Or.inr ?_
        exact Or.inl h
      c13 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 13 refine Or.inr ?_
        exact h }
  have hC9 : CFSG.Quasithin.G11.Canon.G118NineContains
      (fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) =>
          G112FaithfulWithU33 B Γ X) :=
    { c9 := fun _ _ _ h => by
        refine Or.inl ?_
        iterate 9 refine Or.inr ?_
        exact Or.inl h }
  exact CFSG.Quasithin.G11.Canon.g11_8_canon hQ hC9 CFSG.Quasithin.G11.Canon.g118NineInput_holds
    V B Γ v₁ W X X₀ L ⟨⟨cs.cx.hyp, cs.cx.sqtk, cs.h108, cs.numConj⟩, cs.cx.notConcl⟩ I hI

end G11_8

@[expose] def G_11_9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        (∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
          ∃ Ix : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) Ix ∧ Ix ≤ B.orthogonal I ∧
            Ix ≠ I ∧ conjSub x Ix = Ix ∧
            ∃ c : V, Ix ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x Ix c) ∧
        (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ IsNatAltModule (normalClosure Γ L) I n) ∧
        (centralizerIn X (normalClosure Γ L)).relIndex X = 2

section G11_9

theorem g119Canonical_full
    :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)), G11CanonicalSetup B Γ v₁ W X X₀ L →
        ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
          (∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
            ∃ Ix : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) Ix ∧ Ix ≤ B.orthogonal I ∧
              Ix ≠ I ∧ conjSub x Ix = Ix ∧
              ∃ c : V, Ix ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x Ix c) ∧
          (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ IsNatAltModule (normalClosure Γ L) I n) ∧
          (centralizerIn X (normalClosure Γ L)).relIndex X = 2 ∧
          ∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
            3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I) := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  obtain ⟨⟨k, hk, hk2⟩, hfix⟩ := as_G_11_8 V B Γ v₁ W X X₀ L cs I hI
  have hne : I ≠ ⊥ := fun hbot => by
    have hlt := hI.1.2.2.1
    rw [hbot, inf_bot_eq] at hlt
    exact lt_irrefl _ hlt
  have hpos : 0 < Module.finrank (ZMod 2) I :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrank : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V := by
    rw [hk]
    exact Nat.mul_lt_mul_of_pos_right hk2 hpos
  have hcent : ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i := fun x hx =>
    CFSG.Quasithin.G11.G118.fixes_of_mem_centralizerIn cs.h108 hI hx
  have c : CFSG.Quasithin.G11.G119Ctx B Γ v₁ W X X₀ L I := by
    obtain ⟨hirrP, hv₁, hinvX, -, hhom, hiso, -, hfaith, hnot⟩ := hI
    refine ⟨cs.h108, cs.cx.sqtk, hirrP, hv₁, hinvX, hhom, ?_, hfaith, hnot, hrank, hfix, hcent⟩
    rcases hiso with h | h
    · exfalso
      have h1 : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) V := by
        rw [h]
        exact finrank_top (ZMod 2) V
      omega
    · exact h
  have h14c : CFSG.Quasithin.G11.G1014Concl B Γ v₁ W X L := as_G_10_14 V B Γ v₁ W X X₀ L cs.h108
  have hE : CFSG.Quasithin.G11.G119E11Use :=
    CFSG.Quasithin.G11.g119_e11Use_of_e11Stmt CFSG.Quasithin.G11.e11
  have hrk : ∀ (y : GLV V) (hy : y ∈ X), y ∉ centralizerIn X (normalClosure Γ L) →
      Module.finrank (ZMod 2) (LinearMap.range (commMap y I (c.conjSub_I hy))) = 1 := by
    intro y hy hyC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hy
    exact c.finrank_commMap_I h14c hy hyC hJ hle hne hfixJ
  obtain ⟨x₀, hx₀, hx₀C⟩ := c.exists_not_central
  obtain ⟨n, hn5, hn8, hnat, hdec⟩ :=
    c.natural_package_of_b5 CFSG.Quasithin.asB56_holds hx₀ (hrk x₀ hx₀ hx₀C)
  have h4 : 4 ≤ Module.finrank (ZMod 2) I := by
    obtain ⟨θ, β, hrange, hker, -, -⟩ := hnat
    have := g119_four_le_finrank_range_of_ker hn5 β hker
    rwa [hrange, finrank_top] at this
  refine ⟨?_, ⟨n, hn5, hn8, c.isNatAltModule_of_natSym hx₀ (hrk x₀ hx₀ hx₀C) hnat hdec⟩,
    c.relIndex_eq_two hx₀ hx₀C hrk hnat, ?_⟩
  · intro x hx hxC
    obtain ⟨J, hJ, hle, hne, hfixJ⟩ := c.exists_fixed hE hx
    obtain ⟨c', hc1, hc2⟩ := c.transvection_Ix h14c hx hxC hJ hle hne hfixJ
    exact ⟨J, hJ, hle, hne, hfixJ, c', hc1, hc2⟩
  · intro x hx hxC
    exact c.three_le_finrank_fixed hx (hrk x hx hxC) h4

theorem as_G_11_9
    : G_11_9 := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI
  obtain ⟨h1, h2, h3, -⟩ := g119Canonical_full V B Γ v₁ W X X₀ L cs I hI
  exact ⟨h1, h2, h3⟩

end G11_9

namespace ChG

@[expose] def G114Canonical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCx B Γ v₁ W X X₀ → IsIrr Γ ⊤

@[expose] def G115Canonical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCx B Γ v₁ W X X₀ →
      ∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x

@[expose] def G115ComponentCanonical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11CanonicalCx B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      (∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x) →
      ∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧
        (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) ∧ numConjugates Γ L ≤ 2

@[expose] def G116Canonical : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∃ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I

@[expose] def G11CanonicalCentralizerOnI : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i

@[expose] def G11CanonicalFixedRank : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11CanonicalSetup B Γ v₁ W X X₀ L →
      ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
          3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I)

theorem g112_u33_handback {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V))
    (hU33 : G112ProposedU33 Γ) : G112FaithfulWithU33 B Γ X :=
  Or.inr hU33

theorem g112Canonical_of_lemmas (h4 : G114Canonical) (h5 : G115Canonical)
    (h5b : G115ComponentCanonical) (h6 : G116Canonical)
    (h8 : G_11_8) (h9 : G_11_9)
    (hcentralizer : G11CanonicalCentralizerOnI) (hfixedRank : G11CanonicalFixedRank) :
    G_11_2 := by
  intro V _ _ _ B Γ v₁ W X X₀ hyp hq
  by_cases hU33 : G112ProposedU33 Γ
  · exact g112_u33_handback B Γ X hU33
  by_contra hnot
  have cx : G11CanonicalCx B Γ v₁ W X X₀ := ⟨hyp, hq, hnot⟩
  have hirr := h4 V B Γ v₁ W X X₀ cx
  have hx := h5 V B Γ v₁ W X X₀ cx
  obtain ⟨L, hLc, hLn, hLnum⟩ := h5b V B Γ v₁ W X X₀ cx hirr hx
  have h108 : G108Hyp B Γ v₁ W X X₀ L :=
    { toG101Hyp := hyp.toG101Hyp
      irreducible := hirr
      component := hLc
      noncomm := hLn
      three := Or.inr hLnum
      four := hyp.four }
  have hs : G11CanonicalSetup B Γ v₁ W X X₀ L := ⟨cx, h108, hLnum⟩
  obtain ⟨I, hI⟩ := h6 V B Γ v₁ W X X₀ L hs
  obtain ⟨-, hfix⟩ := h8 V B Γ v₁ W X X₀ L hs I hI
  obtain ⟨-, -, hidx⟩ := h9 V B Γ v₁ W X X₀ L hs I hI
  have hcI := hcentralizer V B Γ v₁ W X X₀ L hs I hI
  have h3 := hfixedRank V B Γ v₁ W X X₀ L hs I hI
  set C := centralizerIn X (normalClosure Γ L) with hC
  obtain ⟨x, hxX, hxC⟩ : ∃ x ∈ X, x ∉ C := by
    by_contra hall
    have hle : X ≤ C := fun x hx => by_contra fun h => hall ⟨x, hx, h⟩
    have : C.relIndex X = 1 := Subgroup.relIndex_eq_one.2 hle
    rw [hidx] at this
    exact absurd this (by norm_num)
  have hge := h3 x hxX hxC
  have hindex : (C.subgroupOf X).index = 2 := hidx
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 hindex
  have hle : fixedSpace (Subgroup.zpowers x) ⊓ I ≤ fixedSpace X := by
    intro i hi y hy
    have hxi : x i = i := hi.1 x (Subgroup.mem_zpowers x)
    by_cases hyC : y ∈ C
    · exact hcI y hyC i hi.2
    ·
      have hxa : (⟨x, hxX⟩ : ↥X) * a ∈ C.subgroupOf X := by
        rcases ha ⟨x, hxX⟩ with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd (Subgroup.mem_subgroupOf.1 h2) hxC
      have hya : (⟨y, hy⟩ : ↥X) * a ∈ C.subgroupOf X := by
        rcases ha ⟨y, hy⟩ with ⟨h1, _⟩ | ⟨h2, _⟩
        · exact h1
        · exact absurd (Subgroup.mem_subgroupOf.1 h2) hyC
      have hyx : y * x⁻¹ ∈ C := by
        have := (C.subgroupOf X).mul_mem hya ((C.subgroupOf X).inv_mem hxa)
        have h' := Subgroup.mem_subgroupOf.1 this
        simpa [mul_assoc] using h'
      have h1 : (y * x⁻¹) i = i := hcI (y * x⁻¹) hyx i hi.2
      have h2 : y i = (y * x⁻¹) (x i) := by
        show y i = y (x⁻¹ (x i))
        have : x⁻¹ (x i) = i := x.symm_apply_apply i
        rw [this]
      rw [h2, hxi]
      exact h1
  have hle2 : fixedSpace (Subgroup.zpowers x) ⊓ I ≤ Submodule.span (ZMod 2) {v₁} := by
    rw [← hfix]
    exact hle
  have hrank := Submodule.finrank_mono hle2
  have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {v₁}) = 1 :=
    finrank_span_singleton hyp.point
  omega

end ChG

theorem g114Canonical_holds : CFSG.ASVolI.ChG.G114Canonical := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have h4 := CFSG.Quasithin.g10_4 CFSG.Quasithin.G11.g10_3 CFSG.Quasithin.G11.SzG11S.b49
  have h5 : CFSG.Quasithin.G11.G1005Stmt := CFSG.Quasithin.g10_5 CFSG.Quasithin.G11.g10_3 h4
  rcases h5 V B Γ v₁ W X X₀ cx.hyp.toG101Hyp with h | ⟨hd, h18⟩
  · exact h
  · exact (cx.notConcl (Or.inl (Or.inr (Or.inl ⟨hd, Or.inr h18⟩)))).elim

theorem g115Canonical_holds : CFSG.ASVolI.ChG.G115Canonical := by
  intro V _ _ _ B Γ v₁ W X X₀ cx
  have hirr : IsIrr Γ ⊤ := g114Canonical_holds V B Γ v₁ W X X₀ cx
  by_contra hcon
  have hfaith : ∀ x ∈ X, (∀ f ∈ fittingOf Γ, x * f = f * x) → x = 1 := by
    intro x hx hc
    by_contra hx1
    exact hcon ⟨x, hx, hx1, hc⟩
  have h101 := cx.hyp.toG101Hyp
  obtain ⟨k, hk⟩ := h101.exists_card_X
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero] at hk
    have hX1 : ∀ x ∈ X, x = 1 := by
      intro x hx
      have hsub : Subsingleton ↥X := Nat.card_eq_one_iff_unique.1 hk |>.1
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ↥X) 1)
    rcases cx.hyp.three with h | ⟨a, ha, -, hv⟩
    ·
      obtain ⟨w, hw⟩ : ∃ w, B v₁ w ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h101.point (h101.nondegenerate v₁ hall)
      rcases h w (fun x hx => by rw [hX1 x hx]; rfl) with hw0 | hw1
      · exact hw (by rw [hw0, map_zero])
      · exact hw (by rw [hw1]; exact h101.alt v₁)
    · have : a = 1 := hX1 a ha
      subst this
      have : v₁ = 0 := by
        obtain ⟨u, hu⟩ := hv
        rw [← hu]
        simp
      exact h101.point this
  have hbound : Module.finrank (ZMod 2) V ≤ 2 * (k + 1) := by
    refine h101.dim_le_two_mul.trans (Nat.mul_le_mul_left 2 (Nat.succ_le_succ ?_))
    have hdvd : X₀.relIndex X ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.relIndex_dvd_card X₀ X
    calc Nat.log 2 (X₀.relIndex X) ≤ Nat.log 2 (2 ^ k) :=
          Nat.log_mono_right (Nat.le_of_dvd (by positivity) hdvd)
      _ = k := Nat.log_pow Nat.one_lt_two k
  have hyp94 : G94Hyp Γ X k :=
    { quotient := cx.sqtk
      A_le := h101.X_le
      A_elem := h101.X_isElemAbelian
      A_card := hk
      A_ne := hk1
      bound := hbound
      irreducible := hirr
      faithful := hfaith }
  have hconcl := (CFSG.Quasithin.SzG11.g94Stmt_proved V Γ X k hyp94).toG112
  rcases hconcl with h | h | h
  · exact cx.notConcl (Or.inl (Or.inl h))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inl h)))
  · exact cx.notConcl (Or.inl (Or.inr (Or.inr (Or.inl h))))

theorem g11CanonicalCentralizerOnI_holds : CFSG.ASVolI.ChG.G11CanonicalCentralizerOnI := by
  intro V _ _ _ B Γ v₁ W X X₀ L cs I hI x hx
  exact CFSG.Quasithin.G11.G118.fixes_of_mem_centralizerIn cs.h108 hI hx

section G115b

theorem g115ComponentCanonical_holds
    : CFSG.ASVolI.ChG.G115ComponentCanonical := by
  intro V _ _ _ B Γ v₁ W X X₀ cx hirr hx
  obtain ⟨L, hL, hn⟩ :=
    CFSG.Quasithin.G11.SzG11S.g115bPart1 V B Γ v₁ W X X₀ cx.hyp hirr hx
  exact ⟨L, hL, hn, CFSG.Quasithin.G11.SzG11S.numConjugates_le_two_of_asA21
    CFSG.Quasithin.asA21SQTKSection cx.sqtk hL⟩

end G115b

section G116

theorem g116Canonical_holds
    : CFSG.ASVolI.ChG.G116Canonical := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs
  have h3 := CFSG.Quasithin.G11.g10_3
  have h4 := CFSG.Quasithin.g10_4 h3 CFSG.Quasithin.G11.SzG11S.b49
  have h10 := CFSG.Quasithin.G11.g10_10_of_g10_4 h4
  have h11 := CFSG.Quasithin.G11.g10_11 h10
  have h12 := CFSG.Quasithin.G11.g10_12 h11
  have h13 := CFSG.Quasithin.G11.g10_13 h10 h11
  have h1212 := CFSG.Quasithin.G11.g12_12_of_four
    (CFSG.Quasithin.G11.g12_1_of_four CFSG.Quasithin.G11.g12_four_fact)
    CFSG.Quasithin.G11.g12_part_four_fact
  have h15 : CFSG.Quasithin.G11.G1015Stmt :=
    CFSG.Quasithin.G11.g10_15 h10 h11 h12 h13 h1212 CFSG.Quasithin.G11.outerGLInput
      CFSG.Quasithin.G11.inspect_simple CFSG.Quasithin.G11.inspect_outer
      CFSG.Quasithin.G11.inspect_sylow
      (CFSG.Quasithin.SzG11.sectionSQTInput_of_asA21 CFSG.Quasithin.asA21SQTKSection)
  have hII : CFSG.Quasithin.G11.G116IIStmt :=
    CFSG.Quasithin.G11.g116_II CFSG.Quasithin.G11.Harris.g93StmtDimensionOnly_holds
      CFSG.Quasithin.G11.outerSL34Input
  have hIII : CFSG.Quasithin.G11.G116IIIStmt := CFSG.Quasithin.G11.g116_III
  have h108 := hs.h108
  have hirrH : ∀ I : Submodule (ZMod 2) V,
      IrrPlus (normalClosure Γ L) I → IsIrr (normalClosure Γ L) I :=
    fun I hI => hI.isIrr h108.fixedSpace_H
  have hG : ∃ I : Submodule (ZMod 2) V, CFSG.Quasithin.G11.G116Props B Γ v₁ X L I := by
    obtain ⟨I, hI, hone, htwo, hthree⟩ :=
      (CFSG.Quasithin.G11.G1015Concl_iff B Γ v₁ W X L).1 (h15 V B Γ v₁ W X X₀ L h108 hs.cx.sqtk)
    rcases htwo with h2I | h2II | h2III
    · have hone_i : CFSG.Quasithin.G11.G1015One_i B Γ v₁ W X L I := by
        rcases hone with h | ⟨x, hx, hxI, -, hno, -⟩
        · exact h
        · exfalso
          have hconj : IrrPlus (normalClosure Γ L) (conjSub x I) :=
            ((hirrH I hI).conj_of_normal (normalClosure_normal Γ L) (h108.X_le hx)).irrPlus
              h108.fixedSpace_H
          exact hno (h2I.1 I (conjSub x I) hI hconj)
      have hnot : ¬ AutAll (normalClosure Γ L) I :=
        CFSG.Quasithin.G11.not_autAll_of_selfDual (h108.two_lt_finrank (hirrH I hI)) h2I.2.1
      refine ⟨I, hI, hone_i.2.2.1, hone_i.2.1, hone_i.2.2.2, hone_i.1, ?_, h2I.2.1, h2I.2.2.1,
        hnot⟩
      rcases h2I.2.2.2 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2II.1
        · exact h
      rcases hII V B Γ v₁ W X X₀ L h108 hs.numConj hs.cx.sqtk I hI hone_ii h2II hthree with
        h | h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl h
      · exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inl h
    · exfalso
      have hone_ii : CFSG.Quasithin.G11.G1015One_ii B Γ v₁ W X L I := by
        rcases hone with h | h
        · exact absurd h.1 h2III.1
        · exact h
      have h12' := hIII V B Γ v₁ W X X₀ L h108 hs.cx.sqtk I hI hone_ii h2III hthree
      exact hs.cx.notConcl <| Or.inl <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h12'
  exact hG

end G116

section G11_2

theorem as_G_11_2
    : G_11_2 :=
  CFSG.ASVolI.ChG.g112Canonical_of_lemmas g114Canonical_holds g115Canonical_holds
    g115ComponentCanonical_holds g116Canonical_holds as_G_11_8 as_G_11_9
    g11CanonicalCentralizerOnI_holds
    (fun V _ _ _ B Γ v₁ W X X₀ L cs I hI x hx hxC =>
      (g119Canonical_full V B Γ v₁ W X X₀ L cs I hI).2.2.2 x hx hxC)

end G11_2

end CFSG.ASVolI
