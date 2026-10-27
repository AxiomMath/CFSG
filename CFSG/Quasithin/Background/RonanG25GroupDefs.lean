module

public import CFSG.Quasithin.Background.G25Eight

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section Group

variable {G : Type} [Group G]

abbrev gS (V H L : Subgroup G) : Subgroup G := pCoreOf 2 (L ⊔ conjClosure V H)

abbrev gW (V H L : Subgroup G) : Subgroup G := conjClosure V H ⊓ gS V H L

abbrev gS₂ (V H : Subgroup G) (g h : G) : Subgroup G :=
  conjClosure V H ⊓ rconj (conjClosure V H) g ⊓ rconj (conjClosure V H) h

abbrev gS₃ (V H L : Subgroup G) (g h : G) : Subgroup G := sThree (gW V H L) g h

variable {n : ℕ} {V V₁ L T H : Subgroup G}

theorem lOne_le_L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left

theorem lOne_le_normalizer : lOne L V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  (oTwoUpper_le _).trans inf_le_right

@[expose] noncomputable def rho (D : NatData3 n L (pCoreOf 2 (L ⊔ T)) V V₁) :
    ↥(lOne L V₁) →* SL(3, GaloisField 2 n) :=
  D.θ.comp (Subgroup.inclusion lOne_le_L)

structure SubFacts (V L H : Subgroup G) (g h : G) : Prop where
  V_le_S₂ : V ≤ gS₂ V H g h
  S₂_le_S₃ : gS₂ V H g h ≤ gS₃ V H L g h
  S₃_le_S : gS₃ V H L g h ≤ gS V H L
  V_le_center : V ≤ centerOf (gS V H L)
  I_V : L ⊔ conjClosure V H ≤ Subgroup.normalizer (V : Set G)
  I_S₂ : L ⊔ conjClosure V H ≤ Subgroup.normalizer (gS₂ V H g h : Set G)
  I_S₃ : L ⊔ conjClosure V H ≤ Subgroup.normalizer (gS₃ V H L g h : Set G)
  I_S : L ⊔ conjClosure V H ≤ Subgroup.normalizer (gS V H L : Set G)
  comm : ⁅gS₂ V H g h, L ⊔ conjClosure V H⁆ ≤ V
  dir : (gW V H L ⊓ rconj (gW V H L) g) ⊓ (gW V H L ⊓ rconj (gW V H L) h) = gS₂ V H g h

structure SumFacts (D : NatData3 n L (pCoreOf 2 (L ⊔ T)) V V₁) (g h : G) (hg : g ∈ L)
    (hh : h ∈ L) (r s : ℕ)
    (φ₇ : ↥(gS V H L) →* Multiplicative (Fin r → Fin 3 → GaloisField 2 n))
    (φ₆ : ↥(gS₃ V H L g h) →* Multiplicative (Fin s → Fin 3 → GaloisField 2 n)) : Prop where
  seven : IsSumOfSL3ModulesVia r L (gS V H L) (gS₃ V H L g h) D.θ φ₇
  seven_W : ∀ x : ↥(gS V H L), (x : G) ∈ gW V H L ⊔ gS₃ V H L g h ↔
    ∀ l : Fin r, ∃ c : GaloisField 2 n,
      Multiplicative.toAdd (φ₇ x) l = c • vE (GaloisField 2 n) 0
  six : IsSumOfSL3ModulesVia s L (gS₃ V H L g h) (gS₂ V H g h)
    ((dualHom (GaloisField 2 n) 3).comp D.θ) φ₆
  six_g : ∀ x : ↥(gS₃ V H L g h), (x : G) ∈ gW V H L ⊓ rconj (gW V H L) g ↔
    ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
      Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0
  six_h : ∀ x : ↥(gS₃ V H L g h), (x : G) ∈ gW V H L ⊓ rconj (gW V H L) h ↔
    ∀ l : Fin s, Multiplicative.toAdd (φ₆ x) l ⬝ᵥ vE (GaloisField 2 n) 0 = 0 ∧
      Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0
  six_gh : ∀ x : ↥(gS₃ V H L g h), (x : G) ∈ rconj (gW V H L) g ⊓ rconj (gW V H L) h ↔
    ∀ l : Fin s,
      Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨g, hg⟩⁻¹ • vE (GaloisField 2 n) 0) = 0 ∧
      Multiplicative.toAdd (φ₆ x) l ⬝ᵥ (D.θ ⟨h, hh⟩⁻¹ • vE (GaloisField 2 n) 0) = 0

end Group

end CFSG.Quasithin.RonanG25
