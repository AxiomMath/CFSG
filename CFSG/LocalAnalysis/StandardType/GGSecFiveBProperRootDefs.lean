module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def GGSecFiveBPermUnitaryLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → B ≠ Bs →
      ∀ (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
          ∃ r f : ℕ, 3 ≤ r ∧ p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, r, f⟩ (L ⧸ Subgroup.center L)

@[expose] def GGSecFiveBPermUnitaryModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → B ≠ Bs →
      ∀ (n : ℕ) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))),
        (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p →
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (f d : ℕ)
            (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (φ : ↥(unitarySU 2 f F d) →* L),
            4 ≤ d ∧ p ∣ 2 ^ f + 1 ∧ Nat.card F = (2 ^ f) ^ 2 ∧ UnitTB.Model φ ∧
              ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t

end CFSG.StandardType

end
