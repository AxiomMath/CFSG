module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveBCoordBLabel (n p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1 ∧
      (p ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ p = 3)) ∨
    (lab.tag = .twD ∧ lab.rank = n ∧ (p ∣ 2 ^ lab.n - 1 ∨ Even n ∧ p ∣ 2 ^ lab.n + 1)) ∨
    (lab.tag = .D ∧ lab.rank = n ∧ Odd n ∧ lab.n = 1 ∧ p = 3) ∨
    (lab.tag = .A ∧ (lab.rank = 2 * n - 3 ∨ lab.rank = 2 * n - 2) ∧ lab.n = 1 ∧ p = 3)

@[expose] def GGSecFiveBCoordBResLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p = 3 ∧ ((lab.tag = .A ∧ 6 ≤ lab.rank ∧ lab.n = 1) ∨ (lab.tag = .E6 ∧ lab.n = 1) ∨
    (lab.tag = .F4 ∧ lab.n = 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1))

@[expose] def GGSecFiveBCoordBResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (n : ℕ), 4 ≤ n → ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
          GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBResLabel p lab) p Bs L →
            GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L

@[expose] def GGSecFiveBCoordBLabelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∀ (n : ℕ), 4 ≤ n → ∀ (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n),
        (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0 →
          GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L

end CFSG.StandardType

end
