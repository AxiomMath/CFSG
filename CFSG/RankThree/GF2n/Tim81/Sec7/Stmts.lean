module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec7

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.Timmesfeld.Transvection CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev yOf (h : G) : Subgroup G := cenOf (Subgroup.zpowers h)

abbrev rOf (M : Subgroup G) (h : G) : Subgroup G := M ⊓ yOf h

abbrev oOf (M : Subgroup G) (h : G) : Subgroup G := inSubgroup (pPrimeCore 2) (rOf M h)

@[expose] def Stmt71 (M V : Subgroup G) : Prop :=
  ∀ N : Subgroup G, V ≤ N → N ≤ Pc M V → m0Of M V ≤ Subgroup.normalizer (N : Set G) →
    N = V ∨ N = Pc M V

@[expose] def Stmt72 (M V : Subgroup G) (n f : ℕ) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B) ∧
    Nat.card ↥(p0Of M V (A ⊔ B)) = Nat.card V ^ (2 * n - 3) ∧
    ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ = V ∧
    p0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) = V ∧
    (∀ x ∈ p0Of M V (A ⊔ B), x * x ∈ V) ∧
    {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)} ∧
    p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B) ∧
    r0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) = V ∧
    (∀ (hf : 1 ≤ f) (h5 : 5 ≤ n), IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
      (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf (by omega)) ∧
    (n = 4 → ∃ C ∈ sigmaSet M V, ∃ D ∈ sigmaSet M V, C ⊔ D ≤ cenOf (A ⊔ B) ∧ IsL2Gen C D ∧
      r0Of M V (A ⊔ B) = C ⊔ D ⊔ p0Of M V (A ⊔ B))

@[expose] def Stmt73alpha (M V : Subgroup G) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    inSubgroup (Op_p'p 2) (rOf M h) = oOf M h ⊔ p0Of M V (A ⊔ B) ∧
    oOf M h ⊓ p0Of M V (A ⊔ B) = ⊥ ∧ ⁅oOf M h, p0Of M V (A ⊔ B)⁆ = ⊥ ∧
    rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)) = oOf M h ⊔ V ∧
    (∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B)) ∧
    generalizedFitting (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) =
      pCore 2 (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) ∧
    pCore 2 (↥(rOf M h) ⧸ pPrimeCore 2 ↥(rOf M h)) =
      ((p0Of M V (A ⊔ B)).subgroupOf (rOf M h)).map (QuotientGroup.mk' _)

@[expose] def Stmt73gamma (M V : Subgroup G) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    (∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) →
      M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (N : Set G) → N = V ∨ N = p0Of M V (A ⊔ B)) ∧
    Maximal (fun U : Subgroup G => U ≤ rOf M h ∧ rOf M h ≤ Subgroup.normalizer (U : Set G) ∧
      Assembly.IsElemAbelian 2 U) V

@[expose] def Stmt73delta (M V : Subgroup G) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    ∃ H₀ : Subgroup G, H₀ ≤ yOf h ∧ p0Of M V (A ⊔ B) ≤ H₀ ∧ ¬ H₀ ≤ M ∧
      inSubgroup (pCore 2) H₀ ≠ ⊥ ∧ ∃ c ∈ H₀, conjSubgroup c V ≠ V ∧
        conjSubgroup c V ≤ M ⊓ cenOf (A ⊔ B)

@[expose] def Stmt73eps (M V : Subgroup G) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    inSubgroup (pPrimeCore 2) (yOf h) = oOf M h ∧
      ∀ y ∈ yOf h, inSubgroup (pPrimeCore 2) (yOf h) ≤ cenOf (conjSubgroup y V)

@[expose] def Stmt73 (M V : Subgroup G) (n f : ℕ) : Prop :=
  ∀ (A B : Subgroup G) (h : G), L2Datum M V A B h →
    y0Of V (Subgroup.zpowers h) ≤ cenOf (A ⊔ B) ∧
    (∀ y ∈ yOf h, ∃ x ∈ y0Of V (Subgroup.zpowers h), conjSubgroup y V = conjSubgroup x V) ∧
    pCore 2 ↥(y0Of V (Subgroup.zpowers h)) = ⊥ ∧
    pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h)) ≤ Subgroup.center _ ∧
    ∃ Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n →*
        (↥(y0Of V (Subgroup.zpowers h)) ⧸ pPrimeCore 2 ↥(y0Of V (Subgroup.zpowers h))),
      Function.Surjective Φ ∧ Φ.ker = Subgroup.center _

@[expose] def Stmt74 (M V : Subgroup G) : Prop :=
  ∀ (A B : Subgroup G) (g : G), A = conjSubgroup g V → A ∈ sigmaSet M V →
    B ∈ sigmaSet M V → IsL2Gen A B →
    y0Of V (A ⊔ B) = (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) ∧
    y0Of V (A ⊔ B) ⊓ conjSubgroup g (Pc M V) = ⊥ ∧
    y0Of V (A ⊔ B) ⊔ conjSubgroup g (Pc M V) = conjSubgroup g (m0Of M V)

@[expose] def Stmt75 (V : Subgroup G) : Prop :=
  ∀ A ∈ gammaAt V, gammaAt A = gammaAt V

@[expose] def Stmt76 (V : Subgroup G) : Prop :=
  ∀ A ∈ gammaAt V, ∀ B ∈ gammaAt V, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B

@[expose] def Stmt76U (V : Subgroup G) (n f : ℕ) : Prop :=
  ∀ hf : 1 ≤ f, ∃ Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (n + 2) →* G,
    Φ.ker = Subgroup.center _ ∧ Φ.range = (⨆ A ∈ gammaAt V, A) ∧ ∀ X : Subgroup G,
      X ∈ gammaAt V ↔ ∃ x, X = (CFSG.Timmesfeld.ARS.conjSub
        ((Unitary.rootDatum (card_galoisField_two_mul hf) (n + 2)).rootGroup
          (unitaryLongRoot (n + 2) (by omega))) x).map Φ

@[expose] def Stmt77a (V : Subgroup G) : Prop :=
  omegaSet V ≠ gammaAt V → ∃ B ∈ omegaSet V, B ∉ gammaAt V ∧ ⁅V, B⁆ = ⊥

@[expose] def Stmt77b (V : Subgroup G) : Prop :=
  (∃ B ∈ omegaSet V, B ∉ gammaAt V ∧ ⁅V, B⁆ = ⊥) →
    ∃ B ∈ omegaSet V, B ∉ gammaAt V ∧ ⁅V, B⁆ = ⊥ ∧ ∃ A₁ ∈ gammaAt V, ∃ A₂ ∈ gammaAt V,
      IsL2Gen A₁ A₂ ∧ B ≤ cenOf (A₁ ⊔ A₂)

@[expose] def Stmt77 (V : Subgroup G) : Prop :=
  omegaSet V = gammaAt V

end CFSG.RankThree.GF2n.Tim81.Sec7
