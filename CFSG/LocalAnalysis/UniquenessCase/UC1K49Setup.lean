module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs49
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

abbrev cj (g a : G) : G := g⁻¹ * a * g

abbrev Lc (L : Subgroup G) (x : G) (i : ℕ) : Subgroup G := CFSG.conjugate L (x ^ i)

structure Setup49 (H X L Q I : Subgroup G) : Prop where
  X_le : X ≤ H
  card_X : Nat.card X = 3
  L_mem : L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H
  L_alt : IsAlt (Bar2 L) 5
  X_nle : ¬ X ≤ Subgroup.normalizer (L : Set G)
  Q_eq : Q = CFSG.Open.pCoreOf 2 H
  H_eq : H = X ⊔ L ⊔ Q
  I_eq : I = ⨆ x ∈ X, CFSG.conjugate L x

noncomputable def KI (X I : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.perfectCore (Subgroup.centralizer (X : Set G) ⊓ I)

@[expose] def KI49 (X I : Subgroup G) : Prop :=
  CFSG.Quasithin.IsExt ↥(KI X I)
    (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
    (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)

@[expose] def Concl49 (H X L Q I : Subgroup G) : Prop :=
  (∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
      ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ = ⊥) ∧
    (Q = (Q ⊓ Subgroup.centralizer (I : Set G)) ⊔ ⁅Q, I⁆ ∧
      ⁅Q ⊓ Subgroup.centralizer (I : Set G), ⁅Q, I⁆⁆ = ⊥) ∧
    ((IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (I : Set G)) ∨
        CFSG.Open.pRank 2 (Q ⊓ Subgroup.centralizer (I : Set G)) = 1) →
      CFSG.Open.IsElemAbelian 2
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G))) ∧
      H ≤ Subgroup.normalizer
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)) : Set G) ∧
      ∀ (p : ℕ), p.Prime → ∀ E : Subgroup G, E ≤ H → H ≤ Subgroup.normalizer (E : Set G) →
        CFSG.Open.IsElemAbelian p E →
        E ≤ CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)))

@[expose] def XReg49 (X A : Subgroup G) : Prop :=
  Nat.card X = 3 ∧ CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
    X ≤ Subgroup.normalizer (A : Set G) ∧
    Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set G)) = 3

abbrev Z49 (X A : Subgroup G) : Subgroup G := A ⊓ Subgroup.centralizer (X : Set G)

theorem k49I_of_core
    (h : ∀ (G : Type) [Group G] [Finite G] (H X L Q I : Subgroup G),
      Setup49 H X L Q I → KI49 X I → Concl49 H X L Q I) : K49I := by
  intro G _ _ H X L Q I h1 h2 h3 h4 h5 h6 h7 hI hK
  exact h G H X L Q I ⟨h1, h2, h3, h4, h5, h6, h7, hI⟩ (by subst hI; exact hK)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
