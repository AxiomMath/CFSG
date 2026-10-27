module

public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2W
public import CFSG.Quasithin.Vol2.Ch11SecAFactsLine
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadU

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
  CFSG.Quasithin.Vol2.Ch11.SecB

@[expose] def Rad11_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₂ : Subgroup G),
    Hyp11 G T L I n → KindG2 L (fsuV T I) n →
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → IsVi T L I n 2 V₂ →
      quasithinIsCComponent (LOf L V₂)
        (Subgroup.normalizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G)) ∧
      ¬ LOf L V₂ ≤ Subgroup.centralizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G) ∧
      ∀ K : Subgroup G,
        quasithinIsCComponent K (Subgroup.normalizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G)) →
        ¬ K ≤ Subgroup.centralizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G) → K = LOf L V₂

@[expose] def FactSiegelG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      (∀ h ∈ H, ∀ z ∈ Z, h z = z) → commV H = ⊤ →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
        commS (perfectCore (H ⊓ stabW U₂)) U₂ ⊓ Z = ⊥

@[expose] def FactG2OffenderRad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ)
    (h : FlagG2 L V X T V₁ V₂ V₃ n), V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 A →
      autI h.elem A ∈ E3.aSet (2 * n) (autI h.elem X) →
      ∃ l ∈ L, ∀ x ∈ L, conjSubgroup V₁ l ≤ conjSubgroup V₂ x →
        conjSubgroup V₂ x ≤ conjSubgroup V₃ l →
        ∃ D : Subgroup G, D ≤ A ∧ A ⊓ Subgroup.centralizer (V : Set G) ≤ D ∧
          E3.mQuot A D = 2 * n ∧
          A ⊓ Subgroup.centralizer
            ((V ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) = D ∧
          ⁅V ⊓ Subgroup.centralizer (D : Set G), A⁆ =
            ⁅conjSubgroup V₂ x, LOf L (conjSubgroup V₂ x)⁆

@[expose] def FactG2RootLineRad : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V X T V₁ V₂ V₃ : Subgroup G) (n : ℕ),
    FlagG2 L V X T V₁ V₂ V₃ n → V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
    ∀ E : Subgroup G, E ≤ X ⊓ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 E →
      E3.mQuot V (V ⊓ Subgroup.centralizer (E : Set G)) = 2 * n →
        ∃ l ∈ L, ⁅V, E⁆ = ⁅conjSubgroup V₂ l, LOf L (conjSubgroup V₂ l)⁆

end CFSG.Quasithin.Vol2.Ch11.G2Q8
