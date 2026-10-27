module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal Matrix SpecialLinear

@[expose] def GGTypeACrossLiftInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G) (y₃ : G) (K₃ : Subgroup G),
    GGTypeANbrCfg p B Bs x L D J n f y K → GGTypeANbr p B Bs x L D J n f y₃ K₃ → p ∣ n + 3 →
    ¬ K₃ ≤ L ⊔ K →
    ∃ φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      φ₃.range = K₃ ∧
      φ₃.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₃.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ j : Fin n, j.val + 1 = n →
        (φ₃ (weylRep n (GaloisField 2 f) j) * φ₂ (weylRep n (GaloisField 2 f) j)) ^ 3 = 1 ∧
        ∀ g, φ₂ (weylRep n (GaloisField 2 f) j) * φ₃ (weylRep n (GaloisField 2 f) j) *
            φ₂ (weylRep n (GaloisField 2 f) j) * φ₁ g =
          φ₁ g * (φ₂ (weylRep n (GaloisField 2 f) j) * φ₃ (weylRep n (GaloisField 2 f) j) *
            φ₂ (weylRep n (GaloisField 2 f) j))

@[expose] def GGTypeACorankTwoExInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGConfig p B Bs x L D J → GGOpAutTrivial p Bs →
    GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → GGTypeANbr p B Bs x L D J n f y K →
    p ∣ n + 3 → (∃ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' ∧ ¬ K' ≤ L ⊔ K) →
    ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      ∃ T₁ T₂ : G, T₁ ∈ ggG0 p B x L D J ∧ T₂ ∈ ggG0 p B x L D J ∧
        GGTypeATwoEndNodes φ₁ T₁ T₂ ∧
        ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
          K' ≤ L ⊔ L.map (MulAut.conj T₁).toMonoidHom ⊔
            L.map (MulAut.conj (T₂ * T₁)).toMonoidHom ⊔
              L.map (MulAut.conj (T₁ * T₂ * T₁)).toMonoidHom

end CFSG.StandardType
