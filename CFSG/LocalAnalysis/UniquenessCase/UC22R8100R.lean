module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def Case8100ThreeR (D : Data G) (L : Fin 2 → Subgroup G) (p : ℕ) (X : Subgroup G) :
    Prop :=
  ({L 0, L 1} : Set (Subgroup G)) = {N | ∃ m ∈ D.M, N = (L 0).map (MulAut.conj m).toMonoidHom} ∧
    IsL2 (Bar2 (L 0)) 3 ∧ p = 3 ∧ 3 < evenRank G ∧
    ∃ φ : ↥D.M →* DihedralGroup 3, Function.Surjective φ ∧
      φ.ker = (X ⊔ CentOverO2 D.M X).subgroupOf D.M

@[expose] def Case8100FourR (D : Data G) (L : Fin 2 → Subgroup G) (p : ℕ) (X : Subgroup G) :
    Prop :=
  ({L 0, L 1} : Set (Subgroup G)) = {N | ∃ m ∈ D.M, N = (L 0).map (MulAut.conj m).toMonoidHom} ∧
    IsSz (Bar2 (L 0)) 5 ∧ p = 5 ∧ 3 < evenRank G ∧
    ∃ φ : ↥D.M →* DihedralGroup 5, Function.Surjective φ ∧
      φ.ker = (X ⊔ CentOverO2 D.M X).subgroupOf D.M

@[expose] def R8100R (D : Data G) : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X : Subgroup G),
    Hyp8100 D L n r p A X →
      IsStronglyPEmbedded r D.M ∨ Case8100Two D L n r p A X ∨ Case8100ThreeR D L p X ∨
        Case8100FourR D L p X

@[expose] def R8101R (D : Data G) : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X : Subgroup G),
    Hyp8100 D L n r p A X → (Case8100ThreeR D L p X ∨ Case8100FourR D L p X) →
      A ∈ uniqueSet D.M

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
