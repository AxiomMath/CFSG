module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaMinus)

@[expose] def Shape207 (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n ∨ IsL3 X n ∨ IsU3 X n ∨
      LieModel X .PSL 4 2 n ∨ IsU4 X n ∨ IsG2 X n ∨ Is3D4 X n ∨
      LieModel X .twistedF4 0 2 n ∨ IsSp4 X n ∨ IsSL3 X n ∨
      IsSU3 X n ∨ LieModel X .PSp 3 2 n ∨ IsOmega8m X n)) ∨
    IsU4 X 2 ∨ IsU5 X 2 ∨ IsOmega8m X 2 ∨ Is3D4 X 2 ∨
    Is3D4 X 1 ∨
    (∃ n : ℕ, 2 < n ∧ IsSzL2Product X n) ∨
    IsSU3CentralSquare X

theorem shape207_of_s20_7 {G : Type} [Group G] [Finite G] {D : Data G} (h207 : S20_7 D)
    (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M) : Shape207 (Bar2 L) :=
  h207 h1930 L hL

@[expose] def KDiag : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Shape207 X →
    ∀ θ : MulAut X, Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ P : Subgroup X, IsParabolicTwo X P → (S : Subgroup X) ≤ normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P

@[expose] def KOrdBorel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 2 ≤ m →
    (IsSz X m ∨ IsL2 X m ∨ IsSU3 X m ∨ IsSL3 X m ∨ IsSp4 X m ∨ IsOmegaMinus X 4 m) →
    ∀ r : ℕ, r.Prime → 3 < r → ¬ r ∣ m → ¬ r ∣ 2 ^ (2 * m) - 1 →
    ∀ (S : Sylow 2 X) (θ : MulAut X), θ ^ r = 1 →
      (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) → θ = 1

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
