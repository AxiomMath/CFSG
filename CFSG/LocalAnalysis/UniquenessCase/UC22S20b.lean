module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Lie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

section Section20b

variable {G : Type} [Group G] [Finite G]

@[expose] def S20_7 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M,
    (∃ n : ℕ, 2 < n ∧ (IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsL3 (Bar2 L) n ∨ IsU3 (Bar2 L) n ∨
      LieModel (Bar2 L) .PSL 4 2 n ∨ IsU4 (Bar2 L) n ∨ IsG2 (Bar2 L) n ∨ Is3D4 (Bar2 L) n ∨
      LieModel (Bar2 L) .twistedF4 0 2 n ∨ IsSp4 (Bar2 L) n ∨ IsSL3 (Bar2 L) n ∨
      IsSU3 (Bar2 L) n ∨ LieModel (Bar2 L) .PSp 3 2 n ∨ IsOmega8m (Bar2 L) n)) ∨
    IsU4 (Bar2 L) 2 ∨ IsU5 (Bar2 L) 2 ∨ IsOmega8m (Bar2 L) 2 ∨ Is3D4 (Bar2 L) 2 ∨
    Is3D4 (Bar2 L) 1 ∨
    (∃ n : ℕ, 2 < n ∧ IsSzL2Product (Bar2 L) n) ∨
    IsSU3CentralSquare (Bar2 L)

@[expose] def MinTInvParabolic (T M L P : Subgroup G) : Prop :=
  Minimal (fun Q : Subgroup G => ParabolicOf L Q ∧ T ≤ normalizer (Q : Set G) ∧ ¬ Q ≤ M) P

@[expose] def S20_9 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M, ∀ K : Subgroup G,
    (K ∈ calLLow D.T D.M ∧ K ≤ L) ↔ ∃ P : Subgroup G, MinTInvParabolic D.T D.M L P ∧ K = Hinf P

@[expose] def S20_10 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calLLow D.T D.M,
    (∃ n : ℕ, IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) ∨
    (∃ L₁ L₂ : Subgroup G, L₁ ∈ calC L ∧ L₂ ∈ calC L ∧ L = L₁ ⊔ L₂ ∧ L₁ ≠ L₂ ∧
      (∃ t ∈ D.T, L₂ = L₁.map (MulAut.conj t).toMonoidHom) ∧
      ∃ n : ℕ, ∀ L' ∈ ({L₁, L₂} : Set (Subgroup G)),
        IsSz (Bar2 L') n ∨ IsL2 (Bar2 L') n ∨ (n = 3 ∧ IsSU3 (Bar2 L') 3)) ∨
    (∃ n : ℕ, (IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n) ∧ ∃ t ∈ D.T, ActsNontrivOnDiagram L t)

end Section20b

end CFSG.LocalAnalysis.UniquenessCase.UC22
