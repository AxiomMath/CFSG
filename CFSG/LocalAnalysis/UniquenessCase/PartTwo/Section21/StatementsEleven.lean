module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def W2111 (X : Type) [Group X] (θ : MulAut X) : Prop :=
  ((∃ a, IsSp4 X a) ∧ θ ∉ (MulAut.conj : X →* MulAut X).range) ∨
  ((∃ a, IsU3 X a) ∧ θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup X)

@[expose] def S21_11N (D : Data G) (Ch : Choice2011 G)
    (W : ∀ (X : Type) [Group X], MulAut X → Prop) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal → ∀ b ∈ c.B,
    b ∈ normalizer (L : Set G) →
    ∀ θ : MulAut (BarInf L ⧸ Subgroup.center (BarInf L)), InducedQuotInf L b θ → W _ θ →
      ∃ n : ℕ, IsL2 (BarInf L) n ∨ IsSz (BarInf L) n

@[expose] def KOutDiagU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (a : ℕ), IsU3 X a → ∀ α β : MulAut X,
    α * β * α⁻¹ * β⁻¹ ∈ CFSG.ASVolI.ChA.innDiagSubgroup X

@[expose] def KFieldCent : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (a r : ℕ), IsSp4 X a → r.Prime → r ≠ 2 →
      ∀ θ : MulAut X, orderOf θ = r → θ ∉ (MulAut.conj : X →* MulAut X).range →
        r ∣ a ∧ ∃ x : X, orderOf x = 3 ∧ θ x = x) ∧
    (∀ (X : Type) [Group X] [Finite X] (a r : ℕ), IsU3 X a → r.Prime → r ≠ 2 →
      ∀ θ : MulAut X, orderOf θ = r → θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup X →
        r ∣ a ∧ ∃ x : X, orderOf x = 3 ∧ θ x = x)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
