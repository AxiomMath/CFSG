module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def P18_6_3e (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∃ f : ℕ,
    (IsSp4 (Bar2 (conjClosure D.M L)) f ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (π : ↥(StatedSp 2 K) →*
            ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))),
          Nat.card K = 2 ^ f ∧
            Inputs1719.SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedSp 2 K))
              (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π) ∨
      (IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 6 f ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
          (π : ↥(StatedOmega (StatedQuadMinus 3 K b c)) →*
            ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))),
          Nat.card K = 2 ^ f ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
            Inputs1719.SumOfNatVia
              (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c)))
              (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π) ∨
      (Even f ∧ IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 (f / 2) ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
          (π : ↥(StatedOmega (StatedQuadMinus 2 K b c)) →*
            ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))),
          Nat.card K = 2 ^ (f / 2) ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
            Inputs1719.SumOfNatVia
              (CFSG.Quasithin.FFModel.nat (StatedOmega (StatedQuadMinus 2 K b c)))
              (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π)

@[expose] def P18_6_6 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  IsSUn ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 2 ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (π : ↥(StatedSU 4 (2 ^ 2) K) →*
        ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L))),
      Nat.card K = (2 ^ 2) ^ 2 ∧
        Inputs1719.SumOfNatVia (CFSG.Quasithin.FFModel.nat (StatedSU 4 (2 ^ 2) K))
          (barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) ⊤ ⊥ 2 π

@[expose] def R18_7bAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ MBarGT D.M V₀ V
    (max (bBar (conjClosure D.M L) D.M V₀ V h.hyp125.isElemAbelian) (S17.nOf L) + 2)

@[expose] def R18_6bAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  MBarGT D.M V₀ V 3 → R18_7bAt D V₀ V p L h →
    P18_6_2 D V₀ V p L h ∨ P18_6_3e D V₀ V p L h ∨ P18_6_4 D V₀ V p L h ∨
      P18_6_5 D V₀ V p L h ∨ P18_6_6 D V₀ V p L h

@[expose] def Gap_18_9b (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ¬ P18_6_6 D V₀ V p L h

theorem P18_6_3e.toP18_6_3 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    {h : Hyp18 D V₀ V p L} (h3 : P18_6_3e D V₀ V p L h) :
    P18_6_3 D V₀ V p L h := by
  obtain ⟨f, ⟨h1, K, hKf, hKfin, π, hK, I, hI1, hI2, hI3, hI4⟩ |
      ⟨h1, K, hKf, hKfin, b, c, π, hK, hbc, I, hI1, hI2, hI3, hI4⟩ |
      ⟨h0, h1, K, hKf, hKfin, b, c, π, hK, hbc, I, hI1, hI2, hI3, hI4⟩⟩ := h3
  · exact ⟨f, Or.inl ⟨h1, I, hI1, hI2, hI3, fun i => ⟨⟨2, rfl⟩, K, hKf, hKfin, hK, π, hI4 i⟩⟩⟩
  · exact ⟨f, Or.inr (Or.inl ⟨h1, I, hI1, hI2, hI3,
      fun i => ⟨⟨3, rfl⟩, K, hKf, hKfin, b, c, hK, hbc, π, hI4 i⟩⟩)⟩
  · exact ⟨f, Or.inr (Or.inr ⟨h0, h1, I, hI1, hI2, hI3,
      fun i => ⟨⟨2, rfl⟩, K, hKf, hKfin, b, c, hK, hbc, π, hI4 i⟩⟩)⟩

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
