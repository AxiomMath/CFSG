module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6A2
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Family
public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81 (FF81Sec5 β')
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

local instance am6NeZeroRankP : NeZero Tag.F4.rank := ⟨by decide⟩

section LSide


def LSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ →
    ∃ θP : ↥(B3Levi (GaloisField 2 1)) →* G, Function.Injective θP ∧ θP.range = L ∧
      pimg (GaloisField 2 1) θP (Lv (GaloisField 2 1) {0}) =
        Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ∧
      (∃ t₁ : G, pimg (GaloisField 2 1) θP (Lv (GaloisField 2 1) {2}) =
          Subgroup.closure ({b₁, t₁} : Set G) ∧
        t₁ * b₁ * t₁⁻¹ = b₁⁻¹ ∧ t₁ * (b₂ * b₃) = (b₂ * b₃) * t₁) ∧
      Nat.card ↥(L ⊓ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G))) = 36 ∧
      Nat.card ↥(L ⊓ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ⊔
        pimg (GaloisField 2 1) θP (Lv (GaloisField 2 1) {2}))) = 6

end LSide

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
