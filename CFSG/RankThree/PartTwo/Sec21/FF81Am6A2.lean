module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Family
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.Open.StatedDefs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

local instance am6NeZeroRankA2 : NeZero Tag.F4.rank := ⟨by decide⟩

section A2


variable (K : Type) [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]

noncomputable def pimg {G : Type} [Group G] (θP : ↥(B3Levi K) →* G)
    (A : Subgroup ↥(adjointGroup .F4 K)) : Subgroup G :=
  (A.subgroupOf (B3Levi K)).map θP

def A2Piece : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (θP : ↥(B3Levi K) →* G), Function.Injective θP →
    ∀ M K₀ : Subgroup G, StatedClassicalModel M .PSp 3 2 1 →
    (∀ m ∈ M, ∀ x ∈ pimg K θP (Lv K {0}), Commute m x) →
    pimg K θP (Lv K {2}) ≤ M →
    IsLnq 3 2 1 (CenS (pimg K θP (Lv K {0, 1}))) → CenS (pimg K θP (Lv K {0, 1})) ≤ M →
    K₀ ≤ CenS (pimg K θP (Lv K {0, 1})) → Nonempty (↥K₀ ≃* Equiv.Perm (Fin 3)) →
    (∀ x ∈ K₀, ∀ y ∈ pimg K θP (Lv K {2}), Commute x y) →
    Nat.card ↥(M ⊓ CenS K₀) = 36 → Nat.card ↥(M ⊓ CenS (pimg K θP (Lv K {2}))) = 36 →
    ∃ θA : ↥(Lv K {2, 3}) →* G,
      (∀ (x : ↥(adjointGroup .F4 K)) (hx : x ∈ Lv K {2}),
        θA ⟨x, Lv_two_le_A hx⟩ = θP ⟨x, Lv_two_le_P hx⟩) ∧
      (∀ (x : ↥(adjointGroup .F4 K)) (hx : x ∈ Lv K {3}),
        θA ⟨x, Lv_three_le_A hx⟩ ∈ CenS (pimg K θP (Lv K {0, 1}))) ∧
      θA.range ≤ M

end A2

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
