module

public import CFSG.RankThree.GF2n.Tim81.Sec8.Reduction

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.Sec15Final
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

@[expose] def Sec8RankOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ (M V : Subgroup G), Hyp M V → 4 ≤ Nat.card V →
      WeaklyClosedIn V (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn V M →
      (∀ H : Subgroup G, ¬ IsHMember M V H) → Sec8SylowData M →
      ((∃ n : ℕ, 1 ≤ n ∧ (Nonempty (G ≃* projSL 2 (GaloisField 2 n)) ∨
          Nonempty (G ≃* projSU 3 2 n))) ∨
        (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
          Nonempty (G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group))) → False

@[expose] def Sec8L3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ (M V : Subgroup G), Hyp M V → 4 ≤ Nat.card V →
      WeaklyClosedIn V (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn V M →
      (∀ H : Subgroup G, ¬ IsHMember M V H) → Sec8SylowData M →
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* projSL 3 (GaloisField 2 n))) → False

@[expose] def Sec8Sp4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ (M V : Subgroup G), Hyp M V → 4 ≤ Nat.card V →
      WeaklyClosedIn V (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn V M →
      (∀ H : Subgroup G, ¬ IsHMember M V H) → Sec8SylowData M →
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* projSp 2 (GaloisField 2 n))) → False

@[expose] def Sec8SmallRankStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ (M V : Subgroup G), Hyp M V → 4 ≤ Nat.card V →
      WeaklyClosedIn V (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn V M →
      (∀ H : Subgroup G, ¬ IsHMember M V H) → Sec8SylowData M →
      (∀ R : Subgroup G, IsPGroup 2 R →
        ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = R) → False

theorem sec8Statement_of_pushingUp (hPU : PushingUpCorollary) (h1 : Sec8RankOneStatement)
    (h2 : Sec8L3Statement) (h3 : Sec8Sp4Statement) (h4 : Sec8SmallRankStatement) :
    Sec8Statement := by
  intro G _ _ _ hnonab hK hchar M V hHyp h4c hwcQ hnwc
  by_contra hno
  have hempty : ∀ H : Subgroup G, ¬ IsHMember M V H := fun H hH => hno ⟨H, hH⟩
  obtain ⟨hsyl, hout⟩ := sec8_reduction hPU hnonab hK hchar hHyp hempty
  rcases hout with ⟨n, hn, hL2 | hU3 | hL3 | hSp⟩ | hSz | hrk
  · exact h1 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl
      (Or.inl ⟨n, hn, Or.inl hL2⟩)
  · exact h1 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl
      (Or.inl ⟨n, hn, Or.inr hU3⟩)
  · exact h2 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl ⟨n, hn, hL3⟩
  · exact h3 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl ⟨n, hn, hSp⟩
  · exact h1 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl (Or.inr hSz)
  · exact h4 G hnonab hK hchar M V hHyp h4c hwcQ hnwc hempty hsyl hrk

end CFSG.RankThree.GF2n.Tim81
