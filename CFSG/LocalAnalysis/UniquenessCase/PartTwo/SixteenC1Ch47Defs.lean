module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1ChoiceDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_47_O1_ne (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 → (calO 1 D.M V₀ V).Nonempty

@[expose] def R16_47_card_le (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∀ x : IntMod V hV, Setup1645 D V hV x → Chosen1647 D V₀ V x.val →
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) →
        Concl1646 L x.val → Nat.card ↥V ≤ 2 * Nat.card ↥(uOne V x.val)

@[expose] def R16_47_ord_gap (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∀ x : IntMod V hV, Setup1645 D V hV x → Chosen1647 D V₀ V x.val →
        IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) →
        Concl1646 L x.val → Nat.card ↥V = 2 * Nat.card ↥(uOne V x.val) →
          ∀ h ∈ centralizer ({x.val} : Set G), conjSubgroup V h ∈ calOStar 1 D.M V₀ V →
            ∀ w ∈ V, w ∉ pCoreOf 2 (centralizer ({x.val} : Set G)) →
              ⁅w, h⁻¹ * w * h⁆ ∉ pCoreOf 2 (centralizer ({x.val} : Set G)) →
                ∃ d ∈ ({3, 5, 17} : Set ℕ),
                  (w * (h⁻¹ * w * h)) ^ d ∈ pCoreOf 2 (centralizer ({x.val} : Set G))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
