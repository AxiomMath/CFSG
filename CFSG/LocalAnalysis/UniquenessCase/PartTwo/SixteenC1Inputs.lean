module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def hConj (H X : Subgroup G) : Subgroup G :=
  ⨆ h : ↥H, conjSubgroup X (h : G)

@[expose] def IsParabolic2In (L P : Subgroup G) : Prop :=
  P ≤ L ∧ P ≠ L ∧ CFSG.pCore 2 ↥L ≤ P.subgroupOf L ∧
    ∃ S : Sylow 2 (Bar2 L),
      (S : Subgroup (Bar2 L)) ≤ (P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))

@[expose] noncomputable def R925 (D : Data G) : Prop :=
  ∀ L P X H Y : Subgroup G, L ∈ calC D.M → IsU4 (Bar2 L) 1 → IsParabolic2In L P →
    X = perfectCore P → X ≠ ⊥ → ¬ H ≤ D.M → Fstar H = pCoreOf 2 H → Y = perfectCore (H ⊓ X) →
    X = Y ⊔ pCoreOf 2 X → pCoreOf 2 Y ≠ ⊥ → Odd (D.M.relIndex H) → D.sig = {3} →
    CFSG.Open.pRank 3 D.M = 3 →
      IsSL2Prime ↥(starImg H Y) 5 ∧
        (IsL3Five ↥(starImg H (hConj H Y)) ∨
          EqTimesOdd (starImg H Y) (starImg H (hConj H Y)))

@[expose] noncomputable def R925Used (D : Data G) : Prop :=
  ∀ (L P X H Y : Subgroup G) (z : G), L ∈ calC D.M → IsU4 (Bar2 L) 1 → IsParabolic2In L P →
    X = perfectCore P → X ≠ ⊥ → ¬ H ≤ D.M → Fstar H = pCoreOf 2 H → Y = perfectCore (H ⊓ X) →
    X = Y ⊔ pCoreOf 2 X → pCoreOf 2 Y ≠ ⊥ → Odd (D.M.relIndex H) → D.sig = {3} →
    CFSG.Open.pRank 3 D.M = 3 →
    z ≠ 1 → z ^ 2 = 1 → H = centralizer ({z} : Set G) →
    CFSG.Open.pRank 3 H = 1 → (∀ q : ℕ, q.Prime → 3 < q → CFSG.Open.pRank q H ≤ 2) →
    IsSylowIn 2 (D.T ⊓ H) H → IsE16A5 ↥(starImg L Y) →
      IsSL2Prime ↥(starImg H Y) 5 ∧
        (IsL3Five ↥(starImg H (hConj H Y)) ∨
          EqTimesOdd (starImg H Y) (starImg H (hConj H Y)))

theorem r925Used_of_r925 {D : Data G} (h : R925 D) : R925Used D :=
  fun L P X H Y _ hL hU4 hP hX hXne hHM hF hY hXY hO2 hodd hsig hm3 _ _ _ _ _ _ _ =>
    h L P X H Y hL hU4 hP hX hXne hHM hF hY hXY hO2 hodd hsig hm3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
