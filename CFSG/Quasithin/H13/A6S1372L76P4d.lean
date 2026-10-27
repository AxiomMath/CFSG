module

public import CFSG.Quasithin.H13.A6S1372L76P4c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

@[expose] def Lem1376OddNCA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, ∀ hH : H ∈ S.Hz, IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H →
      AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5 →
      (∃ x ∈ S.X1375, ∃ hxH : x ∈ H, ∃ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩ * y ≠
          y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
            ⟨x, hxH⟩) →
      S.L1 ≤ K

@[expose] def Lem1376OddNCBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, ∀ hH : H ∈ S.Hz, IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H →
      (∃ n, Odd n ∧ 3 ≤ n ∧ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) →
      (∃ x ∈ S.X1375, ∃ hxH : x ∈ H, ∃ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩ * y ≠
          y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
            ⟨x, hxH⟩) →
      S.L1 ≤ K

@[expose] def Lem1376OddNCL32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 →
    ∀ H : Subgroup G, ∀ hH : H ∈ S.Hz, IsElemAbelian 2 (conjClosure S.V3 H) →
    ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (K : Subgroup G), K ∈ cComp H →
      BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 1 →
      (∃ x ∈ S.X1375, ∃ hxH : x ∈ H, ∃ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH) ⟨x, hxH⟩ * y ≠
          y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
            ⟨x, hxH⟩) →
      S.L1 ≤ K

theorem lem1376L1KSmallOddNC_of (hA : Lem1376OddNCA5) (hB : Lem1376OddNCBig)
    (hL : Lem1376OddNCL32) : Lem1376L1KSmallOddNC := by
  intro G _ _ T L V S hNS hNU H hH hab _ K hK hmod hc
  rcases hmod with ⟨n, hn, hSL⟩ | h5
  · by_cases h1 : n = 1
    · subst h1
      exact hL G T L V S hNS hNU H hH hab K hK hSL hc
    · have h3 : 3 ≤ n := by
        obtain ⟨m, rfl⟩ := hn
        omega
      exact hB G T L V S hNS hNU H hH hab K hK ⟨n, hn, h3, hSL⟩ hc
  · exact hA G T L V S hNS hNU H hH hab K hK h5 hc

end CFSG.Quasithin.H13.A6
