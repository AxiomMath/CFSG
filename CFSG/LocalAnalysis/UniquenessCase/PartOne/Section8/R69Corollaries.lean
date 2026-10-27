module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

variable {G : Type} [Group G] [Finite G]

theorem commute_of_mem_upperCentral_two_of_R6_9 {D : Data G}
    (h69 : R6_9 D) (hsub : D.sig ⊆ D.sig1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E : Subgroup G} (hE : E ≤ D.M) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ D.M)
    {p : ℕ} (hp : p.Prime) {X P : Subgroup G} (hX : X ≤ D.M) (hXcard : Nat.card X = p)
    (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hnotN : ¬ Subgroup.normalizer (X : Set G) ≤ D.M)
    (hP : P ≤ D.M) (hPp : IsPGroup p P) (hXP : X ≤ P)
    {y : G} (hy : y ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype)
    {x : G} (hx : x ∈ X) :
    x * y = y * x :=
  (h69 hsub r hr hr2 E hE hEel hEcard hΓ p X hp hX hXcard hEX hnotN P hP hPp hXP).2.1 y hy x hx

theorem le_center_of_le_upperCentral_two_of_R6_9 {D : Data G}
    (h69 : R6_9 D) (hsub : D.sig ⊆ D.sig1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {E : Subgroup G} (hE : E ≤ D.M) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hΓ : rankThreeGamma 1 r E ≤ D.M)
    {p : ℕ} (hp : p.Prime) {X P : Subgroup G} (hX : X ≤ D.M) (hXcard : Nat.card X = p)
    (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hnotN : ¬ Subgroup.normalizer (X : Set G) ≤ D.M)
    (hP : P ≤ D.M) (hPp : IsPGroup p P) (hXP : X ≤ P)
    (hXZ2 : X ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype) :
    X ≤ (Subgroup.center ↥P).map P.subtype :=
  (h69 hsub r hr hr2 E hE hEel hEcard hΓ p X hp hX hXcard hEX hnotN P hP hPp hXP).2.2 hXZ2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
