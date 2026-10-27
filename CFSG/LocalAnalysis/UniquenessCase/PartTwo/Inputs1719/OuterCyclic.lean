module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.Background.QuasisimpleSp4G2Facts
public import CFSG.ClassicalInvolution.SmallCases.NobqU3
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isCyclic_outer_of_lieModel_PSp4 {Y : Type} [Group Y] {n : ℕ}
    (h : LieModel Y .PSp 2 2 n) : IsCyclic (Outer Y) :=
  CFSG.Quasithin.isCyclic_outer_of_isPSp4 (n := n) (h.statedClassicalModel (by decide))

theorem isCyclic_outer_of_lieModel_G2
    {Y : Type} [Group Y] {n : ℕ} (h : LieModel Y .G2 0 2 n) : IsCyclic (Outer Y) :=
  CFSG.Quasithin.isCyclic_outer_of_isG2 (n := n)
    ((LieModel.chevalleyExceptional_iff (t := .G2) (p := 2) (f := n) (by decide)).1 h).2

theorem isCyclic_outer_of_lieModel_PSU4 {Y : Type} [Group Y] {n : ℕ}
    (h : LieModel Y .PSU 4 2 n) : IsCyclic (Outer Y) := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := (h.statedClassicalModel (by decide)).2
  letI := hKf
  letI := hKfin
  have hn1 : 1 ≤ n := (h.admissible).2.1
  have hcard : Nat.card K = 2 ^ (2 * n) := by
    rw [hKcard, pow_two, ← pow_add]
    congr 1
    omega
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn1, hcard⟩
  have hodd : Odd (2 ^ n + 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_add_one
      (f := n) (n := 1) hn1 le_rfl
  have hgcd : Nat.gcd 4 (2 ^ n + 1) = 1 :=
    CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one hodd
  have hcyc : IsCyclic (Outer (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hdata 4)) :=
    CFSG.ClassicalInvolution.Nobq.isCyclic_outer_unitaryPSU_of_gcd_eq_one hdata
      (n := 4) (by norm_num) (by norm_num) hgcd
  exact GL83.I713.isCyclic_outer_congr
    (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hdata (n := 4) (by norm_num)).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
