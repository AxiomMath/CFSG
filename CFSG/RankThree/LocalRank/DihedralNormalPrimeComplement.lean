module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.LocalRank

theorem normalizer_le_normalizer_inf_centralizer {G : Type*} [Group G] (B : Subgroup G) :
    Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((B ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro v hv z hz
  obtain ⟨hzB, hzC⟩ := Subgroup.mem_inf.mp hz
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hv z).mp hzB, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : v⁻¹ * u * v⁻¹⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (inv_mem hv) u).mp hu
  rw [inv_inv] at hu'
  have key := Subgroup.mem_centralizer_iff.mp hzC _ hu'
  calc u * (v * z * v⁻¹) = v * ((v⁻¹ * u * v) * z) * v⁻¹ := by group
    _ = v * (z * (v⁻¹ * u * v)) * v⁻¹ := by rw [key]
    _ = v * z * v⁻¹ * u := by group

end CFSG.RankThree.LocalRank
