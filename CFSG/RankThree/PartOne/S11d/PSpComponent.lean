module

public import CFSG.RankThree.PartOne.S11d.PSpCyclic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OddIso CFSG.RankThree.PartOne.KCSpFull
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary Polynomial

variable {r p : ℕ} {K : Type} [Field K]

theorem mem_spFixedFactor_of_fix {a g : StatedSp r K} (hg : g * a = a * g)
    (hW : ∀ w ∈ LinearMap.range (spEnd a - 1), spEnd g w = w) : g ∈ spFixedFactor a := by
  rw [spFixedFactor, mem_spSupported]
  refine ⟨hg, fun k hk hk1 v hv => hW v ?_⟩
  have hk1' : k ≠ X - 1 := fun h => hk1 (by rw [h]; exact Set.mem_singleton _)
  obtain ⟨w', hw'⟩ := exists_sub_one_apply_eq_of_mem_primaryComponent (spEnd a)
    (irreducible_of_mem_primaryFactors hk) (monic_of_mem_primaryFactors hk) hk1' hv
  exact ⟨w', hw'⟩

theorem spFixedFactor_conj {a g f : StatedSp r K} (hg : g ∈ Subgroup.centralizer {a})
    (hf : f ∈ spFixedFactor a) : g * f * g⁻¹ ∈ spFixedFactor a := by
  have hgu : spLin r K g ∈ unitaryCentralizer (spForm r K) (spLin r K a) := by
    refine ⟨spLin_mem g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [← map_mul, ← map_mul, this]
  have hconj := conj_mem_supportedUnitary hgu
    (show spLin r K f ∈ supportedUnitary (spForm r K) (spLin r K a) {X - 1} from hf)
  change spLin r K (g * f * g⁻¹) ∈ supportedUnitary (spForm r K) (spLin r K a) {X - 1}
  rw [map_mul, map_mul, map_inv]
  exact hconj


theorem two_mem_spFixedFactor [Finite K] [CharP K 2] {a : StatedSp r K} (hodd : Odd p)
    (hap : a ^ p = 1) (hcyc : IsCyclicOn (spEnd a) (LinearMap.range (spEnd a - 1)))
    {g : StatedSp r K}
    (hg : g ∈ Subgroup.centralizer {a}) {k : ℕ} (hgk : g ^ 2 ^ k = 1) : g ∈ spFixedFactor a := by
  have hÂp : spEnd a ^ p = 1 := by rw [← spEnd_pow', hap, spEnd_one]
  have hga : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hcomm : spEnd g * spEnd a = spEnd a * spEnd g := spEnd_comm_iff.mp hga
  have hgk' : spEnd g ^ (2 ^ k) = 1 := by rw [← spEnd_pow', hgk, spEnd_one]
  exact mem_spFixedFactor_of_fix hga (eq_id_on_range_of_two_pow hodd hÂp hcyc hcomm hgk')

theorem spEnd_injective' (g : StatedSp r K) : Function.Injective (spEnd g) := by
  intro x y h
  have h1 := congrArg (spEnd g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one,
    Module.End.one_apply, Module.End.one_apply] at h1

theorem scalar_on_fix_of_centralizes {a g : StatedSp r K}
    (hgD : g ∈ Subgroup.centralizer (spFixedFactor a : Set (StatedSp r K))) :
    ∃ l : K, ∀ u ∈ LinearMap.ker (spEnd a - 1), spEnd g u = l • u := by
  refine exists_scalar_of_forall_eigenvector (W := LinearMap.ker (spEnd a - 1)) (F := spEnd g)
    fun u hu => ?_
  by_cases hu0 : u = 0
  · exact ⟨0, by rw [hu0, map_zero, smul_zero]⟩
  have hua : spEnd a u = u := mem_ker_sub_one_iff.mp hu
  obtain ⟨-, c, -, hc⟩ := eq_refl_of_commute_transvections (B := spForm r K)
    spForm_nondegenerate (σ := RingEquiv.refl K) (F := spEnd g) (map_add _)
    (fun c v => by simp) (spEnd_injective' g) hu0 (fun t y => by
      have hmem := spTransvection_mem_spFixedFactor hua t
      have h1 := (Subgroup.mem_centralizer_iff.mp hgD) _ hmem
      have h2 := congrArg (fun f : Module.End K _ => f y) (spEnd_comm_iff.mp h1.symm)
      simp only [Module.End.mul_apply, spEnd_spTransvection] at h2
      exact h2)
  exact ⟨c, hc⟩

end CFSG.RankThree.PartOne
