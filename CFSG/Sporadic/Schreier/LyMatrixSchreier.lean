module

public import CFSG.Sporadic.Schreier.LyGeneration
public import CFSG.Sporadic.SchreierLemmas.LocalRestrictionSchreier

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.SchreierLemmas CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms

theorem center_map_lySylow :
    (Subgroup.center (lySylow : Subgroup J)).map (lySylow : Subgroup J).subtype =
      Subgroup.zpowers lyz := by
  change (Subgroup.center lyS).map lyS.subtype = _
  rw [center_lyS, MonoidHom.map_zpowers]
  rfl

theorem lyC_eq_centralizer_center :
    lyC = Subgroup.centralizer
    (((Subgroup.center (lySylow : Subgroup J)).map (lySylow : Subgroup J).subtype : Subgroup J) :
      Set J) := by
  rw [center_map_lySylow, full_involution_centralizer.1]
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hz : lyz ∈ Subgroup.centralizer ({x} : Set J) := by
      rw [Subgroup.mem_centralizer_singleton_iff]; exact h.symm
    have := (Subgroup.zpowers_le.2 hz) hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  · intro h
    exact (h lyz (Subgroup.mem_zpowers lyz)).symm

theorem finite_mulAut_lyC : Finite (MulAut lyC) :=
  Finite.of_injective (fun f : MulAut lyC => (f : lyC → lyC)) DFunLike.coe_injective

theorem matrix_schreier :
    Group.IsSolvable (Outer J) := by
  have hCsolv : Group.IsSolvable (pointwiseFixingAut ((lySylow : Subgroup J).subgroupOf lyC)) := by
    change Group.IsSolvable (pointwiseFixingAut (lyS.subgroupOf lyC))
    have := finite_mulAut_lyC
    have := isPGroup_fixes_S.isNilpotent
    infer_instance
  exact local_restriction_Schreier_criterion (G := J) lySylow lyQ (by exact lyQ_le) lyC
    (by exact lyC_eq_centralizer_center) lyN rfl (by exact intrinsic_local_generation.2.2)
    (by exact isSolvable_mulAut_lyS) (by exact hCsolv) (by exact local_automorphism_bounds.2.2)

end CFSG.Sporadic.LySchreier
