module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch5Sec1L34U4Vertex
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_le_derivedSeriesOf
  le_perfectCore_of_perfect normalizer_le_normalizer_perfectCore)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private noncomputable def alphaP :
    ↥(perfectCore (parP h)) →* Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  (rhoF h).comp (Subgroup.inclusion (perfectCore_parP_le_parH h))

private theorem alphaP_surjective (hm : 2 ≤ m) : Function.Surjective (alphaP h) := by
  intro A
  refine ⟨⟨levHom h A, levHom_range_le_perfectCore h hm ⟨A, rfl⟩⟩, ?_⟩
  exact rhoF_levHom h A

private theorem alphaP_ker (hm : 2 ≤ m) :
    (alphaP h).ker = CFSG.pCore 2 ↥(perfectCore (parP h)) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxQ := CFSG.Quasithin.H13.U4V.mem_radQ_of_rhoF_eq_one h
      (g := ⟨(x : hypSU h 2 0), perfectCore_parP_le_parH h x.2⟩) hx
    rw [← pCoreOf_perfectCore_parP h hm] at hxQ
    exact (CFSG.mem_openPCoreOf_iff x).mp hxQ
  · intro hx
    have hxQ : (x : hypSU h 2 0) ∈ radQ h := by
      rw [← pCoreOf_perfectCore_parP h hm]
      exact (CFSG.mem_openPCoreOf_iff x).mpr hx
    have hrho : rho h (x : hypSU h 2 0) = 1 := (chi_rho_of_mem_radQ h hxQ).2
    have hmap : (rhoFMat h ⟨(x : hypSU h 2 0), perfectCore_parP_le_parH h x.2⟩).map
        h.fixedField.subtype =
        (1 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype := by
      rw [Matrix.map_one _ (map_zero _) (map_one _), map_rhoFMat, hrho]
    have hmat : rhoFMat h ⟨(x : hypSU h 2 0), perfectCore_parP_le_parH h x.2⟩ = 1 :=
      Matrix.map_injective h.fixedField.subtype_injective hmap
    apply Subtype.ext
    change rhoFMat h ⟨(x : hypSU h 2 0), perfectCore_parP_le_parH h x.2⟩ =
      (1 : Matrix (Fin 2) (Fin 2) h.fixedField)
    exact hmat

noncomputable def modO2PerfectCoreParPEquivSL2 (hm : 2 ≤ m) :
    CFSG.Quasithin.ModO2 (perfectCore (parP h)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) h.fixedField :=
  (QuotientGroup.quotientMulEquivOfEq (alphaP_ker h hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (alphaP h) (alphaP_surjective h hm))

theorem isSimpleGroup_modO2_perfectCore_parP (hm : 2 ≤ m) :
    IsSimpleGroup (CFSG.Quasithin.ModO2 (perfectCore (parP h))) := by
  haveI := isSimpleGroup_sl2 h hm
  exact (modO2PerfectCoreParPEquivSL2 h hm).isSimpleGroup

theorem perfectCore_parP_eq_bot (hm : m = 1) : perfectCore (parP h) = ⊥ := by
  subst hm
  haveI := h.finite
  haveI := finite_hypSU h
  by_contra hne
  haveI : Nontrivial ↥(perfectCore (parP h)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  haveI : Group.IsPerfect ↥(perfectCore (parP h)) :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect (parP h))
  haveI : Group.IsSolvable ↥(parP h) := CFSG.Quasithin.H13.U4V.isSolvable_parP_one h
  haveI : Group.IsSolvable ↥(perfectCore (parP h)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (perfectCore_le (parP h)))
  exact Group.IsPerfect.not_isSolvable ↥(perfectCore (parP h)) inferInstance

end CFSG.Quasithin.H13.U4Par

end
