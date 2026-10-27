module

public import CFSG.Sporadic.Fi24I301.Elements
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Elem5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenFour
public import CFSG.LargeExtraspecial.BridgeNat
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
  CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.Sporadic.Fi24 (J)


noncomputable abbrev RJ : Subgroup J := fi24QC.map fi24C.subtype

theorem RJ_le_C : RJ ≤ fi24C := Subgroup.map_subtype_le _

theorem fi24R2_mem_RJ : fi24R2 ∈ RJ := by
  refine ⟨⟨fi24R2, fi24R2_mem_C⟩, ?_, rfl⟩
  show fi24Rho _ ∈ fi24N
  rw [fi24Rho_z]
  exact Subgroup.one_mem _

theorem comm_fi24R2_of_mem_C {g : J} (hg : g ∈ fi24C) : g * fi24R2 = fi24R2 * g :=
  (Subgroup.mem_centralizer_singleton_iff (G := J)).1 hg

theorem fi24_hR : IsExtraSpec2 RJ ∧ Nat.card RJ = 2 ^ 13 := by
  haveI := fi24C_finite
  haveI := fi24QC_extraspecial
  have hQC : timmesfeldIsExtraspecial ↥fi24QC :=
    (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2
      (CFSG.IsExtraspecial.isExtraspecialPGroup (p := 2) (P := ↥fi24QC))
  have key := CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (H := ↥fi24QC) (K := ↥RJ)
  refine ⟨key (fi24QC.equivMapOfInjective fi24C.subtype fi24C.subtype_injective) hQC, ?_⟩
  rw [Subgroup.card_map_of_injective fi24C.subtype_injective, card_fi24QC]

theorem fi24C_le_normalizer_RJ : fi24C ≤ Subgroup.normalizer (RJ : Set J) := by
  haveI := fi24QC_normal
  have h := Subgroup.le_normalizer_map (H := fi24QC) fi24C.subtype
  rw [Subgroup.normalizer_eq_top] at h
  intro g hg
  exact h ⟨⟨g, hg⟩, Subgroup.mem_top _, rfl⟩

theorem normalizer_RJ_le : Subgroup.normalizer (RJ : Set J) ≤ fi24C := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff (G := J)]
  exact H301B.comm_of_mem_normalizer fi24_hR.1 fi24R2_mem_RJ
    (fun r hr => comm_fi24R2_of_mem_C (RJ_le_C hr)) fi24R2_ne_one hg

noncomputable abbrev B1J : Subgroup J := Subgroup.closure {xJ 0, xJ 1, xJ 2, xJ 3, xJ 4}

theorem B1J_le_C : B1J ≤ fi24C := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl | rfl | rfl) <;> exact xJ_mem _

theorem fi24_hB : IsElemAbelian 3 B1J ∧ Nat.card B1J = 3 ^ 5 := by
  have hc : ∀ i < 5, ∀ j < 5, Commute (xJ i) (xJ j) := fun i hi j hj => xJ_comm hi hj
  exact isElemAbelian_closure_five (hc 0 (by norm_num) 1 (by norm_num))
    (hc 0 (by norm_num) 2 (by norm_num)) (hc 0 (by norm_num) 3 (by norm_num))
    (hc 0 (by norm_num) 4 (by norm_num)) (hc 1 (by norm_num) 2 (by norm_num))
    (hc 1 (by norm_num) 3 (by norm_num)) (hc 1 (by norm_num) 4 (by norm_num))
    (hc 2 (by norm_num) 3 (by norm_num)) (hc 2 (by norm_num) 4 (by norm_num))
    (hc 3 (by norm_num) 4 (by norm_num)) (xJ_pow_three (by norm_num))
    (xJ_pow_three (by norm_num)) (xJ_pow_three (by norm_num)) (xJ_pow_three (by norm_num))
    (xJ_pow_three (by norm_num)) xJ_indep

theorem fi24_hd : dJ ∈ B1J ∧ dJ ≠ 1 :=
  ⟨Subgroup.subset_closure (Set.mem_insert _ _), dJ_ne_one⟩

theorem nonempty_jEquiv :
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  exact ⟨CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans b⟩

theorem catalogIs_J :
    catalogIs J (sporIs .Fi24Prime) := by
  obtain ⟨e⟩ := nonempty_jEquiv
  exact ⟨.sporadic .Fi24Prime, rfl, ⟨e⟩⟩

end CFSG.Sporadic.Fi24I301
