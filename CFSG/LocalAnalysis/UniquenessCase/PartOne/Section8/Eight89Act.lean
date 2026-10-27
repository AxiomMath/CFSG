module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

theorem s889_act : S889Act := by
  intro K _ _ hperfect hA6Z3 A _ φ hφrange
  have : Group.IsPerfect K := ⟨hperfect⟩
  have : Finite ↥φ.range :=
    Finite.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  let T : Subgroup K := CFSG.pCore 2 K
  let Kbar := K ⧸ T
  let q : K →* Kbar := QuotientGroup.mk' T
  let Nbar : Subgroup Kbar := (φ.ker).map q
  have hNbarNormal : Nbar.Normal :=
    Subgroup.Normal.map (inferInstance : (φ.ker).Normal) q (QuotientGroup.mk'_surjective T)
  have hKbarQuasi : CFSG.Open.IsQuasisimple Kbar :=
    ⟨Group.isPerfect_def.mp hA6Z3.1.1, hA6Z3.1.2.1⟩
  rcases GL83.I243.normal_le_center_or_eq_top hKbarQuasi Nbar with hNbarCenter | hNbarTop
  ·
    let W : Subgroup K := (Subgroup.center Kbar).comap q
    have hWnormal : W.Normal := Subgroup.normal_comap q
    have hker_le_W : φ.ker ≤ W := fun x hx =>
      (Subgroup.mem_comap).mpr (hNbarCenter (Subgroup.mem_map_of_mem q hx))
    let ρ : K →* ↥φ.range := φ.rangeRestrict
    have hker_le_W' : ρ.ker ≤ W := by
      simpa only [ρ, MonoidHom.ker_rangeRestrict] using hker_le_W
    let V : Subgroup ↥φ.range := W.map ρ
    have hVnormal : V.Normal :=
      hWnormal.map ρ (MonoidHom.rangeRestrict_surjective φ)
    refine ⟨V, hVnormal, ?_⟩
    let ψ1 : K →* (↥φ.range) ⧸ V := (QuotientGroup.mk' V).comp ρ
    have hψ1_surj : Function.Surjective ψ1 :=
      (QuotientGroup.mk'_surjective V).comp (MonoidHom.rangeRestrict_surjective φ)
    have hker1 : ψ1.ker = W := by
      change (((QuotientGroup.mk' V).comp ρ).ker) = W
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact Subgroup.comap_map_eq_self hker_le_W'
    let ψ2 : K →* Kbar ⧸ Subgroup.center Kbar :=
      (QuotientGroup.mk' (Subgroup.center Kbar)).comp q
    have hψ2_surj : Function.Surjective ψ2 :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective T)
    have hker2 : ψ2.ker = W := by
      change (((QuotientGroup.mk' (Subgroup.center Kbar)).comp q).ker) = W
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    obtain ⟨eAlt⟩ := hA6Z3.2.2
    let e1' : K ⧸ ψ1.ker ≃* (↥φ.range) ⧸ V :=
      QuotientGroup.quotientKerEquivOfSurjective ψ1 hψ1_surj
    let e1 : K ⧸ W ≃* (↥φ.range) ⧸ V :=
      (QuotientGroup.quotientMulEquivOfEq hker1).symm.trans e1'
    let e2' : K ⧸ ψ2.ker ≃* Kbar ⧸ Subgroup.center Kbar :=
      QuotientGroup.quotientKerEquivOfSurjective ψ2 hψ2_surj
    let e2 : K ⧸ W ≃* Kbar ⧸ Subgroup.center Kbar :=
      (QuotientGroup.quotientMulEquivOfEq hker2).symm.trans e2'
    exact ⟨(e1.symm.trans e2).trans eAlt⟩
  ·
    exfalso
    have hB : φ.ker ⊔ T = ⊤ := by
      have h := Subgroup.comap_map_eq (f := q) φ.ker
      rw [show (φ.ker).map q = ⊤ from hNbarTop, Subgroup.comap_top] at h
      rw [QuotientGroup.ker_mk'] at h
      exact h.symm
    have hrange_le : φ.range ≤ T.map φ := by
      intro x hx
      rcases hx with ⟨a, rfl⟩
      have ha : a ∈ φ.ker ⊔ T := hB ▸ Subgroup.mem_top a
      rcases Subgroup.mem_sup_of_normal_right.mp ha with ⟨y, hy, z, hz, rfl⟩
      rw [map_mul, (MonoidHom.mem_ker.mp hy), one_mul]
      exact Subgroup.mem_map_of_mem φ hz
    have hrange_eq : T.map φ = φ.range :=
      le_antisymm (Subgroup.map_le_range (f := φ) T) hrange_le
    have hT2 : IsPGroup 2 T := CFSG.pCore_isPGroup
    have hR2 : IsPGroup 2 ↥φ.range := hrange_eq ▸ hT2.map φ
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent ↥φ.range := IsPGroup.isNilpotent hR2
    have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot φ.range).mpr hφrange
    exact (Group.IsPerfect.not_isNilpotent ↥φ.range) hnil

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
