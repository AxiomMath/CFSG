module

public import CFSG.LocalAnalysis.StandardType.PhanEBruhat
public import CFSG.LieType.RootSystem.Form
public import CFSG.Monster.B.Geometry.Coxeter

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)

@[expose] noncomputable def stdδ : K ⧸ borel D H → K ⧸ borel D H → W :=
  open Classical in
  cosetDistance (borel D H) (bruhatCell hct)

theorem stdδ_mk_eq_iff (hext : SteinbergExtras D n H) (g h : K) (w : W) :
    stdδ hct (g : K ⧸ borel D H) (h : K ⧸ borel D H) = w ↔ g⁻¹ * h ∈ bruhatCell hct w :=
  cosetDistance_mk (isBruhatPartition_bruhatCell hct hext) g h w

theorem stdδ_smul (hext : SteinbergExtras D n H) (a : K) (x y : K ⧸ borel D H) :
    stdδ hct (a • x) (a • y) = stdδ hct x y :=
  cosetDistance_smul (isBruhatPartition_bruhatCell hct hext) a x y

theorem stdBuilding (hext : SteinbergExtras D n H) :
    IsWeylDistanceBuilding (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) :=
  isWeylDistanceBuilding (isBruhatPartition_bruhatCell hct hext)

theorem std_residue_mk (hext : SteinbergExtras D n H) (J : Set (Fin D.rank)) :
    ∃ P : Subgroup K, (P : Set K) = ⋃ w ∈ Subgroup.closure ((cs).simple '' J), bruhatCell hct w ∧
      ∀ g : K, residue (coxeterMatrix D.isFiniteType).toCoxeterSystem (stdδ hct) J
        (g : K ⧸ borel D H) = (fun x : K => (x : K ⧸ borel D H)) '' (g • (P : Set K)) := by
  refine ⟨parabolic (isBruhatPartition_bruhatCell hct hext) J, ?_, ?_⟩
  · exact coe_parabolic (isBruhatPartition_bruhatCell hct hext) J
  · intro g
    exact residue_mk (isBruhatPartition_bruhatCell hct hext) J g

theorem std_thick (hext : SteinbergExtras D n H) (i : Fin D.rank) (x : K ⧸ borel D H) :
    ∃ y z : K ⧸ borel D H, stdδ hct x y = (cs).simple i ∧ stdδ hct x z = (cs).simple i ∧
      y ≠ z := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨c, hc, hcB⟩ :=
    Set.not_subset.mp (not_map_conj_n_borel_le hct hext i)
  obtain ⟨p, hp, hpc⟩ := Subgroup.mem_map.mp hc
  have hp_not : p ∉ (borel D H).map (MulAut.conj ((n i)⁻¹)).toMonoidHom := by
    intro hpmem
    obtain ⟨d, hd, hdp⟩ := Subgroup.mem_map.mp hpmem
    apply hcB
    have hcd : c = d := by
      rw [← hpc, ← hdp]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcd]
    exact hd
  have hn_inv : (n i)⁻¹ ∈ bruhatCell hct ((cs).simple i) := by
    have ht : (n i ^ 2)⁻¹ ∈ borel D H :=
      inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
    have hni : n i ∈ bruhatCell hct ((cs).simple i) := by
      rw [← nrep_simple hct i]
      exact nrep_mem_bruhatCell hct _
    have e : (n i)⁻¹ = n i * (n i ^ 2)⁻¹ := by group
    rw [e]
    exact mul_mem_bruhatCell_right hct hni ht
  refine ⟨((g * (n i)⁻¹ : K) : K ⧸ borel D H),
    ((g * p * (n i)⁻¹ : K) : K ⧸ borel D H), ?_, ?_, ?_⟩
  · rw [stdδ_mk_eq_iff hct hext g (g * (n i)⁻¹) ((cs).simple i)]
    rw [show g⁻¹ * (g * (n i)⁻¹) = (n i)⁻¹ by group]
    exact hn_inv
  · rw [stdδ_mk_eq_iff hct hext g (g * p * (n i)⁻¹) ((cs).simple i)]
    rw [show g⁻¹ * (g * p * (n i)⁻¹) = p * (n i)⁻¹ by group]
    exact mul_mem_bruhatCell hct hp hn_inv
  · intro heq
    have hmem : n i * p * (n i)⁻¹ ∈ borel D H := by
      have h := QuotientGroup.eq.mp heq
      have e : (g * (n i)⁻¹)⁻¹ * (g * p * (n i)⁻¹) = n i * p * (n i)⁻¹ := by group
      rwa [e] at h
    apply hp_not
    rw [Subgroup.mem_map]
    exact ⟨n i * p * (n i)⁻¹, hmem, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩

end CFSG.ClassicalInvolution.Phan.PhanE
