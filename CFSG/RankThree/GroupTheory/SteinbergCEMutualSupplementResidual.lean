module

public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.RankThree.GroupTheory.SteinbergCEQuotientKernelMonotonicity
import CFSG.RankThree.PerfectCover.SubnormalSolvableSupplement

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isSolvable_sup_of_le_normalizer {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable N)
    (hT : Group.IsSolvable T) : Group.IsSolvable (N ⊔ T : Subgroup G) := by
  set V := N ⊔ T
  have hNV : N ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V)
  set f : T →* V ⧸ N.subgroupOf V := π.comp (Subgroup.inclusion hTV)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : G) ∈ ((T ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (Subgroup.inclusion hTV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hTV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : G) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVsol : Group.IsSolvable (N.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNV).injective
  have hQsol : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hf
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf V).subtype π ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem inSubgroup_core_eq_inf_of_subgroupOf_isSubnormal [Finite G] {p : ℕ} (hp : p.Prime)
    {K C : Subgroup G} (hKC : K ≤ C) (hK : (K.subgroupOf C).IsSubnormal) :
    inSubgroup (aschbacherSolvableCore p) K = K ⊓ inSubgroup (aschbacherSolvableCore p) C := by
  set K' := K.subgroupOf C
  have h1 := solvable_prime_complement_core_subnormal_intersection hp hK
  set e := Subgroup.subgroupOfEquivOfLe hKC
  have h2 : (aschbacherSolvableCore p K').map e.toMonoidHom = aschbacherSolvableCore p K :=
    aschbacherSolvableCore_map_mulEquiv hp e
  have hcomp : K.subtype.comp e.toMonoidHom = C.subtype.comp K'.subtype :=
    MonoidHom.ext fun _ => rfl
  calc inSubgroup (aschbacherSolvableCore p) K
      = ((aschbacherSolvableCore p K').map e.toMonoidHom).map K.subtype := by
        rw [h2]
        rfl
    _ = (inSubgroup (aschbacherSolvableCore p) K').map C.subtype := by
        rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
        rfl
    _ = (K' ⊓ aschbacherSolvableCore p C).map C.subtype := by rw [h1]
    _ = K ⊓ inSubgroup (aschbacherSolvableCore p) C := by
        rw [Subgroup.map_inf_eq _ _ _ C.subtype_injective, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hKC]
        rfl

theorem mutual_theta_supplements_identify_local_residual [Finite G] {p : ℕ} (hp : p.Prime)
    {b : G} {L K : Subgroup G} (hK : K ∈ thetaComponentsAt p b)
    (hLK : L = (L ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore p) L)
    (hKL : K = (K ⊓ L) ⊔ inSubgroup (aschbacherSolvableCore p) K) :
    ∃ U : Subgroup G,
      (U : Set G) = ((L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) : Set G) *
        (inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) : Set G) ∧
      inSubgroup perfectResidual U = K := by
  set CB := Subgroup.centralizer ({b} : Set G)
  set N := inSubgroup (aschbacherSolvableCore p) CB
  set θL := inSubgroup (aschbacherSolvableCore p) L
  set θK := inSubgroup (aschbacherSolvableCore p) K
  set M := L ⊓ K
  set T := θL ⊓ CB
  set CL := L ⊓ CB
  obtain ⟨K', hK', hK'K⟩ := hK
  have hKCB : K ≤ CB := hK'K ▸ Subgroup.map_subtype_le K'
  have hK'eq : K' = K.subgroupOf CB := by
    rw [← hK'K]
    exact (Subgroup.comap_map_eq_self_of_injective CB.subtype_injective K').symm
  have hKperf : Group.IsPerfect K := by
    have := hK'.1
    have e := (K'.equivMapOfInjective CB.subtype CB.subtype_injective).trans
      (MulEquiv.subgroupCongr hK'K)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hKsn : (K.subgroupOf CB).IsSubnormal := hK'eq ▸ hK'.2.1
  have hθK : θK = K ⊓ N := inSubgroup_core_eq_inf_of_subgroupOf_isSubnormal hp hKCB hKsn
  have hNCB : N ≤ CB := Subgroup.map_subtype_le _
  have hNnormal : (N.subgroupOf CB).Normal := by
    have h : N.subgroupOf CB = aschbacherSolvableCore p CB :=
      Subgroup.comap_map_eq_self_of_injective CB.subtype_injective _
    rw [h]
    infer_instance
  have hCBN : CB ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNCB).mp hNnormal
  have hMCB : M ≤ CB := inf_le_right.trans hKCB
  have hCLMT : CL ≤ M ⊔ T := by
    intro x hx
    obtain ⟨m, hm, n, hn, rfl⟩ := exists_mul_of_eq_sup_core inf_le_left hLK hx.1
    have hnCB : n ∈ CB := by
      have h := CB.mul_mem (CB.inv_mem (hMCB hm)) hx.2
      rwa [inv_mul_cancel_left] at h
    exact Subgroup.mul_mem_sup hm ⟨hn, hnCB⟩
  set U := CL ⊔ N
  have hCLN : CL ≤ Subgroup.normalizer (N : Set G) := inf_le_right.trans hCBN
  have hUset : (U : Set G) = (CL : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right CL N hCLN
  have hMCL : M ≤ CL := le_inf inf_le_left hMCB
  have hKU : K ≤ U := by
    rw [hKL, inf_comm, hθK]
    exact sup_le (hMCL.trans le_sup_left) (inf_le_right.trans le_sup_right)
  have hUCB : U ≤ CB := sup_le inf_le_right hNCB
  set V := N ⊔ T
  have hθLL : θL ≤ L := Subgroup.map_subtype_le _
  have hTCL : T ≤ CL := inf_le_inf_right CB hθLL
  have hVU : V ≤ U := sup_le le_sup_right (hTCL.trans le_sup_left)
  have hTN : T ≤ Subgroup.normalizer (N : Set G) := hTCL.trans hCLN
  have hNeq : N = thetaCoreOf p CB := inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp CB
  have hθLeq : θL = thetaCoreOf p L := inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp L
  have hNsol : Group.IsSolvable N := hNeq ▸ thetaCoreOf_solvable p hp CB
  have hθLsol : Group.IsSolvable θL := hθLeq ▸ thetaCoreOf_solvable p hp L
  have hTsol : Group.IsSolvable T :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
  have hVsol : Group.IsSolvable V := isSolvable_sup_of_le_normalizer hTN hNsol hTsol
  have hVnorm : U ≤ Subgroup.normalizer (V : Set G) := by
    refine sup_le ?_ (le_sup_left.trans Subgroup.le_normalizer)
    refine le_trans ?_ (Subgroup.inf_normalizer_le_normalizer_sup N T)
    refine le_inf hCLN fun x hx => ?_
    have hxθ : x ∈ Subgroup.normalizer (θL : Set G) := by
      have hθnormal : (θL.subgroupOf L).Normal := by
        have h : θL.subgroupOf L = aschbacherSolvableCore p L :=
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
        rw [h]
        infer_instance
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hθLL).mp hθnormal hx.1
    have hxC : x ∈ Subgroup.normalizer (CB : Set G) := Subgroup.le_normalizer hx.2
    rw [Subgroup.mem_normalizer_iff] at hxθ hxC ⊢
    intro h
    exact and_congr (hxθ h) (hxC h)
  have hUKV : U ≤ K ⊔ V := by
    refine sup_le (hCLMT.trans (sup_le_sup ?_ le_sup_right)) (le_sup_left.trans le_sup_right)
    exact inf_le_right
  have hKUperf : Group.IsPerfect (K.subgroupOf U) := by
    have := hKperf
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hKU).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKU).symm.surjective
  have hKUsn : (K.subgroupOf U).IsSubnormal := by
    have h := hKsn.comap (Subgroup.inclusion hUCB)
    rwa [Subgroup.comap_inclusion_subgroupOf] at h
  have hVUnormal : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mpr hVnorm
  have hVUsol : Group.IsSolvable (V.subgroupOf U) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hVU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hVU).injective
  have hsup : K.subgroupOf U ⊔ V.subgroupOf U = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKU hVU, le_antisymm (sup_le hKU hVU) hUKV,
      Subgroup.subgroupOf_self]
  obtain ⟨-, hres⟩ := CFSG.RankThree.PerfectCover.perfect_subnormal_solvable_supplement_residual
    hKUperf hKUsn hVUnormal hVUsol hsup
  refine ⟨U, hUset, ?_⟩
  rw [inSubgroup, hres, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKU]

end CFSG.RankThree.GroupTheory
