module

public import CFSG.Monster.B.GSide.EdgeQCertOrbits
public import CFSG.Monster.B.GSide.TriangleData
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Monster.B.GSide.MuFourOmega
public import Certificates.Certificate3134
public import Certificates.Certificate3057
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.Co2 (v0 decW)

theorem clabel_cu_mul_fourth
    {g : CVert}
    (hg : clabelS g = clabelS cv0 * clabelS cw0 * clabelS (cu 0)) :
    clabel (cu 0) * clabel g = xhat := by
  have hg' : clabel g = clabel cv0 * clabel cw0 * clabel (cu 0) := congrArg Subtype.val hg
  have hx : clabel cv0 * clabel cw0 = xhat := by
    rw [clabel_cv0, clabel_cw0, ← mul_assoc, cQ_mul_self, one_mul]
  have h1 := clabel_comm_of_adj (cgraph_adj_cu 0).1
  have h2 := clabel_comm_of_adj (cgraph_adj_cu 0).2
  have hc : clabel (cu 0) * (clabel cv0 * clabel cw0) =
      clabel cv0 * clabel cw0 * clabel (cu 0) := by
    rw [← mul_assoc, ← h1, mul_assoc, ← h2, ← mul_assoc]
  rw [hg', ← mul_assoc, hc, mul_assoc, clabel_mul_clabel (cu 0), mul_one, hx]

theorem clabel_cu_mem_Ehat :
    clabel
    (cu 0) ∈ Ehat := by
  obtain ⟨g, -, -, hadj, hg⟩ := exists_fourth_vertex
  obtain ⟨s, hs0, hs1⟩ := cvMul_edge_transitive cgraph_adj_cv0_cw0 hadj
  have e1 : clabel (cu 0) = ((s : Dfull))⁻¹ * cQ * s := by
    rw [← hs0, clabel_cvMul, clabel_cv0]
  have e2 : clabel g = ((s : Dfull))⁻¹ * (cQ * xhat) * s := by
    rw [← hs1, clabel_cvMul, clabel_cw0]
  have hyy : clabel (cu 0) * clabel g = ((s : Dfull))⁻¹ * xhat * s := by
    rw [e1, e2]
    calc ((s : Dfull))⁻¹ * cQ * s * (((s : Dfull))⁻¹ * (cQ * xhat) * s) =
        ((s : Dfull))⁻¹ * (cQ * cQ * xhat) * s := by group
      _ = ((s : Dfull))⁻¹ * xhat * s := by rw [cQ_mul_self, one_mul]
  have hsx : ((s : Dfull))⁻¹ * xhat * s = xhat := hyy.symm.trans (clabel_cu_mul_fourth hg)
  have hsJ : (s : Dfull) ∈ Jhat := by
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff]
    calc (s : Dfull) * xhat = (s : Dfull) * (((s : Dfull))⁻¹ * xhat * s) := by rw [hsx]
      _ = xhat * s := by group
  rw [e1]
  exact conj_mem_Ehat hsJ cQ_mem_Ehat

theorem clabelS_cu_mem_cEdgeFix :
    clabelS (cu 0) ∈ cEdgeFix :=
  ⟨(commute_clabel_iff cv0 _).1 (clabel_comm_of_adj (cgraph_adj_cu 0).1).symm,
    (commute_clabel_iff cw0 _).1 (clabel_comm_of_adj (cgraph_adj_cu 0).2).symm⟩

@[expose] def lamU0 :
    cEdgeFix := ⟨clabelS (cu 0), clabelS_cu_mem_cEdgeFix⟩

theorem coe_lamU0 :
    ((lamU0 : Shat) : Dfull) =
    clabel (cu 0) := rfl

theorem lamU0_mem_edgeL :
    lamU0 ∈
    edgeL := by
  have hinj := native_global_label_bijection_and_full_vertex_centralizer.1
  refine ⟨clabel_cu_mem_Ehat, ⟨cu 0, rfl⟩, fun h => ?_, fun h => ?_⟩
  · have e : clabel cv0 = clabel (cu 0) :=
      (congrArg (fun a : cEdgeFix => ((a : Shat) : Dfull)) h).symm
    exact cv0_ne_cu 0 (hinj e)
  · have e : clabel cw0 = clabel (cu 0) :=
      (congrArg (fun a : cEdgeFix => ((a : Shat) : Dfull)) h).symm
    exact cw0_ne_cu 0 (hinj e)

theorem wit_checks :
    Co2.Native.vectors.contains 1023447 = true ∧ bWcode 6144 1023447 = 1 ∧
    bWcode (6144 ^^^ 31) 1023447 = 0 :=
  Certificates.certificate3134

theorem bV_u0_wit :
    bV (Unitary.sigmaW + wFr)
    (decW 1023447) = 0 :=
    by
  rw [Unitary.sigmaW_eq_decW, wFr_eq_decW, ← Co2.decW_xor, bV_decW, wit_checks.2.2]
  rfl

@[expose] def witE : Ehat := (psiW_surjective (decW 1023447)).choose

theorem psiW_witE : psiW witE = decW 1023447 := (psiW_surjective _).choose_spec

theorem exists_clabel_eq_witE :
    ∃ y₀ :
    CVert, clabel y₀ = witE := by
  have hΩ : psiW witE ∈ Unitary.OmegaW := by
    rw [psiW_witE]
    exact Unitary.decW_mem_OmegaW wit_checks.1
  obtain ⟨s, hs⟩ := exists_label_of_psiW_mem_OmegaW hΩ
  refine ⟨cvMul cv0 s, ?_⟩
  rw [clabel_cvMul, clabel_cv0, hs]

theorem witE_comm_u0 :
    (witE : Dfull) * (cQ * yhat) =
    cQ * yhat *
    witE := by
  have h := (Ehat_commute_iff witE (toEhat (a := edgeU0) u0_mem_Ehat)).2 (by
    rw [psiW_witE, psiW_edgeU0, bV_comm]
    exact bV_u0_wit)
  exact h

theorem witE_not_mem_cEdgeFix :
    (elS witE.2 : Shat) ∉
    cEdgeFix := by
  have h := (not_mem_cEdgeFix_iff_of_edgeQ (x := edgeQOf witE.2) witE.2).2 (by
    have e : qToEhat (x := edgeQOf witE.2) witE.2 = witE := rfl
    rw [e, psiW_witE]
    exact bV_sigma_decW_one wit_checks.2.1)
  exact h

theorem conj_mem_cEdgeFix_iff
    (a : cEdgeFix) {b : Shat} :
    (a : Shat) * b * (a : Shat)⁻¹ ∈ cEdgeFix ↔ b ∈ cEdgeFix := by
  constructor
  · intro h
    have h' := cEdgeFix.mul_mem (cEdgeFix.mul_mem (cEdgeFix.inv_mem a.2) h) a.2
    have e : ((a : Shat))⁻¹ * ((a : Shat) * b * (a : Shat)⁻¹) * (a : Shat) = b := by group
    rw [e] at h'
    exact h'
  · intro h
    exact cEdgeFix.mul_mem (cEdgeFix.mul_mem a.2 h) (cEdgeFix.inv_mem a.2)

theorem edgeQCert_hWit :
    ∃ y, ∃ hs : clabelS y ∈
    cvSetStab
    {cv0, cw0},
    IsTriB 0 (clabelS y) ∧ (⟨clabelS y, hs⟩ : cEdgeStab) ∈ edgeQ := by
  obtain ⟨y₀, hy₀⟩ := exists_clabel_eq_witE
  obtain ⟨a, ha⟩ := edgeL_conj edgeU0_mem_edgeL lamU0_mem_edgeL
  have hb₀ : clabelS y₀ = elS witE.2 := Subtype.ext hy₀
  have hy : clabelS (cvMul y₀ (a : Shat)⁻¹) = (a : Shat) * clabelS y₀ * (a : Shat)⁻¹ := by
    rw [clabelS_cvMul, inv_inv]
  have haE : (a : Shat) ∈ cEdgeStab := cEdgeFix_le_cEdgeStab a.2
  have hb₀E : clabelS y₀ ∈ cEdgeStab := hb₀ ▸ mem_cEdgeStab_of_mem_Ehat witE.2
  have hs : clabelS (cvMul y₀ (a : Shat)⁻¹) ∈ cvSetStab {cv0, cw0} := by
    rw [hy]
    exact cEdgeStab.mul_mem (cEdgeStab.mul_mem haE hb₀E) (cEdgeStab.inv_mem haE)
  have hnA : clabelS (cvMul y₀ (a : Shat)⁻¹) ∉ cEdgeFix := by
    rw [hy, conj_mem_cEdgeFix_iff, hb₀]
    exact witE_not_mem_cEdgeFix
  have haP : ((a : Shat) : Dfull) ∈ P1 := mem_cEdgeFix_iff.1 a.2
  have haJ : ((a : Shat) : Dfull)⁻¹ ∈ Jhat := Jhat.inv_mem (P1_le_Jhat haP)
  have hval : clabel (cvMul y₀ (a : Shat)⁻¹) =
      ((a : Shat) : Dfull) * witE * ((a : Shat) : Dfull)⁻¹ := by
    have h := congrArg Subtype.val hy
    rw [← hy₀]
    exact h
  have hu : clabel (cu 0) = ((a : Shat) : Dfull) * (cQ * yhat) * ((a : Shat) : Dfull)⁻¹ :=
    congrArg (fun b : cEdgeFix => ((b : Shat) : Dfull)) ha
  refine ⟨cvMul y₀ (a : Shat)⁻¹, hs, ⟨?_, ?_, ?_⟩, ?_⟩
  · rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hs with h | h
    · exact absurd ⟨h.1, h.2⟩ hnA
    · exact h.1
  · rcases (mem_cvSetStab_pair cgraph_adj_cv0_cw0.ne).1 hs with h | h
    · exact absurd ⟨h.1, h.2⟩ hnA
    · exact h.2
  · refine (commute_clabel_iff (cu 0) _).1 ?_
    show clabel (cvMul y₀ (a : Shat)⁻¹) * clabel (cu 0) =
      clabel (cu 0) * clabel (cvMul y₀ (a : Shat)⁻¹)
    rw [hval, hu]
    calc ((a : Shat) : Dfull) * witE * ((a : Shat) : Dfull)⁻¹ *
          (((a : Shat) : Dfull) * (cQ * yhat) * ((a : Shat) : Dfull)⁻¹) =
        ((a : Shat) : Dfull) * ((witE : Dfull) * (cQ * yhat)) * ((a : Shat) : Dfull)⁻¹ := by
          group
      _ = ((a : Shat) : Dfull) * (cQ * yhat * witE) * ((a : Shat) : Dfull)⁻¹ := by
          rw [witE_comm_u0]
      _ = ((a : Shat) : Dfull) * (cQ * yhat) * ((a : Shat) : Dfull)⁻¹ *
          (((a : Shat) : Dfull) * witE * ((a : Shat) : Dfull)⁻¹) := by group
  · show clabel (cvMul y₀ (a : Shat)⁻¹) ∈ Ehat
    rw [hval]
    have h := conj_mem_Ehat haJ witE.2
    rw [inv_inv] at h
    exact h

end CFSG.Monster.B.GSide
