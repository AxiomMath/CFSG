module

public import Certificates.Kernel.Co1ThreeK.GlueE
public import Certificates.Kernel.Co1ThreeK.Plane
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KS.SporSch.M24 CFSG.KS.Raw
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (root)

theorem KZ_base : [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR] =
    (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (KZ.M i) := by
  have h := kZB
  simp only [Bool.and_eq_true] at h
  have e0 : KZ.M 0 = SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : KZ.M 1 = SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDagB_eq : CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag
    CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext =
    ((List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (KZ.M i),
      (List.range 91).map fun i => CFSG.KS.Raw.unpack 24 24 (KZ.MI i), true) := by
  rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag, ← kZW]
  exact dagWK_sound KZ_base kKZ

theorem matK_z :
    matK (KZ.M 90) = ((CFSG.HardMathSupport.Dickson.I271.TabCo1.kG
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91 : GL24) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have hflag : (CFSG.HardMathSupport.Dickson.I271.TabCo1.kDag
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext).2.2 = true := by
    rw [kDagB_eq]
  have hrep := CFSG.HardMathSupport.Dickson.I271.TabCo1.rep_nd hflag 91
  rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.nd, kDagB_eq] at hrep
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range] at hrep
  rw [← mRep_iff, unpackR_eq_unpack]
  exact hrep

section Plane


theorem plane_K : ∃ n : ↥GA, n⁻¹ * root 1 * n ∈ eSplitK.T ∧
    n⁻¹ * ⟨CFSG.HardMathSupport.Dickson.I271.TabCo1.kG
      CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91,
      CFSG.HardMathSupport.Dickson.I271.TabCo1.kG_mem _ 91⟩ * n ∈ eSplitK.T := by
  obtain ⟨n, hn⟩ := kdK_ex (k := 87) (by norm_num)
  refine ⟨n, ?_, ?_⟩
  · have e := congrArg matK (Nat.eq_of_beq_eq_true kNB)
    have hL : matK (L.M 5) = ιK (nodeK 5) := by
      rw [← TS_LM (by norm_num)]
      exact matK_nodeK (by norm_num)
    rw [matK_mulWK, matK_mulWK, hn, matK_RM (by norm_num), hL] at e
    have h : n * nodeK 5 * n⁻¹ = root 1 := conj_of_mat e
    have e5 : n⁻¹ * root 1 * n = nodeK 5 := by
      rw [← h]
      group
    rw [e5]
    exact nodeK_mem_T (by norm_num)
  · have h := kZ
    simp only [Bool.and_eq_true] at h
    have e := congrArg matK (Nat.eq_of_beq_eq_true h.2)
    have hE : matK (epK L.M 3 [0, 1, 2, 3, 4, 5] CZ.V oneK) = ιK (eQ nodeK CZ.V) := by
      rw [epK_mat, matK_oneK]
      have hc : epM (fun k => matK (L.M k)) 3 [0, 1, 2, 3, 4, 5] CZ.V 1 =
          epM (fun k => matK (TS k)) 3 [0, 1, 2, 3, 4, 5] CZ.V 1 :=
        epM_congr 3 _ (fun g hg => by
          have hg6 : g < 9 := by simp at hg; omega
          rw [TS_LM hg6]) CZ.V 1
      rw [hc, eQ_mat qHypK]
    rw [matK_mulWK, matK_mulWK, hn, matK_z, hE] at e
    have e' : n⁻¹ * ⟨CFSG.HardMathSupport.Dickson.I271.TabCo1.kG
        CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91,
        CFSG.HardMathSupport.Dickson.I271.TabCo1.kG_mem _ 91⟩ * n = eQ nodeK CZ.V := by
      have e2 : ⟨CFSG.HardMathSupport.Dickson.I271.TabCo1.kG
          CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB.ext 91,
          CFSG.HardMathSupport.Dickson.I271.TabCo1.kG_mem _ 91⟩ * n = n * eQ nodeK CZ.V := by
        apply ιK_injective
        rw [map_mul, map_mul]
        exact e
      rw [mul_assoc, e2, inv_mul_cancel_left]
    rw [e']
    exact eQ_mem_T _

end Plane

end CertificateChecks.KernelCo1ThreeK

end
