
module

public import Certificates.Kernel.Co1ThreeK.GlueQ
public import Certificates.Kernel.Co1ThreeK.Conj
public import Certificates.Kernel.Co1ThreeK.ForestSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KS.SporSch.M24 CFSG.KS.Raw
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance Timmesfeld.Co1Leaf
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (lG wG eltG aGA SplitData root
  mem_expVecs_iff aGA_length)

@[expose] noncomputable def kdWords : List (List ℤ) := CS.KW.map CFSG.Sporadic.Co1Schreier.Native.decWord

theorem KD_base : [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR] =
    (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (KD.M i) := by
  have h := kKB
  simp only [Bool.and_eq_true] at h
  have e0 : KD.M 0 = SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : KD.M 1 = SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem KD_dag : CFSG.Sporadic.Co1Schreier.Native.dag
    [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR] kdWords =
    ((List.range 89).map fun i => CFSG.KS.Raw.unpack 24 24 (KD.M i),
      (List.range 89).map fun i => CFSG.KS.Raw.unpack 24 24 (KD.MI i), true) :=
  dagWK_sound KD_base kKD

theorem kdK_ex {k : ℕ} (hk : k < 89) :
    ∃ g : ↥GA, matK (KD.M k) = ιK g := by
  have hflag : (CFSG.Sporadic.Co1Schreier.Native.dag
      [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR]
        kdWords).2.2 = true := by
    rw [KD_dag]
  have hrep := getD_rep (dag_rep (List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂
    List.Forall₂.nil)) _ hflag) MRep.one k
  have hmem : ∀ y ∈ [A₁, A₂], y ∈ GA := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with h | h
    · rw [h]; exact A₁_mem
    · rw [h]; exact A₂_mem
  refine ⟨⟨_, getD_mem_of_forall (dagG_mem hmem kdWords) k⟩, ?_⟩
  rw [KD_dag, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getElem_range] at hrep
  change matK (KD.M k) = (((dagG [A₁, A₂] kdWords).getD k 1 : GL24) :
    Matrix (Fin 24) (Fin 24) (ZMod 2))
  rw [← mRep_iff, unpackR_eq_unpack]
  exact hrep

section Classes

theorem mem_T_eQ {t : ↥GA} (ht : t ∈ eSplitK.T) : ∃ c < 729, t = eQ nodeK c := by
  obtain ⟨x, rfl⟩ := ht
  rw [← ofAdd_toAdd x, Co1T.SplitData.φ_apply]
  obtain ⟨hl, hlt⟩ := mem_expVecs_iff.1 (Co1T.vecList_mem_expVecs (Multiplicative.toAdd x))
  generalize Co1T.vecList (Multiplicative.toAdd x) = l at hl hlt ⊢
  obtain ⟨x0, x1, x2, x3, x4, x5, rfl⟩ := six_of_length (hl.trans aGA_length)
  have h0 := hlt x0 (by simp)
  have h1 := hlt x1 (by simp)
  have h2 := hlt x2 (by simp)
  have h3 := hlt x3 (by simp)
  have h4 := hlt x4 (by simp)
  have h5 := hlt x5 (by simp)
  refine ⟨x0 + 3 * x1 + 9 * x2 + 27 * x3 + 81 * x4 + 243 * x5, by omega, ?_⟩
  rw [eQ_eltG, digK]
  congr 1
  simp only [List.cons.injEq, and_true]
  omega

theorem eQ_zero_K : eQ nodeK 0 = 1 := eQ_zero

theorem conj_of_mat {n x y : ↥GA} (h : ιK n * ιK x = ιK y * ιK n) : n * x * n⁻¹ = y := by
  rw [← map_mul, ← map_mul] at h
  rw [ιK_injective h]
  group

theorem classes_E {t : ↥GA} (ht : t ∈ eSplitK.T) (h1 : t ≠ 1) : ∃ g : ↥GA,
    g * t * g⁻¹ = root 0 ∨ g * t * g⁻¹ = root 1 ∨ g * t * g⁻¹ = eltG aGA [0, 1, 0, 0, 1, 1] := by
  obtain ⟨c, hc, rfl⟩ := mem_T_eQ ht
  have hc0 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · exact absurd eQ_zero_K h1
    · exact h
  obtain ⟨r, hr, hconj⟩ := forest_conj ιK ιK_injective nodeK (fun k hk => matK_nodeK (by omega))
    qHypK.comm qHypK.cube hc0 hc
  obtain ⟨h, hh⟩ := isConj_iff.1 hconj
  change h * eQ nodeK r * h⁻¹ = eQ nodeK c at hh
  rw [← hh]
  have hs : ∀ (n : ↥GA) (y : ↥GA), n * eQ nodeK r * n⁻¹ = y →
      (n * h⁻¹) * (h * eQ nodeK r * h⁻¹) * (n * h⁻¹)⁻¹ = y := by
    intro n y hy
    rw [← hy]
    group
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · obtain ⟨nC, hnC⟩ := kdK_ex (k := 88) (by norm_num)
    refine ⟨nC * h⁻¹, Or.inl (hs _ _ (conj_of_mat ?_))⟩
    have e := congrArg matK (Nat.eq_of_beq_eq_true kNC)
    have hL : matK (L.M 4) = ιK (nodeK 4) := by
      rw [← TS_LM (by norm_num)]
      exact matK_nodeK (by norm_num)
    rw [matK_mulWK, matK_mulWK, hnC, matK_RM (by norm_num), hL] at e
    have e81 : eQ nodeK 81 = nodeK 4 := by
      have hd : digK 81 = [0, 0, 0, 0, 1, 0] := rfl
      rw [eQ_eltG, hd, nodeK_a (i := 4) (by norm_num)]
      apply Subtype.ext
      rw [coe_eltG_six]
      simp only [pow_zero, pow_one, one_mul, mul_one]
      rfl
    rw [e81]
    exact e
  · obtain ⟨nB, hnB⟩ := kdK_ex (k := 87) (by norm_num)
    refine ⟨nB * h⁻¹, Or.inr (Or.inl (hs _ _ (conj_of_mat ?_)))⟩
    have e := congrArg matK (Nat.eq_of_beq_eq_true kNB)
    have hL : matK (L.M 5) = ιK (nodeK 5) := by
      rw [← TS_LM (by norm_num)]
      exact matK_nodeK (by norm_num)
    rw [matK_mulWK, matK_mulWK, hnB, matK_RM (by norm_num), hL] at e
    have e243 : eQ nodeK 243 = nodeK 5 := by
      have hd : digK 243 = [0, 0, 0, 0, 0, 1] := rfl
      rw [eQ_eltG, hd, nodeK_a (i := 5) (by norm_num)]
      apply Subtype.ext
      rw [coe_eltG_six]
      simp only [pow_zero, pow_one, one_mul, mul_one]
      rfl
    rw [e243]
    exact e
  · refine ⟨h⁻¹, Or.inr (Or.inr ?_)⟩
    have hd : digK 327 = [0, 1, 0, 0, 1, 1] := rfl
    rw [inv_inv, eQ_eltG, hd]
    group

end Classes

end CertificateChecks.KernelCo1ThreeK

end
