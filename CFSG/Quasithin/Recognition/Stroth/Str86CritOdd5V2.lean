module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs

import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5L311
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5N3
import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str86_conjSub_eq_of_forall_commute {x : G} {Z : Subgroup G}
    (h : ∀ z ∈ Z, x * z = z * x) : conjSub x Z = Z := by
  ext z
  rw [mem_conjSub]
  constructor
  · intro hz
    have h' : x * (x⁻¹ * z * x) = (x⁻¹ * z * x) * x := h _ hz
    have e : z = x⁻¹ * z * x := by
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = (x⁻¹ * z * x) * x * x⁻¹ := by rw [h']
        _ = x⁻¹ * z * x := by group
    rw [e]
    exact hz
  · intro hz
    have h' : x * z = z * x := h z hz
    have e : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
        _ = x⁻¹ * (x * z) := by rw [h']
        _ = z := by group
    rw [e]
    exact hz

private theorem str86_V2_le_pCoreOf_lam_sub_three
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb5 : 5 ≤ str86CritB L1 L2 S) :
    str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 3))) := by
  obtain ⟨-, hGL2, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  unfold str86V2
  refine iSup₂_le fun γ hγ => ?_
  refine hGL2 γ (lam (str86CritB L1 L2 S - 3))
    (F112Crit.vtype_eq_true_of_mem_nbrs hP.linear hγ) ?_
  have h1 := CosetGeom.dist_triangle hI.critHypN.amalgam.gen γ (lam 0)
    (lam (str86CritB L1 L2 S - 3))
  have h2 : CosetGeom.dist γ (lam 0) = 1 := by
    rw [CosetGeom.dist_comm]
    exact CosetGeom.dist_eq_one_iff_adj.mpr hγ
  have h3 : CosetGeom.dist (lam 0) (lam (str86CritB L1 L2 S - 3)) =
      str86CritB L1 L2 S - 3 := by
    have := hP.isGeo 0 (str86CritB L1 L2 S - 3) (Nat.zero_le _) (by omega)
    simpa using this
  omega

private theorem str86_V2_le_S_lam_sub_three_two
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb5 : 5 ≤ str86CritB L1 L2 S) :
    str86V2 L1 L2 S (lam 0) ≤ stab (lam (str86CritB L1 L2 S - 2)) ∧
      str86V2 L1 L2 S (lam 0) ≤
        pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 3)) ⊓
          stab (lam (str86CritB L1 L2 S - 2))) ∧
      str86V2 L1 L2 S (lam 0) ≤
        pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)) ⊓
          stab (lam (str86CritB L1 L2 S - 3))) := by
  have hVA := str86_V2_le_pCoreOf_lam_sub_three hI hP hb5
  have hA : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 3)) (lam (str86CritB L1 L2 S - 2)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 3) (by omega)
    rwa [show str86CritB L1 L2 S - 3 + 1 = str86CritB L1 L2 S - 2 by omega] at h
  have hVS : str86V2 L1 L2 S (lam 0) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 3)) ⊓
        stab (lam (str86CritB L1 L2 S - 2))) :=
    hVA.trans (str86_pCoreOf_le_pCoreOf_inf hI hA)
  refine ⟨hVS.trans ((pCoreOf_le 2 _).trans inf_le_right), hVS, ?_⟩
  rw [inf_comm]
  exact hVS

private theorem str86_moves_lam_sub_one
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb5 : 5 ≤ str86CritB L1 L2 S) (x : ↥(L1 ⊔ L2 ⊔ S))
    (hxS : (x : G) ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)) ⊓
      stab (lam (str86CritB L1 L2 S - 3))))
    (hxQ : (x : G) ∉ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)))) :
    x • lam (str86CritB L1 L2 S - 1) ≠ lam (str86CritB L1 L2 S - 1) := by
  have hA : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 3)) (lam (str86CritB L1 L2 S - 2)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 3) (by omega)
    rwa [show str86CritB L1 L2 S - 3 + 1 = str86CritB L1 L2 S - 2 by omega] at h
  have hB : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S - 1)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 2) (by omega)
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hne : lam (str86CritB L1 L2 S - 3) ≠ lam (str86CritB L1 L2 S - 1) :=
    hP.isGeo.ne (i := str86CritB L1 L2 S - 3) (j := str86CritB L1 L2 S - 1)
      (by omega) (by omega)
  exact (str86_graph_TI hI).2.2 (lam (str86CritB L1 L2 S - 2))
    (lam (str86CritB L1 L2 S - 3)) (lam (str86CritB L1 L2 S - 1))
    hA.symm hB hne x hxS hxQ

private theorem str86_Z_smul_eq
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb5 : 5 ≤ str86CritB L1 L2 S) (x : ↥(L1 ⊔ L2 ⊔ S))
    (hxV : (x : G) ∈ str86V2 L1 L2 S (lam 0))
    (hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0)) :
    omegaOneCenterOf (pCoreOf 2 (stab (x • lam (str86CritB L1 L2 S)))) =
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
  have hVab : IsElemAbelian 2 (str86V2 L1 L2 S (lam 0)) :=
    (str86_Vv_abelian hI).2.2.2.2 hb5 (lam 0) hP.linear
  have hxcomm : ∀ z ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))),
      (x : G) * z = z * (x : G) :=
    fun z hz => CFSG.Open.IsElemAbelian.comm hVab hxV (hZα'V hz)
  rw [(str86_vertex_smul hI x (lam (str86CritB L1 L2 S))
    (lam (str86CritB L1 L2 S))).2.1]
  exact str86_conjSub_eq_of_forall_commute hxcomm

private theorem str86_Z_le_Z_lam_sub_two
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    (hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0))
    (x : ↥(L1 ⊔ L2 ⊔ S))
    (hxV : (x : G) ∈ str86V2 L1 L2 S (lam 0))
    (hxS : (x : G) ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)) ⊓
      stab (lam (str86CritB L1 L2 S - 3))))
    (hxQ : (x : G) ∉ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2))))
    (hxfix2 : x • lam (str86CritB L1 L2 S - 2) = lam (str86CritB L1 L2 S - 2)) :
    omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)))) := by
  classical
  obtain ⟨j, hj⟩ := hodd
  have hB : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S - 1)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 2) (by omega)
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hmove := str86_moves_lam_sub_one hI hP hb5 x hxS hxQ
  have hZx := str86_Z_smul_eq hI hP hb5 x hxV hZα'V
  have hδ' : x • lam (str86CritB L1 L2 S - 1) ∈
      nbrs (lam (str86CritB L1 L2 S - 2)) := by
    have h := (CosetGeom.smul_adj x).mpr hB
    rwa [hxfix2] at h
  have hneδ : lam (str86CritB L1 L2 S - 1) ≠ x • lam (str86CritB L1 L2 S - 1) :=
    Ne.symm hmove
  have hE : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [show str86CritB L1 L2 S - 1 + 1 = str86CritB L1 L2 S by omega] at h
  have hε' : x • lam (str86CritB L1 L2 S) ∈
      nbrs (x • lam (str86CritB L1 L2 S - 1)) :=
    (CosetGeom.smul_adj x).mpr hE
  have hneεγ : lam (str86CritB L1 L2 S) ≠ lam (str86CritB L1 L2 S - 2) :=
    (hP.isGeo.ne (i := str86CritB L1 L2 S - 2) (j := str86CritB L1 L2 S)
      (by omega) le_rfl).symm
  have hneε' : x • lam (str86CritB L1 L2 S) ≠ lam (str86CritB L1 L2 S - 2) := by
    intro h
    have h' : x • lam (str86CritB L1 L2 S) = x • lam (str86CritB L1 L2 S - 2) := by
      rw [h, hxfix2]
    exact hneεγ (MulAction.injective x h')
  have hγ : vtype (lam (str86CritB L1 L2 S - 2)) = true :=
    hP.vtype_of_odd hI (by omega) ⟨j - 1, by omega⟩
  have hN := str86_oddModule_inf_sup hI hO hγ hB hδ' hneδ hE hneεγ hε' hneε'
  have hsup : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)))) ⊔
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)))) := by
    have h := hN
    rw [hZx] at h
    simpa only [inf_idem] using h
  exact sup_eq_left.mp hsup

private theorem str86_false_of_Z_le_Z_lam_sub_two
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    (hle : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2))))) :
    False := by
  obtain ⟨j, hj⟩ := hodd
  have hB : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S - 1)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 2) (by omega)
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hE : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [show str86CritB L1 L2 S - 1 + 1 = str86CritB L1 L2 S by omega] at h
  have hv1b : vtype (lam (str86CritB L1 L2 S - 1)) = false :=
    hP.vtype_of_even hI (by omega) ⟨j, by omega⟩
  have hne : lam (str86CritB L1 L2 S - 2) ≠ lam (str86CritB L1 L2 S) :=
    hP.isGeo.ne (i := str86CritB L1 L2 S - 2) (j := str86CritB L1 L2 S)
      (by omega) le_rfl
  have hT2 := (str86_graph_F1 hI).1 (lam (str86CritB L1 L2 S - 1))
    (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S)) hv1b hB.symm hE hne
  have hbot : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) = ⊥ := by
    have h := hT2
    rw [inf_eq_right.mpr hle] at h
    exact h
  have hvb : vtype (lam (str86CritB L1 L2 S)) = true :=
    hP.vtype_of_odd hI le_rfl ⟨j, hj⟩
  exact (str86_edge_facts hI hvb hE.symm).2.2.2.2.2.1 hbot

private theorem str86_V2_le_pCoreOf_lam_sub_two
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    (hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0)) :
    str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2))) := by
  classical
  obtain ⟨hVstab2, -, hVS'⟩ := str86_V2_le_S_lam_sub_three_two hI hP hb5
  by_contra hle
  obtain ⟨x, hxV, hxQ⟩ := Set.not_subset.mp hle
  have hxstab2 : x ∈ stab (lam (str86CritB L1 L2 S - 2)) := hVstab2 hxV
  have hxG : x ∈ (L1 ⊔ L2 ⊔ S : Subgroup G) := CosetGeom.stab_le _ hxstab2
  let x' : ↥(L1 ⊔ L2 ⊔ S) := ⟨x, hxG⟩
  have hxS : x ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)) ⊓
      stab (lam (str86CritB L1 L2 S - 3))) := hVS' hxV
  have hxfix2 : x' • lam (str86CritB L1 L2 S - 2) =
      lam (str86CritB L1 L2 S - 2) := CosetGeom.smul_eq_of_mem_stab hxstab2
  exact str86_false_of_Z_le_Z_lam_sub_two hI hP hodd hb5
    (str86_Z_le_Z_lam_sub_two hI hO hP hodd hb5 hZα'V x' hxV hxS hxQ hxfix2)

private theorem str86_V2_le_stab_lam_of_le_stab
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    (hVstab1 : str86V2 L1 L2 S (lam 0) ≤ stab (lam (str86CritB L1 L2 S - 1)))
    (hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0)) :
    str86V2 L1 L2 S (lam 0) ≤ stab (lam (str86CritB L1 L2 S)) := by
  obtain ⟨j, hj⟩ := hodd
  have hE : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [show str86CritB L1 L2 S - 1 + 1 = str86CritB L1 L2 S by omega] at h
  have hVab : IsElemAbelian 2 (str86V2 L1 L2 S (lam 0)) :=
    (str86_Vv_abelian hI).2.2.2.2 hb5 (lam 0) hP.linear
  have hv1b : vtype (lam (str86CritB L1 L2 S - 1)) = false :=
    hP.vtype_of_even hI (by omega) ⟨j, by omega⟩
  have hvb : vtype (lam (str86CritB L1 L2 S)) = true :=
    hP.vtype_of_odd hI le_rfl ⟨j, hj⟩
  intro y hy
  have hy1 : y ∈ stab (lam (str86CritB L1 L2 S - 1)) := hVstab1 hy
  have hyG : y ∈ (L1 ⊔ L2 ⊔ S : Subgroup G) := CosetGeom.stab_le _ hy1
  let y' : ↥(L1 ⊔ L2 ⊔ S) := ⟨y, hyG⟩
  by_contra hyα
  have hfix1 : y' • lam (str86CritB L1 L2 S - 1) = lam (str86CritB L1 L2 S - 1) :=
    CosetGeom.smul_eq_of_mem_stab hy1
  have hδ : y' • lam (str86CritB L1 L2 S) ∈ nbrs (lam (str86CritB L1 L2 S - 1)) := by
    have h := (CosetGeom.smul_adj y').mpr hE
    rwa [hfix1] at h
  have hZeq : omegaOneCenterOf (pCoreOf 2 (stab (y' • lam (str86CritB L1 L2 S)))) =
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
    rw [(str86_vertex_smul hI y' (lam (str86CritB L1 L2 S))
      (lam (str86CritB L1 L2 S))).2.1]
    exact str86_conjSub_eq_of_forall_commute
      (fun z hz => CFSG.Open.IsElemAbelian.comm hVab hy (hZα'V hz))
  have hne : lam (str86CritB L1 L2 S) ≠ y' • lam (str86CritB L1 L2 S) := by
    intro h
    exact hyα (CosetGeom.mem_stab_of_smul_eq h.symm)
  have hT2 := (str86_graph_F1 hI).1 (lam (str86CritB L1 L2 S - 1))
    (lam (str86CritB L1 L2 S)) (y' • lam (str86CritB L1 L2 S)) hv1b hE hδ hne
  have hbot : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) = ⊥ := by
    have h := hT2
    rw [hZeq, inf_idem] at h
    exact h
  exact (str86_edge_facts hI hvb hE.symm).2.2.2.2.2.1 hbot

private theorem str86_V2_le_pCoreOf_lam_sub_one
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    (hVQ2 : str86V2 L1 L2 S (lam 0) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2))))
    (hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0)) :
    str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) := by
  classical
  have hB : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S - 1)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 2) (by omega)
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hE : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
      (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) := by
    have h := hP.isGeo.adj (i := str86CritB L1 L2 S - 1) (by omega)
    rwa [show str86CritB L1 L2 S - 1 + 1 = str86CritB L1 L2 S by omega] at h
  have hVS : str86V2 L1 L2 S (lam 0) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 2)) ⊓
        stab (lam (str86CritB L1 L2 S - 1))) :=
    hVQ2.trans (str86_pCoreOf_le_pCoreOf_inf hI hB)
  have hVstab1 : str86V2 L1 L2 S (lam 0) ≤ stab (lam (str86CritB L1 L2 S - 1)) :=
    hVS.trans ((pCoreOf_le 2 _).trans inf_le_right)
  have hVab : IsElemAbelian 2 (str86V2 L1 L2 S (lam 0)) :=
    (str86_Vv_abelian hI).2.2.2.2 hb5 (lam 0) hP.linear
  have hVstabα : str86V2 L1 L2 S (lam 0) ≤ stab (lam (str86CritB L1 L2 S)) :=
    str86_V2_le_stab_lam_of_le_stab hI hP hodd hb5 hVstab1 hZα'V
  have hVle : str86V2 L1 L2 S (lam 0) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)) ⊓
        stab (lam (str86CritB L1 L2 S))) :=
    (str86_graph_TI hI).1 (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S)) hE
      (str86V2 L1 L2 S (lam 0)) (CFSG.Open.IsElemAbelian.isPGroup hVab)
      (le_inf hVstab1 hVstabα)
  have hVS' : str86V2 L1 L2 S (lam 0) ≤
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)) ⊓
        stab (lam (str86CritB L1 L2 S - 2))) := by
    rw [inf_comm]
    exact hVS
  have hne : lam (str86CritB L1 L2 S - 2) ≠ lam (str86CritB L1 L2 S) :=
    hP.isGeo.ne (i := str86CritB L1 L2 S - 2) (j := str86CritB L1 L2 S)
      (by omega) le_rfl
  have hQ := (str86_graph_TI hI).2.1 (lam (str86CritB L1 L2 S - 1))
    (lam (str86CritB L1 L2 S - 2)) (lam (str86CritB L1 L2 S)) hB.symm hE hne
  rw [← hQ]
  exact le_inf hVS' hVle

theorem str86_critPath_odd_V2_le
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S) :
    str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) := by
  have hb3 : 3 ≤ str86CritB L1 L2 S := by omega
  have h01 : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam 0) (lam 1) :=
    hP.isGeo.adj (i := 0) (by omega)
  have hV1 : Vv (Z2 L1 L2 S) (lam 1) ≤ str86V2 L1 L2 S (lam 0) := by
    unfold str86V2
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ nbrs (lam 0)) => Vv (Z2 L1 L2 S) γ)
      (lam 1) h01 le_rfl
  have hZα'V : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      str86V2 L1 L2 S (lam 0) :=
    (str86_critPath_odd_L311ab hI hO hkm hP hodd hb3).2.2.trans (inf_le_left.trans hV1)
  exact str86_V2_le_pCoreOf_lam_sub_one hI hP hodd hb5
    (str86_V2_le_pCoreOf_lam_sub_two hI hO hP hodd hb5 hZα'V) hZα'V

end CFSG.Quasithin.Stroth

end
