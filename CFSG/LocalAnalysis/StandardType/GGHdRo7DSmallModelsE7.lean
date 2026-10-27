module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def hdRo7DSmE7Aux_H : Fin 7 → DV 6 :=
  ![![1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 1, 2],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, 2, 0],
    ![0, 0, 0, 1, 2, 0, 0],
    ![0, 0, 1, 2, 0, 0, 0],
    ![0, 1, 2, 0, 0, 0, 0]]

private noncomputable def hdRo7DSmE7Aux_A (i : Fin 7) : Module.Dual (ZMod 3) (DV 6) :=
  dFun 2 (hdRo7DSmE7Aux_H i)

private lemma hdRo7DSmE7Aux_dB_self_ne (i : Fin 7) :
    dB 2 (hdRo7DSmE7Aux_H i) (hdRo7DSmE7Aux_H i) ≠ 0 := by
  fin_cases i <;> decide

private lemma hdRo7DSmE7Aux_pairing (i j : Fin 7) :
    hdRo7DSmE7Aux_A i (hdRo7DSmE7Aux_H j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma hdRo7DSmE7Aux_hα (i : Fin 7) :
    hdRo7DSmE7Aux_A i (hdRo7DSmE7Aux_H i) = 2 := by
  rw [hdRo7DSmE7Aux_pairing]
  fin_cases i <;> decide

private noncomputable def hdRo7DSmE7Aux_Phi (i : Fin 7) : DGL 6 :=
  Module.reflection (hdRo7DSmE7Aux_hα i)

private lemma hdRo7DSmE7Aux_Phi_dRefl (i : Fin 7) :
    DRefl 2 (hdRo7DSmE7Aux_Phi i) (hdRo7DSmE7Aux_H i) := by
  refine ⟨hdRo7DSmE7Aux_dB_self_ne i, fun v => ?_⟩
  rw [hdRo7DSmE7Aux_Phi, Module.reflection_apply, hdRo7DSmE7Aux_A, dFun_apply]
  rfl

private def hdRo7DSmE7Aux_C : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  (CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))

private def hdRo7DSmE7Aux_Cinv : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  ![![2, 2, 0, 1, 0, 2, 1],
    ![2, 2, 1, 0, 0, 0, 0],
    ![0, 1, 0, 2, 0, 1, 2],
    ![1, 0, 2, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 1],
    ![2, 0, 1, 0, 2, 1, 2],
    ![1, 0, 2, 0, 1, 2, 0]]

private lemma hdRo7DSmE7Aux_Cinv_mul : hdRo7DSmE7Aux_Cinv * hdRo7DSmE7Aux_C = 1 := by decide

private lemma hdRo7DSmE7Aux_linIndep : LinearIndependent (ZMod 3) hdRo7DSmE7Aux_H := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hC : hdRo7DSmE7Aux_C.mulVec g = 0 := by
    ext i
    have h := congrArg (hdRo7DSmE7Aux_A i) hg
    rw [map_sum, map_zero] at h
    have h' : ∑ j, g j * hdRo7DSmE7Aux_A i (hdRo7DSmE7Aux_H j) = 0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    have h'' : ∑ j, g j * ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) = 0 := by
      rw [← h']
      apply Finset.sum_congr rfl
      intro j _
      rw [hdRo7DSmE7Aux_pairing]
    rw [Matrix.mulVec_apply, dotProduct]
    simpa [hdRo7DSmE7Aux_C, Matrix.map_apply, mul_comm] using h''
  have h1 : hdRo7DSmE7Aux_Cinv.mulVec (hdRo7DSmE7Aux_C.mulVec g) = 0 := by
    rw [hC, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, hdRo7DSmE7Aux_Cinv_mul, Matrix.one_mulVec] at h1
  exact congrFun h1 i

private lemma hdRo7DSmE7Aux_φ_isRefl (i : Fin 7) : ZS.IsRefl 3 (hdRo7DSmE7Aux_Phi i) := by
  have h : IsReflLin (hdRo7DSmE7Aux_Phi i) :=
    ⟨hdRo7DSmE7Aux_H i, hdRo7DSmE7Aux_A i, hdRo7DSmE7Aux_hα i, rfl⟩
  exact (ggLinRefl_iff_isReflLin _).mpr h

private lemma hdRo7DSmE7Aux_F_inj :
    Function.Injective (CoxeterMatrix.E₇.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hdRo7DSmE7Aux_hα i),
        isLiftable_reflection_of_intCartan ggIntCartan_E₇ hdRo7DSmE7Aux_H hdRo7DSmE7Aux_A
          hdRo7DSmE7Aux_hα hdRo7DSmE7Aux_pairing⟩) := by
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 7) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rwa [TauCeti.DynkinType.cartanMatrix_E7] at h
  exact ggCartanFaithful_of_isFiniteType (p := 3) (hα := hdRo7DSmE7Aux_hα)
    (hP := hdRo7DSmE7Aux_pairing) (by decide) hFT ggIntCartan_E₇ hdRo7DSmE7Aux_linIndep

private noncomputable def hdRo7DSmE7Aux_L : CoxeterMatrix.E₇.Group →* DGL 6 :=
  CoxeterMatrix.E₇.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hdRo7DSmE7Aux_hα i),
      isLiftable_reflection_of_intCartan ggIntCartan_E₇ hdRo7DSmE7Aux_H hdRo7DSmE7Aux_A
        hdRo7DSmE7Aux_hα hdRo7DSmE7Aux_pairing⟩

private lemma hdRo7DSmE7Aux_L_simple (i : Fin 7) :
    hdRo7DSmE7Aux_L (CoxeterMatrix.E₇.simple i) = hdRo7DSmE7Aux_Phi i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, hdRo7DSmE7Aux_L, CoxeterSystem.lift_apply_simple]
  rfl

private lemma hdRo7DSmE7Aux_L_range :
    hdRo7DSmE7Aux_L.range = Subgroup.closure (Set.range hdRo7DSmE7Aux_Phi) := by
  rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₇.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1

private lemma hdRo7DSmE7Aux_L_inj : Function.Injective hdRo7DSmE7Aux_L :=
  hdRo7DSmE7Aux_F_inj

private lemma hdRo7DSmE7Aux_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private noncomputable def hdRo7DSmE7Aux_K : Subgroup (DGL 6) :=
  Subgroup.closure (Set.range hdRo7DSmE7Aux_Phi)

private lemma hdRo7DSmE7Aux_Phi_mem_K (i : Fin 7) :
    hdRo7DSmE7Aux_Phi i ∈ hdRo7DSmE7Aux_K :=
  Subgroup.subset_closure ⟨i, rfl⟩

private lemma hdRo7DSmE7Aux_dRefl_one_iff {r : DGL 6} {h : DV 6} (h0 : h 0 = 0) :
    DRefl 1 r h ↔ DRefl 2 r h := by
  simp [DRefl, dRef, dB, h0]

private lemma hdRo7DSmE7Aux_dRefl_congr {ρ : ZMod 3} {r : DGL 6} {h h' : DV 6}
    (hh : h = h') (hr : DRefl ρ r h) : DRefl ρ r h' := by
  rw [hh] at hr
  exact hr

private lemma hdRo7DSmE7Aux_H_mem (i : Fin 7) :
    hdRo7DSmE7Aux_H i ∈ dPhiE7 1 := by
  fin_cases i <;> simp only [dPhiE7, Set.mem_setOf_eq] <;> decide

private lemma hdRo7DSmE7Aux_H_zero {k : Fin 7} (hk : k ≠ 0) :
    hdRo7DSmE7Aux_H k 0 = 0 := by
  fin_cases k
  · exact absurd rfl hk
  all_goals decide

private lemma hdRo7DSmE7Aux_gen_of_H {k : Fin 7} {i j : Fin 6} (hk : k ≠ 0)
    (h : hdRo7DSmE7Aux_H k = dE 6 i.succ - dE 6 j.succ) :
    ∃ r ∈ hdRo7DSmE7Aux_K, DRefl 1 r (dE 6 i.succ - dE 6 j.succ) :=
  ⟨hdRo7DSmE7Aux_Phi k, hdRo7DSmE7Aux_Phi_mem_K k,
    (hdRo7DSmE7Aux_dRefl_one_iff (by rw [← h]; exact hdRo7DSmE7Aux_H_zero hk)).mpr
      (hdRo7DSmE7Aux_dRefl_congr h (hdRo7DSmE7Aux_Phi_dRefl k))⟩

private lemma hdRo7DSmE7Aux_gen_adj (i j : Fin 6) (hij : j.val = i.val + 1) :
    ∃ r ∈ hdRo7DSmE7Aux_K, DRefl 1 r (dE 6 i.succ - dE 6 j.succ) := by
  fin_cases i
  · obtain rfl : j = 1 := Fin.ext (by simpa using hij)
    exact hdRo7DSmE7Aux_gen_of_H (k := 6) (by decide) (by decide)
  · obtain rfl : j = 2 := Fin.ext (by simpa using hij)
    exact hdRo7DSmE7Aux_gen_of_H (k := 5) (by decide) (by decide)
  · obtain rfl : j = 3 := Fin.ext (by simpa using hij)
    exact hdRo7DSmE7Aux_gen_of_H (k := 4) (by decide) (by decide)
  · obtain rfl : j = 4 := Fin.ext (by simpa using hij)
    exact hdRo7DSmE7Aux_gen_of_H (k := 3) (by decide) (by decide)
  · obtain rfl : j = 5 := Fin.ext (by simpa using hij)
    exact hdRo7DSmE7Aux_gen_of_H (k := 1) (by decide) (by decide)
  · exfalso
    have hlt : j.val < 6 := j.isLt
    have hv : j.val = 6 := by simpa using hij
    omega

private lemma hdRo7DSmE7Aux_gen_sum (i j : Fin 6) (hi : i.val + 2 = 6) (hj : j.val + 1 = 6) :
    ∃ r ∈ hdRo7DSmE7Aux_K, DRefl 1 r (dE 6 i.succ + dE 6 j.succ) := by
  have hi4 : i.val = 4 := by omega
  have hj5 : j.val = 5 := by omega
  have hi' : i = 4 := Fin.ext (by simpa using hi4)
  have hj' : j = 5 := Fin.ext (by simpa using hj5)
  rw [hi', hj']
  exact ⟨hdRo7DSmE7Aux_Phi 2, hdRo7DSmE7Aux_Phi_mem_K 2,
    (hdRo7DSmE7Aux_dRefl_one_iff (by decide)).mpr
      (hdRo7DSmE7Aux_dRefl_congr (by decide) (hdRo7DSmE7Aux_Phi_dRefl 2))⟩

private lemma hdRo7DSmE7Aux_dsp_mem (hGen : DSmGenLeaf) {a : DGL 6}
    (ha : DSP 3 (dStd 6) a) : a ∈ hdRo7DSmE7Aux_K :=
  hGen 6 (by norm_num) hdRo7DSmE7Aux_K
    (fun i j hij => hdRo7DSmE7Aux_gen_adj i j hij)
    (fun i j hi hj => hdRo7DSmE7Aux_gen_sum i j hi hj) a ha

private def hdRo7DSmE7Aux_cs : Fin 7 → ZMod 3 := fun i => if i = 0 then 1 else -1

private def hdRo7DSmE7Aux_g : DV 6 := ![1, 2, 2, 2, 2, 2, 2]

private lemma hdRo7DSmE7Aux_cs_zero : hdRo7DSmE7Aux_cs 0 = 1 := by decide

private lemma hdRo7DSmE7Aux_cs_sign (i : Fin 7) :
    hdRo7DSmE7Aux_cs i = 1 ∨ hdRo7DSmE7Aux_cs i = -1 := by
  unfold hdRo7DSmE7Aux_cs
  split <;> decide

private lemma hdRo7DSmE7Aux_cs_prod : ∏ i : Fin 7, hdRo7DSmE7Aux_cs i = 1 := by decide

private lemma hdRo7DSmE7Aux_dspData_cs :
    DSPData (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs :=
  ⟨rfl, hdRo7DSmE7Aux_cs_zero, hdRo7DSmE7Aux_cs_sign, hdRo7DSmE7Aux_cs_prod⟩

private lemma hdRo7DSmE7Aux_cs_act_H :
    dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs (hdRo7DSmE7Aux_H 0) = hdRo7DSmE7Aux_g := by
  ext k
  fin_cases k <;> decide

private lemma hdRo7DSmE7Aux_dRef_H_g :
    dRef 2 (hdRo7DSmE7Aux_H 0) hdRo7DSmE7Aux_g = -(dE 6 0) := by
  ext k
  fin_cases k <;> decide

private lemma hdRo7DSmE7Aux_conj_e0_mem (hGen : DSmGenLeaf) :
    ∃ t ∈ hdRo7DSmE7Aux_K, DRefl 2 t (-(dE 6 0)) := by
  have hd := hdRo7DSmE7Aux_dspData_cs
  have hwK : dActL (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs hd.2.2.1 ∈ hdRo7DSmE7Aux_K :=
    hdRo7DSmE7Aux_dsp_mem hGen (dsp_dActL hd)
  have hPhi0 := hdRo7DSmE7Aux_Phi_mem_K 0
  have hs : DRefl 2 (dActL (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs hd.2.2.1 *
      hdRo7DSmE7Aux_Phi 0 * (dActL (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs hd.2.2.1)⁻¹)
      hdRo7DSmE7Aux_g := by
    have hc := dRefl_conj_dActL (σ := Equiv.refl (Fin 7)) (c := hdRo7DSmE7Aux_cs) rfl hd.2.2.1
      (hdRo7DSmE7Aux_Phi_dRefl 0)
    rw [hdRo7DSmE7Aux_cs_act_H] at hc
    exact hc
  refine ⟨hdRo7DSmE7Aux_Phi 0 *
    (dActL (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs hd.2.2.1 * hdRo7DSmE7Aux_Phi 0 *
      (dActL (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_cs hd.2.2.1)⁻¹) * (hdRo7DSmE7Aux_Phi 0)⁻¹,
    ?_, ?_⟩
  · exact hdRo7DSmE7Aux_K.mul_mem
      (hdRo7DSmE7Aux_K.mul_mem hPhi0
        (hdRo7DSmE7Aux_K.mul_mem
          (hdRo7DSmE7Aux_K.mul_mem hwK hPhi0)
          (hdRo7DSmE7Aux_K.inv_mem hwK)))
      (hdRo7DSmE7Aux_K.inv_mem hPhi0)
  · have ht := dRefl_conj (hdRo7DSmE7Aux_Phi_dRefl 0) hs
    rw [hdRo7DSmE7Aux_dRef_H_g] at ht
    exact ht

private lemma hdRo7DSmE7Aux_isO_eq (h : DV 6) (h0 : h 0 ≠ 0) (hO : dIsO h) :
    h = dE 6 0 ∨ h = -dE 6 0 := by
  have hsupp : dSupp h = 0 := by
    rcases (dIsO_iff h).mp hO with ⟨hz, -⟩ | ⟨-, hs⟩
    · exact absurd hz h0
    · exact hs
  have hE := eq_smul_dE_of_dSupp_zero (n := 6) hsupp
  have hpm : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  rcases hpm (h 0) h0 with h1 | h1
  · left; rw [hE, h1, one_smul]
  · right; rw [hE, h1]; simp

private lemma hdRo7DSmE7Aux_gen_mem_isO (hGen : DSmGenLeaf) {r : DGL 6} {h : DV 6}
    (h0 : h 0 ≠ 0) (hO : dIsO h) (hr : DRefl 2 r h) : r ∈ hdRo7DSmE7Aux_K := by
  obtain ⟨t, htK, ht⟩ := hdRo7DSmE7Aux_conj_e0_mem hGen
  rcases hdRo7DSmE7Aux_isO_eq h h0 hO with heq | heq
  · rw [heq] at hr
    rw [dRefl_unique hr (dRefl_neg_iff.mp ht)]
    exact htK
  · rw [heq] at hr
    rw [dRefl_unique hr ht]
    exact htK

private lemma hdRo7DSmE7Aux_gen_mem_isS (hGen : DSmGenLeaf) (hT : DSmTransLeaf) {r : DGL 6}
    {h : DV 6} (hS : dIsS 1 h) (hr : DRefl 2 r h) : r ∈ hdRo7DSmE7Aux_K := by
  obtain ⟨h0, hsupp, hsgn⟩ := (dIsS_iff 1 h).mp hS
  obtain ⟨σ, c, hd, hgt⟩ := hT.1 6 (hdRo7DSmE7Aux_H 0) h (by decide) h0
    (by rw [hsupp]; decide) (by intro _; rw [hsgn]; decide)
  set w : DGL 6 := dActL σ c hd.2.2.1 with hwdef
  have hwK : w ∈ hdRo7DSmE7Aux_K := hdRo7DSmE7Aux_dsp_mem hGen (dsp_dActL hd)
  have hconj : DRefl 2 (w * hdRo7DSmE7Aux_Phi 0 * w⁻¹)
      (dAct σ c (hdRo7DSmE7Aux_H 0)) :=
    dRefl_conj_dActL hd.1 hd.2.2.1 (hdRo7DSmE7Aux_Phi_dRefl 0)
  have hmem : w * hdRo7DSmE7Aux_Phi 0 * w⁻¹ ∈ hdRo7DSmE7Aux_K :=
    hdRo7DSmE7Aux_K.mul_mem (hdRo7DSmE7Aux_K.mul_mem hwK (hdRo7DSmE7Aux_Phi_mem_K 0))
      (hdRo7DSmE7Aux_K.inv_mem hwK)
  rcases hgt with hgt | hgt
  · rw [hgt] at hconj
    rw [dRefl_unique hr hconj]
    exact hmem
  · rw [hgt] at hconj
    rw [dRefl_unique hr (dRefl_neg_iff.mp hconj)]
    exact hmem

private lemma hdRo7DSmE7Aux_Phi_in_dGroup (i : Fin 7) :
    hdRo7DSmE7Aux_Phi i ∈ dGroup 2 (dPhiE7 1) :=
  Subgroup.subset_closure ⟨hdRo7DSmE7Aux_H i, hdRo7DSmE7Aux_H_mem i, hdRo7DSmE7Aux_Phi_dRefl i⟩

private lemma hdRo7DSmE7Aux_gen_mem (hGen : DSmGenLeaf) (hT : DSmTransLeaf) {r : DGL 6}
    {h : DV 6} (hh : h ∈ dPhiE7 1) (hr : DRefl 2 r h) : r ∈ hdRo7DSmE7Aux_K := by
  simp only [dPhiE7, Set.mem_setOf_eq] at hh
  rcases hh with ⟨h0, hD⟩ | ⟨h0, hO⟩ | hS
  · exact hdRo7DSmE7Aux_dsp_mem hGen (dsp_of_dRefl_int hr h0 hD)
  · exact hdRo7DSmE7Aux_gen_mem_isO hGen h0 hO hr
  · exact hdRo7DSmE7Aux_gen_mem_isS hGen hT hS hr

private lemma hdRo7DSmE7Aux_range_eq (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    hdRo7DSmE7Aux_L.range = dGroup 2 (dPhiE7 1) := by
  rw [hdRo7DSmE7Aux_L_range]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact hdRo7DSmE7Aux_Phi_in_dGroup i
  · rw [dGroup, Subgroup.closure_le]
    rintro x ⟨h, hh, hr⟩
    exact hdRo7DSmE7Aux_gen_mem hGen hT hh hr

private lemma hdRo7DSmE7Aux_linWeyl (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    ZS.LinWeyl 3 (dGroup 2 (dPhiE7 1)) := by
  let A := dGroup 2 (dPhiE7 1)
  let F : CoxeterMatrix.E₇.Group →* ↥A :=
    { toFun := fun x => ⟨hdRo7DSmE7Aux_L x, by
        rw [show A = hdRo7DSmE7Aux_L.range from (hdRo7DSmE7Aux_range_eq hGen hT).symm]
        exact ⟨x, rfl⟩⟩
      map_one' := by ext; simp [hdRo7DSmE7Aux_L]
      map_mul' x y := by ext; simp [hdRo7DSmE7Aux_L] }
  have hF_inj : Function.Injective F := by
    intro x y h
    exact hdRo7DSmE7Aux_L_inj (congrArg Subtype.val h)
  have hF_surj : Function.Surjective F := by
    intro a
    have ha : (a : DGL 6) ∈ hdRo7DSmE7Aux_L.range := by
      rw [hdRo7DSmE7Aux_range_eq hGen hT]
      exact a.2
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨Fin 7, CoxeterMatrix.E₇, ?_, ?_⟩
  · exact GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inl ⟨Equiv.refl _, (hdRo7DSmE7Aux_reindex_refl CoxeterMatrix.E₇).symm⟩))
  · have hF_bij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
    refine ⟨MulEquiv.ofBijective F hF_bij, ?_⟩
    intro i
    rw [MulEquiv.ofBijective_apply]
    have hcoe : ((F (CoxeterMatrix.E₇.simple i) : ↥A) : DGL 6) = hdRo7DSmE7Aux_Phi i := by
      change hdRo7DSmE7Aux_L (CoxeterMatrix.E₇.simple i) = hdRo7DSmE7Aux_Phi i
      exact hdRo7DSmE7Aux_L_simple i
    rw [hcoe]
    exact hdRo7DSmE7Aux_φ_isRefl i

private def hdRo7DSmE7Aux_c : Fin 7 → ZMod 3 := fun i => if i = 1 then -1 else 1

private lemma hdRo7DSmE7Aux_c_zero : hdRo7DSmE7Aux_c 0 = 1 := by decide

private lemma hdRo7DSmE7Aux_c_sign (i : Fin 7) :
    hdRo7DSmE7Aux_c i = 1 ∨ hdRo7DSmE7Aux_c i = -1 := by
  unfold hdRo7DSmE7Aux_c
  split <;> decide

private lemma hdRo7DSmE7Aux_c_ne (i : Fin 7) : hdRo7DSmE7Aux_c i ≠ 0 := by
  rcases hdRo7DSmE7Aux_c_sign i with h | h <;> rw [h] <;> decide

private lemma hdRo7DSmE7Aux_c_sq (i : Fin 7) : hdRo7DSmE7Aux_c i * hdRo7DSmE7Aux_c i = 1 := by
  rcases hdRo7DSmE7Aux_c_sign i with h | h <;> rw [h] <;> decide

private lemma hdRo7DSmE7Aux_c_prod : ∏ i : Fin 6, hdRo7DSmE7Aux_c i.succ = -1 := by decide

private lemma hdRo7DSmE7Aux_dAct_apply {n : ℕ} (c : Fin (n + 1) → ZMod 3) (h : DV n)
    (j : Fin (n + 1)) : dAct (Equiv.refl (Fin (n + 1))) c h j = c j * h j := rfl

private lemma hdRo7DSmE7Aux_act_ne_iff (h : DV 6) (i : Fin 7) :
    dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h i ≠ 0 ↔ h i ≠ 0 := by
  rw [hdRo7DSmE7Aux_dAct_apply]
  constructor
  · intro hne hz
    exact hne (by rw [hz, mul_zero])
  · intro hne hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (hdRo7DSmE7Aux_c_ne i)
    · exact hne h

private lemma hdRo7DSmE7Aux_act_zero (h : DV 6) :
    dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h 0 = h 0 := by
  rw [hdRo7DSmE7Aux_dAct_apply, hdRo7DSmE7Aux_c_zero, one_mul]

private lemma hdRo7DSmE7Aux_dSupp_act (h : DV 6) :
    dSupp (dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h) = dSupp h := by
  unfold dSupp
  congr 1
  exact Finset.filter_congr (fun i _ => hdRo7DSmE7Aux_act_ne_iff h i.succ)

private lemma hdRo7DSmE7Aux_dSgn_act (h : DV 6) :
    dSgn (dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h) = -dSgn h := by
  have hpt : ∀ i : Fin 6, dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h 0 *
      dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h i.succ =
      (h 0 * h i.succ) * hdRo7DSmE7Aux_c i.succ := by
    intro i
    simp only [hdRo7DSmE7Aux_dAct_apply, hdRo7DSmE7Aux_c_zero, one_mul]
    ring
  simp only [dSgn]
  rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib,
    hdRo7DSmE7Aux_c_prod]
  ring

private lemma hdRo7DSmE7Aux_dAct_c_invol (g : DV 6) :
    dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c
      (dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c g) = g := by
  funext j
  show hdRo7DSmE7Aux_c j * (hdRo7DSmE7Aux_c j * g j) = g j
  rw [← mul_assoc, hdRo7DSmE7Aux_c_sq j, one_mul]

private lemma hdRo7DSmE7Aux_neg_one_iff (x : ZMod 3) : (-x = 1) ↔ (x = -1) := by
  revert x
  decide

private lemma hdRo7DSmE7Aux_mem_neg_iff (h : DV 6) :
    h ∈ dPhiE7 (-1) ↔ dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h ∈ dPhiE7 1 := by
  have h0 := hdRo7DSmE7Aux_act_zero h
  have hs := hdRo7DSmE7Aux_dSupp_act h
  have hg := hdRo7DSmE7Aux_dSgn_act h
  have hneg := hdRo7DSmE7Aux_neg_one_iff (dSgn h)
  simp only [dPhiE7, Set.mem_setOf_eq, h0, hs, hg, dIsD_iff, dIsO_iff, dIsS_iff, hneg]

private lemma hdRo7DSmE7Aux_hPsi (h : DV 6) :
    h ∈ dPhiE7 (-1) ↔ ∃ g ∈ dPhiE7 1, dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c g = h := by
  constructor
  · intro hh
    exact ⟨dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c h,
      (hdRo7DSmE7Aux_mem_neg_iff h).mp hh, hdRo7DSmE7Aux_dAct_c_invol h⟩
  · rintro ⟨g, hg, rfl⟩
    refine (hdRo7DSmE7Aux_mem_neg_iff
      (dAct (Equiv.refl (Fin 7)) hdRo7DSmE7Aux_c g)).mpr ?_
    simpa [hdRo7DSmE7Aux_dAct_c_invol g] using hg

private lemma hdRo7DSmE7Aux_linWeyl_neg (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    ZS.LinWeyl 3 (dGroup 2 (dPhiE7 (-1))) :=
  linWeyl_dGroup_dAct (ρ := 2) (Φ := dPhiE7 1) (Ψ := dPhiE7 (-1))
    (σ := Equiv.refl (Fin 7)) (c := hdRo7DSmE7Aux_c) rfl hdRo7DSmE7Aux_c_sign
    hdRo7DSmE7Aux_hPsi (hdRo7DSmE7Aux_linWeyl hGen hT)

theorem dSmModelsE7_holds : DSmModelsE7Leaf := by
  intro hGen hT
  exact ⟨hdRo7DSmE7Aux_linWeyl hGen hT, hdRo7DSmE7Aux_linWeyl_neg hGen hT⟩

end CFSG.StandardType.HdRo7D.Small
