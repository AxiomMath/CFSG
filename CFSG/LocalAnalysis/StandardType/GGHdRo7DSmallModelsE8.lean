module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def hdRo7DSmE8Aux_H : Fin 8 → DV 7 :=
  ![![1,1,1,1,1,1,1,1],
    ![0,0,0,0,0,0,1,2],
    ![0,0,0,0,0,0,1,1],
    ![0,0,0,0,0,1,2,0],
    ![0,0,0,0,1,2,0,0],
    ![0,0,0,1,2,0,0,0],
    ![0,0,1,2,0,0,0,0],
    ![0,1,2,0,0,0,0,0]]

private noncomputable def hdRo7DSmE8Aux_A (i : Fin 8) : Module.Dual (ZMod 3) (DV 7) :=
  dFun 1 (hdRo7DSmE8Aux_H i)

private lemma hdRo7DSmE8Aux_dB_H (i j : Fin 8) :
    dB 1 (hdRo7DSmE8Aux_H i) (hdRo7DSmE8Aux_H j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

private lemma hdRo7DSmE8Aux_A_apply (i : Fin 8) (v : DV 7) :
    hdRo7DSmE8Aux_A i v = dB 1 (hdRo7DSmE8Aux_H i) v := by
  rw [hdRo7DSmE8Aux_A, dFun_apply]
  have h2 : dB 1 (hdRo7DSmE8Aux_H i) (hdRo7DSmE8Aux_H i) = 2 := by
    have := hdRo7DSmE8Aux_dB_H i i
    fin_cases i <;> simpa using this
  rw [h2]
  have h4 : (2 : ZMod 3) * 2 = 1 := by decide
  rw [h4, one_mul]

private lemma hdRo7DSmE8Aux_hα (i : Fin 8) : hdRo7DSmE8Aux_A i (hdRo7DSmE8Aux_H i) = 2 := by
  rw [hdRo7DSmE8Aux_A_apply]
  have h := hdRo7DSmE8Aux_dB_H i i
  have hC : (CartanMatrix.E 8) i i = 2 := by
    fin_cases i <;> decide
  rw [h, hC]
  norm_num

private lemma hdRo7DSmE8Aux_hP (i j : Fin 8) :
    hdRo7DSmE8Aux_A i (hdRo7DSmE8Aux_H j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
  rw [hdRo7DSmE8Aux_A_apply, hdRo7DSmE8Aux_dB_H]

private noncomputable def hdRo7DSmE8Aux_Phi (i : Fin 8) : DGL 7 :=
  Module.reflection (hdRo7DSmE8Aux_hα i)

private lemma hdRo7DSmE8Aux_Phi_DRefl (i : Fin 8) :
    DRefl 1 (hdRo7DSmE8Aux_Phi i) (hdRo7DSmE8Aux_H i) := by
  refine ⟨?_, ?_⟩
  · rw [hdRo7DSmE8Aux_dB_H i i]
    fin_cases i <;> decide
  · intro v
    rw [hdRo7DSmE8Aux_Phi, Module.reflection_apply]
    rfl

private def hdRo7DSmE8Aux_C : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (CartanMatrix.E 8).map (Int.castRingHom (ZMod 3))

private def hdRo7DSmE8Aux_Cinv : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![![1,2,1,1,2,0,1,2],
    ![2,2,1,0,0,0,0,0],
    ![1,1,2,2,1,0,2,1],
    ![1,0,2,0,0,0,0,0],
    ![2,0,1,0,2,0,1,2],
    ![0,0,0,0,0,0,2,1],
    ![1,0,2,0,1,2,0,0],
    ![2,0,1,0,2,1,0,2]]

private lemma hdRo7DSmE8Aux_Cinv_mul : hdRo7DSmE8Aux_Cinv * hdRo7DSmE8Aux_C = 1 := by decide

private lemma hdRo7DSmE8Aux_linIndep : LinearIndependent (ZMod 3) hdRo7DSmE8Aux_H := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hC : hdRo7DSmE8Aux_C.mulVec g = 0 := by
    ext i
    have h := congrArg (hdRo7DSmE8Aux_A i) hg
    rw [map_sum, map_zero] at h
    have h' : ∑ j, g j * hdRo7DSmE8Aux_A i (hdRo7DSmE8Aux_H j) = 0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    have h'' : ∑ j, g j * ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) = 0 := by
      rw [← h']
      apply Finset.sum_congr rfl
      intro j _
      rw [hdRo7DSmE8Aux_hP]
    rw [Matrix.mulVec_apply, dotProduct]
    simpa [hdRo7DSmE8Aux_C, Matrix.map_apply, mul_comm] using h''
  have h1 : hdRo7DSmE8Aux_Cinv.mulVec (hdRo7DSmE8Aux_C.mulVec g) = 0 := by
    rw [hC, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, hdRo7DSmE8Aux_Cinv_mul, Matrix.one_mulVec] at h1
  exact congrFun h1 i

private noncomputable def hdRo7DSmE8Aux_L : CoxeterMatrix.E₈.Group →* DGL 7 :=
  CoxeterMatrix.E₈.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hdRo7DSmE8Aux_hα i),
      isLiftable_reflection_of_intCartan ggIntCartan_E₈ hdRo7DSmE8Aux_H hdRo7DSmE8Aux_A
        hdRo7DSmE8Aux_hα hdRo7DSmE8Aux_hP⟩

private lemma hdRo7DSmE8Aux_L_simple (i : Fin 8) :
    hdRo7DSmE8Aux_L (CoxeterMatrix.E₈.simple i) = hdRo7DSmE8Aux_Phi i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, hdRo7DSmE8Aux_L, CoxeterSystem.lift_apply_simple]
  rfl

private lemma hdRo7DSmE8Aux_L_range :
    hdRo7DSmE8Aux_L.range = Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₈.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1

private lemma hdRo7DSmE8Aux_L_inj : Function.Injective hdRo7DSmE8Aux_L := by
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 8) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
    rwa [TauCeti.DynkinType.cartanMatrix_E8] at h
  exact ggCartanFaithful_of_isFiniteType (p := 3) (hα := hdRo7DSmE8Aux_hα) (hP := hdRo7DSmE8Aux_hP)
    (by decide) hFT ggIntCartan_E₈ hdRo7DSmE8Aux_linIndep

private lemma hdRo7DSmE8Aux_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma hdRo7DSmE8Aux_H_mem (i : Fin 8) : hdRo7DSmE8Aux_H i ∈ dPhiE8 1 := by
  fin_cases i <;> (simp only [dPhiE8, Set.mem_setOf_eq]; decide)

private lemma hdRo7DSmE8Aux_Phi_mem (i : Fin 8) :
    hdRo7DSmE8Aux_Phi i ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) :=
  Subgroup.subset_closure ⟨i, rfl⟩

private def hdRo7DSmE8Aux_e01 : DV 7 := dE 7 0 + dE 7 1

private lemma hdRo7DSmE8Aux_e01_0 : hdRo7DSmE8Aux_e01 0 ≠ 0 := by decide

private lemma hdRo7DSmE8Aux_e01_supp : dSupp hdRo7DSmE8Aux_e01 = 1 := by decide

private lemma hdRo7DSmE8Aux_P_le (hGen : DSmGenLeaf) :
    ∀ a, DSP 3 (dStd 7) a → a ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  apply hGen 7 (by norm_num)
  · intro i j hij
    have hroot_all : ∀ i j : Fin 7, j.val = i.val + 1 →
        ∃ k : Fin 8, dE 7 i.succ - dE 7 j.succ = hdRo7DSmE8Aux_H k := by decide
    obtain ⟨k, hk⟩ := hroot_all i j hij
    rw [hk]
    exact ⟨hdRo7DSmE8Aux_Phi k, hdRo7DSmE8Aux_Phi_mem k, hdRo7DSmE8Aux_Phi_DRefl k⟩
  · intro i j hi hj
    have hroot_all : ∀ i j : Fin 7, i.val + 2 = 7 → j.val + 1 = 7 →
        ∃ k : Fin 8, dE 7 i.succ + dE 7 j.succ = hdRo7DSmE8Aux_H k := by decide
    obtain ⟨k, hk⟩ := hroot_all i j hi hj
    rw [hk]
    exact ⟨hdRo7DSmE8Aux_Phi k, hdRo7DSmE8Aux_Phi_mem k, hdRo7DSmE8Aux_Phi_DRefl k⟩

private def hdRo7DSmE8Aux_c0 : Fin 8 → ZMod 3 := ![1,1,2,2,2,2,2,2]

private lemma hdRo7DSmE8Aux_c0_sign (i : Fin 8) :
    hdRo7DSmE8Aux_c0 i = 1 ∨ hdRo7DSmE8Aux_c0 i = -1 := by
  fin_cases i <;> decide

private lemma hdRo7DSmE8Aux_c0_prod : ∏ i, hdRo7DSmE8Aux_c0 i = 1 := by decide

private lemma hdRo7DSmE8Aux_c0_DSPData : DSPData (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 :=
  ⟨rfl, rfl, hdRo7DSmE8Aux_c0_sign, hdRo7DSmE8Aux_c0_prod⟩

private def hdRo7DSmE8Aux_g0 : DV 7 := ![1,1,2,2,2,2,2,2]

private lemma hdRo7DSmE8Aux_dAct_c0_H0 :
    dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 (hdRo7DSmE8Aux_H 0) =
      hdRo7DSmE8Aux_g0 := by
  decide

private lemma hdRo7DSmE8Aux_dRef_g0_H0 :
    dRef 1 hdRo7DSmE8Aux_g0 (hdRo7DSmE8Aux_H 0) = -hdRo7DSmE8Aux_e01 := by
  decide

private lemma hdRo7DSmE8Aux_s0_DRefl :
    DRefl 1 (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign *
      hdRo7DSmE8Aux_Phi 0 *
      (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign)⁻¹)
      hdRo7DSmE8Aux_g0 := by
  have h := dRefl_conj_dActL (ρ := 1) (σ := (1 : Equiv.Perm (Fin 8))) (c := hdRo7DSmE8Aux_c0)
    rfl hdRo7DSmE8Aux_c0_sign (hdRo7DSmE8Aux_Phi_DRefl 0)
  rwa [hdRo7DSmE8Aux_dAct_c0_H0] at h

private noncomputable def hdRo7DSmE8Aux_tau : DGL 7 :=
  (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign *
    hdRo7DSmE8Aux_Phi 0 *
    (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign)⁻¹) *
    hdRo7DSmE8Aux_Phi 0 *
  ((dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign *
    hdRo7DSmE8Aux_Phi 0 *
    (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign)⁻¹))⁻¹

private lemma hdRo7DSmE8Aux_tau_DRefl : DRefl 1 hdRo7DSmE8Aux_tau hdRo7DSmE8Aux_e01 := by
  unfold hdRo7DSmE8Aux_tau
  have h := dRefl_conj hdRo7DSmE8Aux_s0_DRefl (hdRo7DSmE8Aux_Phi_DRefl 0)
  rw [hdRo7DSmE8Aux_dRef_g0_H0] at h
  exact (dRefl_neg_iff (h := hdRo7DSmE8Aux_e01)).mp h

private lemma hdRo7DSmE8Aux_s0_mem
    (hP : ∀ a, DSP 3 (dStd 7) a → a ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi)) :
    dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign *
      hdRo7DSmE8Aux_Phi 0 *
      (dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign)⁻¹ ∈
      Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  have ha : dActL (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_c0 hdRo7DSmE8Aux_c0_sign ∈
      Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) :=
    hP _ (dsp_dActL hdRo7DSmE8Aux_c0_DSPData)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (hdRo7DSmE8Aux_Phi_mem 0))
    (Subgroup.inv_mem _ ha)

private lemma hdRo7DSmE8Aux_tau_mem
    (hP : ∀ a, DSP 3 (dStd 7) a → a ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi)) :
    hdRo7DSmE8Aux_tau ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  unfold hdRo7DSmE8Aux_tau
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hdRo7DSmE8Aux_s0_mem hP) (hdRo7DSmE8Aux_Phi_mem 0))
    (Subgroup.inv_mem _ (hdRo7DSmE8Aux_s0_mem hP))

private lemma hdRo7DSmE8Aux_mem_of_conj
    (hP : ∀ a, DSP 3 (dStd 7) a → a ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi))
    {σ : Equiv.Perm (Fin 8)} {c : Fin 8 → ZMod 3} (hd : DSPData σ c)
    {r : DGL 7} {h : DV 7} (hr : DRefl 1 r h)
    {s : DGL 7} {g : DV 7} (hs : DRefl 1 s g)
    (hsK : s ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi))
    (hact : dAct σ c g = h ∨ dAct σ c g = -h) :
    r ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  have ha : dActL σ c hd.2.2.1 ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) :=
    hP _ (dsp_dActL hd)
  have hmem : dActL σ c hd.2.2.1 * s * (dActL σ c hd.2.2.1)⁻¹ ∈
      Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hsK) (Subgroup.inv_mem _ ha)
  have hconj := dRefl_conj_dActL (ρ := 1) (σ := σ) (c := c) hd.1 hd.2.2.1 hs
  rcases hact with hact | hact
  · rw [hact] at hconj
    rw [dRefl_unique hr hconj]
    exact hmem
  · rw [hact] at hconj
    rw [dRefl_unique hr ((dRefl_neg_iff (h := h)).mp hconj)]
    exact hmem

private lemma hdRo7DSmE8Aux_mem_of_dRefl (hGen : DSmGenLeaf) (hT : DSmTransLeaf)
    {h : DV 7} (hh : h ∈ dPhiE8 1) {r : DGL 7} (hr : DRefl 1 r h) :
    r ∈ Subgroup.closure (Set.range hdRo7DSmE8Aux_Phi) := by
  have hP := hdRo7DSmE8Aux_P_le hGen
  rcases hh with hD | hS
  · by_cases h0 : h 0 = 0
    · exact hP r (dsp_of_dRefl_int hr h0 hD)
    · have hsupp : dSupp h = 1 := by
        rcases (dIsD_iff h).mp hD with ⟨h0', _⟩ | ⟨_, hs⟩
        · exact absurd h0' h0
        · exact hs
      obtain ⟨σ, c, hd, hact⟩ := hT.1 7 hdRo7DSmE8Aux_e01 h hdRo7DSmE8Aux_e01_0 h0
        (by rw [hdRo7DSmE8Aux_e01_supp, hsupp]) (by rw [hdRo7DSmE8Aux_e01_supp]; omega)
      exact hdRo7DSmE8Aux_mem_of_conj hP hd hr hdRo7DSmE8Aux_tau_DRefl
        (hdRo7DSmE8Aux_tau_mem hP) hact
  · have h0 : h 0 ≠ 0 := hS.1
    have hsupp : dSupp h = 7 := ((dIsS_iff 1 h).mp hS).2.1
    have hH0supp : dSupp (hdRo7DSmE8Aux_H 0) = 7 := by decide
    have hH0sgn : dSgn (hdRo7DSmE8Aux_H 0) = 1 := by decide
    have hsgn : dSgn h = 1 := hS.2.2
    have hH00 : (hdRo7DSmE8Aux_H 0) 0 ≠ 0 := by decide
    obtain ⟨σ, c, hd, hact⟩ := hT.1 7 (hdRo7DSmE8Aux_H 0) h hH00 h0
      (by rw [hH0supp, hsupp]) (fun _ => by rw [hH0sgn, hsgn])
    exact hdRo7DSmE8Aux_mem_of_conj hP hd hr (hdRo7DSmE8Aux_Phi_DRefl 0)
      (hdRo7DSmE8Aux_Phi_mem 0) hact

private lemma hdRo7DSmE8Aux_range_eq_group (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    hdRo7DSmE8Aux_L.range = dGroup 1 (dPhiE8 1) := by
  apply le_antisymm
  · rw [hdRo7DSmE8Aux_L_range]
    exact (Subgroup.closure_le _).mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact Subgroup.subset_closure
        ⟨hdRo7DSmE8Aux_H i, hdRo7DSmE8Aux_H_mem i, hdRo7DSmE8Aux_Phi_DRefl i⟩)
  · rw [dGroup, Subgroup.closure_le]
    rintro r ⟨h, hh, hr⟩
    show r ∈ hdRo7DSmE8Aux_L.range
    rw [hdRo7DSmE8Aux_L_range]
    exact hdRo7DSmE8Aux_mem_of_dRefl hGen hT hh hr

private lemma hdRo7DSmE8Aux_linWeyl1 (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    ZS.LinWeyl 3 (dGroup 1 (dPhiE8 1)) := by
  let K := dGroup 1 (dPhiE8 1)
  let F : CoxeterMatrix.E₈.Group →* ↥K :=
    { toFun := fun x => ⟨hdRo7DSmE8Aux_L x, by
        rw [show K = hdRo7DSmE8Aux_L.range from
          (hdRo7DSmE8Aux_range_eq_group hGen hT).symm]
        exact ⟨x, rfl⟩⟩
      map_one' := by ext; simp [hdRo7DSmE8Aux_L]
      map_mul' x y := by ext; simp [hdRo7DSmE8Aux_L] }
  have hF_inj : Function.Injective F := by
    intro x y h
    exact hdRo7DSmE8Aux_L_inj (congrArg Subtype.val h)
  have hF_surj : Function.Surjective F := by
    intro a
    have ha : (a : DGL 7) ∈ hdRo7DSmE8Aux_L.range := by
      rw [hdRo7DSmE8Aux_range_eq_group hGen hT]; exact a.2
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨Fin 8, CoxeterMatrix.E₈, GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inr ⟨Equiv.refl _, (hdRo7DSmE8Aux_reindex_refl CoxeterMatrix.E₈).symm⟩)), ?_⟩
  have hF_bij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
  refine ⟨MulEquiv.ofBijective F hF_bij, ?_⟩
  intro i
  rw [MulEquiv.ofBijective_apply]
  have hcoe : ((F (CoxeterMatrix.E₈.simple i) : ↥K) : DGL 7) = hdRo7DSmE8Aux_Phi i := by
    change hdRo7DSmE8Aux_L (CoxeterMatrix.E₈.simple i) = hdRo7DSmE8Aux_Phi i
    exact hdRo7DSmE8Aux_L_simple i
  rw [hcoe]
  exact ggLinRefl_of_dRefl (hdRo7DSmE8Aux_Phi_DRefl i)

private def hdRo7DSmE8Aux_cb : Fin 8 → ZMod 3 := ![1,2,1,1,1,1,1,1]

private lemma hdRo7DSmE8Aux_cb_zero : hdRo7DSmE8Aux_cb 0 = 1 := rfl

private lemma hdRo7DSmE8Aux_cb_ne (i : Fin 8) : hdRo7DSmE8Aux_cb i ≠ 0 := by
  fin_cases i <;> decide

private lemma hdRo7DSmE8Aux_cb_sign (i : Fin 8) :
    hdRo7DSmE8Aux_cb i = 1 ∨ hdRo7DSmE8Aux_cb i = -1 := by
  fin_cases i <;> decide

private lemma hdRo7DSmE8Aux_cb_sq (j : Fin 8) : hdRo7DSmE8Aux_cb j * hdRo7DSmE8Aux_cb j = 1 := by
  fin_cases j <;> decide

private lemma hdRo7DSmE8Aux_cb_mul_ne (i : Fin 8) (x : ZMod 3) :
    hdRo7DSmE8Aux_cb i * x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h hx; exact h (by rw [hx, mul_zero])
  · intro hx h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hdRo7DSmE8Aux_cb_ne i)
    · exact hx h'

private lemma hdRo7DSmE8Aux_cb_mul_eq (i : Fin 8) (x : ZMod 3) :
    hdRo7DSmE8Aux_cb i * x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hdRo7DSmE8Aux_cb_ne i)
    · exact h'
  · intro h; rw [h, mul_zero]

private lemma hdRo7DSmE8Aux_dAct_cb_cb (h : DV 7) :
    dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb
      (dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h) = h := by
  funext j
  show hdRo7DSmE8Aux_cb j * (hdRo7DSmE8Aux_cb j * h j) = h j
  rw [← mul_assoc, hdRo7DSmE8Aux_cb_sq, one_mul]

private lemma hdRo7DSmE8Aux_dSgn_smul_cb (h : DV 7) :
    dSgn (fun j => hdRo7DSmE8Aux_cb j * h j) = -dSgn h := by
  unfold dSgn
  calc
    ∏ i : Fin 7, ((hdRo7DSmE8Aux_cb 0 * h 0) * (hdRo7DSmE8Aux_cb i.succ * h i.succ))
        = (∏ i : Fin 7, (hdRo7DSmE8Aux_cb 0 * hdRo7DSmE8Aux_cb i.succ)) *
          ∏ i : Fin 7, (h 0 * h i.succ) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i _
          ring
    _ = (∏ i : Fin 7, hdRo7DSmE8Aux_cb i.succ) * dSgn h := by
          congr 1
    _ = -dSgn h := by
          rw [show (∏ i : Fin 7, hdRo7DSmE8Aux_cb i.succ) = -1 by decide]
          exact neg_one_mul _

private lemma hdRo7DSmE8Aux_dSgn_dAct_cb (h : DV 7) :
    dSgn (dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h) = -dSgn h :=
  hdRo7DSmE8Aux_dSgn_smul_cb h

private lemma hdRo7DSmE8Aux_dIsD_dAct_cb (h : DV 7) :
    dIsD (dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h) ↔ dIsD h := by
  unfold dIsD
  constructor
  · rintro ⟨i, j, hij, hi, hj, hk⟩
    exact ⟨i, j, hij, (hdRo7DSmE8Aux_cb_mul_ne i (h i)).mp hi,
      (hdRo7DSmE8Aux_cb_mul_ne j (h j)).mp hj,
      fun k hki hkj =>
        (hdRo7DSmE8Aux_cb_mul_eq k (h k)).mp
          (show hdRo7DSmE8Aux_cb k * h k = 0 from hk k hki hkj)⟩
  · rintro ⟨i, j, hij, hi, hj, hk⟩
    exact ⟨i, j, hij, (hdRo7DSmE8Aux_cb_mul_ne i (h i)).mpr hi,
      (hdRo7DSmE8Aux_cb_mul_ne j (h j)).mpr hj,
      fun k hki hkj => by
        show hdRo7DSmE8Aux_cb k * h k = 0
        rw [hk k hki hkj, mul_zero]⟩

private lemma hdRo7DSmE8Aux_dIsS_dAct_cb (ε : ZMod 3) (h : DV 7) :
    dIsS (-ε) (dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h) ↔ dIsS ε h := by
  unfold dIsS
  have h0 : dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h 0 = h 0 := by
    show hdRo7DSmE8Aux_cb 0 * h 0 = h 0
    rw [hdRo7DSmE8Aux_cb_zero, one_mul]
  have hall : (∀ i : Fin 7, dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h i.succ ≠ 0) ↔
      ∀ i : Fin 7, h i.succ ≠ 0 := by
    constructor
    · intro H i
      exact (hdRo7DSmE8Aux_cb_mul_ne i.succ (h i.succ)).mp (H i)
    · intro H i
      exact (hdRo7DSmE8Aux_cb_mul_ne i.succ (h i.succ)).mpr (H i)
  have hsgn : dSgn (dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h) = -dSgn h :=
    hdRo7DSmE8Aux_dSgn_dAct_cb h
  rw [h0, hall, hsgn, neg_inj]

private lemma hdRo7DSmE8Aux_hPhi_E8_neg :
    ∀ h : DV 7, h ∈ dPhiE8 (-1) ↔
      ∃ g ∈ dPhiE8 1, dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb g = h := by
  intro h
  constructor
  · intro hh
    refine ⟨dAct (1 : Equiv.Perm (Fin 8)) hdRo7DSmE8Aux_cb h, ?_, hdRo7DSmE8Aux_dAct_cb_cb h⟩
    rcases hh with hD | hS
    · exact Or.inl ((hdRo7DSmE8Aux_dIsD_dAct_cb h).mpr hD)
    · exact Or.inr (by simpa using (hdRo7DSmE8Aux_dIsS_dAct_cb (-1) h).mpr hS)
  · rintro ⟨g, hg, rfl⟩
    rcases hg with hD | hS
    · exact Or.inl ((hdRo7DSmE8Aux_dIsD_dAct_cb g).mpr hD)
    · exact Or.inr ((hdRo7DSmE8Aux_dIsS_dAct_cb 1 g).mpr hS)

private lemma hdRo7DSmE8Aux_linWeyl2 (hGen : DSmGenLeaf) (hT : DSmTransLeaf) :
    ZS.LinWeyl 3 (dGroup 1 (dPhiE8 (-1))) :=
  linWeyl_dGroup_dAct (ρ := 1) (σ := (1 : Equiv.Perm (Fin 8))) (c := hdRo7DSmE8Aux_cb)
    rfl hdRo7DSmE8Aux_cb_sign hdRo7DSmE8Aux_hPhi_E8_neg (hdRo7DSmE8Aux_linWeyl1 hGen hT)

theorem dSmModelsE8_holds : DSmModelsE8Leaf := by
  intro hGen hT
  exact ⟨hdRo7DSmE8Aux_linWeyl1 hGen hT, hdRo7DSmE8Aux_linWeyl2 hGen hT⟩

end CFSG.StandardType.HdRo7D.Small
