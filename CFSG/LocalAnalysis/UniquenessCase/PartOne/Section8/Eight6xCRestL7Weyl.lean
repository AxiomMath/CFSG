module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwAct
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTorus
public import CFSG.RankThree.Lattice.SteinbergBIChecks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open scoped Matrix

@[expose] def triWord : List (Fin TwistTag.D4.tag.rank) := [2, 0, 1, 3]

@[expose] def longWord : List (Fin TwistTag.D4.tag.rank) := triWord ++ triWord ++ triWord

@[expose] noncomputable def twEps (eps : ℤ) :
    WeylGroup TwistTag.D4.tag :=
  if eps = 1 then 1 else (coxeterSystem TwistTag.D4.tag).wordProd longWord

@[expose] def trialityM : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]

private theorem trialityM_row_zero_l7y :
    trialityM (0 : Fin TwistTag.D4.tag.rank) = ![0, 0, 0, 1] := by
  funext j
  fin_cases j <;> decide +kernel

private theorem trialityM_row_one_l7y :
    trialityM (1 : Fin TwistTag.D4.tag.rank) = ![1, 0, 0, 0] := by
  funext j
  fin_cases j <;> decide +kernel

private theorem trialityM_row_two_l7y :
    trialityM (2 : Fin TwistTag.D4.tag.rank) = ![0, 0, 1, 0] := by
  funext j
  fin_cases j <;> decide +kernel

private theorem trialityM_row_three_l7y :
    trialityM (3 : Fin TwistTag.D4.tag.rank) = ![0, 1, 0, 0] := by
  funext j
  fin_cases j <;> decide +kernel

theorem permLattice_eq_trialityM_mulVec (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm x = trialityM *ᵥ x := by
  funext i
  fin_cases i
  · change x (TwistTag.D4.perm.symm (0 : Fin TwistTag.D4.tag.rank)) =
      (trialityM *ᵥ x) (0 : Fin TwistTag.D4.tag.rank)
    change x 3 = ∑ i : Fin 4, trialityM 0 i * x i
    rw [trialityM_row_zero_l7y, Fin.sum_univ_four]
    simp
    rfl
  · change x (TwistTag.D4.perm.symm (1 : Fin TwistTag.D4.tag.rank)) =
      (trialityM *ᵥ x) (1 : Fin TwistTag.D4.tag.rank)
    change x 0 = ∑ i : Fin 4, trialityM 1 i * x i
    rw [trialityM_row_one_l7y, Fin.sum_univ_four]
    simp
    rfl
  · change x (TwistTag.D4.perm.symm (2 : Fin TwistTag.D4.tag.rank)) =
      (trialityM *ᵥ x) (2 : Fin TwistTag.D4.tag.rank)
    change x 2 = ∑ i : Fin 4, trialityM 2 i * x i
    rw [trialityM_row_two_l7y, Fin.sum_univ_four]
    simp
    rfl
  · change x (TwistTag.D4.perm.symm (3 : Fin TwistTag.D4.tag.rank)) =
      (trialityM *ᵥ x) (3 : Fin TwistTag.D4.tag.rank)
    change x 1 = ∑ i : Fin 4, trialityM 3 i * x i
    rw [trialityM_row_three_l7y, Fin.sum_univ_four]
    simp
    rfl

private theorem wordMat_longWord_l7y :
    CFSG.RankThree.Lattice.wordMat TwistTag.D4.tag longWord = -1 := by
  rw [CFSG.RankThree.Lattice.wordMat_eq_toMat TwistTag.D4.tag longWord
    (L := [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]])
    (by decide +kernel)]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem wordProd_longWord_neg_l7y
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd longWord • v = -v := by
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, wordMat_longWord_l7y,
    Matrix.neg_mulVec, Matrix.one_mulVec]

private theorem wordProd_longWord_sq_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd longWord *
      (coxeterSystem TwistTag.D4.tag).wordProd longWord = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Fin TwistTag.D4.tag.rank → ℤ) fun v => ?_
  rw [mul_smul, wordProd_longWord_neg_l7y, wordProd_longWord_neg_l7y, neg_neg, one_smul]

private theorem wordProd_triWord_pow_three_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 3 =
      (coxeterSystem TwistTag.D4.tag).wordProd longWord := by
  rw [longWord, CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append]
  simp [pow_succ]

private theorem wordProd_triWord_pow_six_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 6 = 1 := by
  have h : (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 6 =
      ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 3) ^ 2 := by
    rw [← pow_mul]
  rw [h, wordProd_triWord_pow_three_l7y, pow_two, wordProd_longWord_sq_l7y]

private theorem triWord_mem_relWeylTwist_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd triWord ∈ relWeylTwist TwistTag.D4 := by
  have h : triWord = TwistTag.D4.orbitWord 1 ++ TwistTag.D4.orbitWord 0 := by decide +kernel
  rw [h, CoxeterSystem.wordProd_append]
  exact mul_mem (TwistTag.D4.orbitReflection_mem 1) (TwistTag.D4.orbitReflection_mem 0)

private theorem longWord_mem_relWeylTwist_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd longWord ∈ relWeylTwist TwistTag.D4 := by
  rw [← wordProd_triWord_pow_three_l7y]
  exact pow_mem triWord_mem_relWeylTwist_l7y 3

theorem twEps_smul_permLattice {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    twEps eps • permLattice TwistTag.D4.perm x = (eps • trialityM) *ᵥ x := by
  rcases heps with rfl | rfl
  · rw [permLattice_eq_trialityM_mulVec]
    have h : twEps (1 : ℤ) = 1 := by simp [twEps]
    rw [h, one_smul, one_smul]
  · rw [permLattice_eq_trialityM_mulVec]
    have h : twEps (-1 : ℤ) = (coxeterSystem TwistTag.D4.tag).wordProd longWord := by
      simp [twEps]
    rw [h]
    rw [show (coxeterSystem TwistTag.D4.tag).wordProd longWord • (trialityM *ᵥ x) =
      -(trialityM *ᵥ x) from wordProd_longWord_neg_l7y _]
    rw [neg_one_smul, Matrix.neg_mulVec]

theorem twEps_mem_relWeylTwist (eps : ℤ) :
    twEps eps ∈ relWeylTwist TwistTag.D4 := by
  by_cases h : eps = 1
  · simp [twEps, h]
  · rw [show twEps eps = (coxeterSystem TwistTag.D4.tag).wordProd longWord by simp [twEps, h]]
    exact longWord_mem_relWeylTwist_l7y

@[expose] noncomputable def cElt (L : Type) [Field L] :
    ModGL TwistTag.D4.tag L :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) L ((coxeterSystem TwistTag.D4.tag).wordProd triWord)

@[expose] noncomputable def yElt (L : Type) [Field L] :
    ModGL TwistTag.D4.tag L :=
  cElt L ^ 4

private theorem weylTuple_longWord_l7y {L : Type} [Field L]
    (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    weylTuple ((coxeterSystem TwistTag.D4.tag).wordProd longWord) b = b⁻¹ := by
  have hinv : ((coxeterSystem TwistTag.D4.tag).wordProd longWord)⁻¹ =
      (coxeterSystem TwistTag.D4.tag).wordProd longWord :=
    inv_eq_of_mul_eq_one_right wordProd_longWord_sq_l7y
  funext i
  simp only [weylTuple, hinv, Pi.inv_apply]
  rw [wordProd_longWord_neg_l7y]
  rw [show -(Pi.single i (1 : ℤ) : Fin TwistTag.D4.tag.rank → ℤ) =
      (-1 : ℤ) • Pi.single i 1 by rw [neg_one_smul]]
  rw [rootChar_zsmul, CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single, zpow_neg_one]

private theorem weylTuple_triWord_pow_three_l7y {L : Type} [Field L]
    (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    weylTuple ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 3) b = b⁻¹ := by
  rw [wordProd_triWord_pow_three_l7y, weylTuple_longWord_l7y]

private theorem canonicalRep_longWord_l7y {L : Type} [Field L] :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd longWord) = cElt L ^ 3 := by
  have hL : (coxeterSystem TwistTag.D4.tag).IsReduced longWord :=
    isReduced_of_reducedCheck (by decide +kernel)
  have hT : (coxeterSystem TwistTag.D4.tag).IsReduced triWord :=
    isReduced_of_reducedCheck (by decide +kernel)
  rw [canonicalRep_wordProd hL, longWord, List.map_append, List.map_append, List.prod_append,
    List.prod_append, ← canonicalRep_wordProd hT, cElt]
  simp [pow_succ]

private theorem units_map_entrywiseHom_weylElt_one_l7y {L : Type} [Field L]
    (σ : L →+* L) (i : Fin TwistTag.D4.tag.rank) :
    Units.map (entrywiseHom σ) (weylElt TwistTag.D4.tag L i 1) =
      weylElt TwistTag.D4.tag L i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_xUnit,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [map_one, map_neg]

private theorem units_map_entrywiseHom_canonicalRep_l7y {L : Type} [Field L]
    (σ : L →+* L) (w : WeylGroup TwistTag.D4.tag) :
    Units.map (entrywiseHom σ) (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem TwistTag.D4.tag).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod
    (List.map_congr_left fun i _ => units_map_entrywiseHom_weylElt_one_l7y σ i)

private theorem twistHom_canonicalRep_triWord_l7y {L : Type} [Field L]
    (Fr : L →+* L) :
    twistHom TwistTag.D4 L Fr
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd triWord)) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd triWord) := by
  rw [twistHom_apply, units_map_entrywiseHom_canonicalRep_l7y]
  have hcomm : Commute (diagramMap TwistTag.D4 L)
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd triWord)) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.diagramMap_comm_canonicalRep
      (L := L) triWord_mem_relWeylTwist_l7y
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem twistHom_yElt_l7y {L : Type} [Field L]
    (Fr : L →+* L) :
    twistHom TwistTag.D4 L Fr (yElt L) = yElt L := by
  change twistHom TwistTag.D4 L Fr (cElt L ^ 4) = cElt L ^ 4
  rw [map_pow, show cElt L =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd triWord) from rfl,
    twistHom_canonicalRep_triWord_l7y]

theorem twActsAs_yElt {L : Type} [Field L] :
    TwActsAs (yElt L) ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4) := by
  have h : TwActsAs (cElt L) ((coxeterSystem TwistTag.D4.tag).wordProd triWord) :=
    twActsAs_canonicalRep _
  change TwActsAs (cElt L ^ 4) ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)
  simpa [pow_succ] using ((h.mul h).mul h).mul h

private theorem twActsAs_cube_l7y {L : Type} [Field L] :
    TwActsAs (cElt L ^ 3) ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 3) := by
  have h : TwActsAs (cElt L) ((coxeterSystem TwistTag.D4.tag).wordProd triWord) :=
    twActsAs_canonicalRep _
  simpa [pow_succ] using (h.mul h).mul h

private theorem twActsAs_six_l7y {L : Type} [Field L] :
    TwActsAs (cElt L ^ 6) 1 := by
  have h := twActsAs_cube_l7y (L := L)
  have h2 : TwActsAs (cElt L ^ 6) ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 6) := by
    convert h.mul h using 2 <;> rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add]
  rwa [wordProd_triWord_pow_six_l7y] at h2

private theorem cElt_six_conj_rootDiagUnit_l7y {L : Type} [Field L]
    (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    cElt L ^ 6 * rootDiagUnit TwistTag.D4.tag b * (cElt L ^ 6)⁻¹ =
      rootDiagUnit TwistTag.D4.tag b := by
  have h := twActsAs_six_l7y (L := L) b
  simpa [weylTuple_one] using h

private theorem cElt_six_mem_torus_l7y {L : Type} [Field L]
    [Infinite L] :
    cElt L ^ 6 ∈ torusGroup TwistTag.D4.tag L := by
  refine CFSG.HardMathSupport.Timmesfeld.Torality.mem_torusGroup_of_forall_commute_rootDiagUnit
    ?_ ?_
  · exact pow_mem (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd triWord)) 6
  · intro b
    have h := cElt_six_conj_rootDiagUnit_l7y (L := L) b
    show cElt L ^ 6 * rootDiagUnit TwistTag.D4.tag b =
      rootDiagUnit TwistTag.D4.tag b * cElt L ^ 6
    calc cElt L ^ 6 * rootDiagUnit TwistTag.D4.tag b =
        (cElt L ^ 6 * rootDiagUnit TwistTag.D4.tag b * (cElt L ^ 6)⁻¹) * cElt L ^ 6 := by
          group
      _ = rootDiagUnit TwistTag.D4.tag b * cElt L ^ 6 := by rw [h]

private theorem exists_rootDiagUnit_cElt_six_l7y {L : Type} [Field L]
    [Infinite L] :
    ∃ b : Fin TwistTag.D4.tag.rank → Lˣ,
      cElt L ^ 6 = rootDiagUnit TwistTag.D4.tag b :=
  exists_rootDiagUnit_eq_of_mem_torusGroup (cElt_six_mem_torus_l7y (L := L))

private theorem cElt_twelve_l7y {L : Type} [Field L]
    [Infinite L] :
    cElt L ^ 12 = 1 := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_cElt_six_l7y (L := L)
  have h3 := twActsAs_cube_l7y (L := L) b
  rw [weylTuple_triWord_pow_three_l7y] at h3
  have h6 : cElt L ^ 6 = (cElt L ^ 6)⁻¹ := by
    rw [← rootDiagUnit_inv b, ← hb] at h3
    have hleft : cElt L ^ 3 * cElt L ^ 6 * (cElt L ^ 3)⁻¹ = cElt L ^ 6 := by group
    rwa [hleft] at h3
  have hsq : cElt L ^ 6 * cElt L ^ 6 = 1 := by
    nth_rewrite 1 [h6]
    exact inv_mul_cancel _
  rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul, pow_two, hsq]

private theorem yElt_pow_three_l7y {L : Type} [Field L]
    [Infinite L] :
    yElt L ^ 3 = 1 := by
  change (cElt L ^ 4) ^ 3 = 1
  rw [show (cElt L ^ 4) ^ 3 = cElt L ^ 12 by rw [← pow_mul]]
  exact cElt_twelve_l7y

private theorem exists_primitiveRoot_three_l7y {L : Type} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0) :
    ∃ ζ : L, IsPrimitiveRoot ζ 3 :=
  @HasEnoughRootsOfUnity.exists_primitiveRoot L _ 3
    (@IsSepClosed.hasEnoughRootsOfUnity L _ 3 ⟨h3⟩ (inferInstance : IsSepClosed L))

private theorem wordMat_triWord_sq_l7y :
    CFSG.RankThree.Lattice.wordMat TwistTag.D4.tag (triWord ++ triWord) =
      CFSG.RankThree.Lattice.toMat TwistTag.D4.tag.rank
        [[0, -1, 1, -1], [-1, 0, 1, -1], [-1, -1, 1, -1], [-1, -1, 1, 0]] :=
  CFSG.RankThree.Lattice.wordMat_eq_toMat _ _ (by decide +kernel)

private theorem wordProd_triWord_sq_smul_zero_l7y :
    (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 2 •
      (Pi.single (0 : Fin TwistTag.D4.tag.rank) 1 : Fin TwistTag.D4.tag.rank → ℤ) =
      -(Pi.single (1 : Fin TwistTag.D4.tag.rank) (1 : ℤ) +
        Pi.single (2 : Fin TwistTag.D4.tag.rank) (1 : ℤ) +
        Pi.single (3 : Fin TwistTag.D4.tag.rank) (1 : ℤ)) := by
  rw [show (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 2 =
      (coxeterSystem TwistTag.D4.tag).wordProd (triWord ++ triWord) by
    rw [CoxeterSystem.wordProd_append, pow_two]]
  rw [CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec, wordMat_triWord_sq_l7y]
  ext j
  fin_cases j <;> decide +kernel

private theorem weylTuple_r4_zero_l7y {L : Type} [Field L]
    (z : Lˣ) :
    weylTuple ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)
      (Pi.mulSingle (2 : Fin TwistTag.D4.tag.rank) z) 0 = z⁻¹ := by
  have hinv : ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)⁻¹ =
      (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, wordProd_triWord_pow_six_l7y]
  rw [weylTuple, hinv, wordProd_triWord_sq_smul_zero_l7y]
  have hneg : -((Pi.single (1 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
        Fin TwistTag.D4.tag.rank → ℤ) +
        (Pi.single (2 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
          Fin TwistTag.D4.tag.rank → ℤ) +
        (Pi.single (3 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
          Fin TwistTag.D4.tag.rank → ℤ)) =
      (-1 : ℤ) • ((Pi.single (1 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
        Fin TwistTag.D4.tag.rank → ℤ) +
        (Pi.single (2 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
          Fin TwistTag.D4.tag.rank → ℤ) +
        (Pi.single (3 : Fin TwistTag.D4.tag.rank) (1 : ℤ) :
          Fin TwistTag.D4.tag.rank → ℤ)) := by rw [neg_one_smul]
  rw [hneg]
  rw [rootChar_zsmul, rootChar_add,
    rootChar_add,
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single,
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single,
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single]
  simp [Pi.mulSingle]

theorem yElt_mem_monomialSubgroup {L : Type} [Field L] :
    yElt L ∈ monomialSubgroup TwistTag.D4.tag L := by
  rw [yElt, cElt]
  exact pow_mem
    (CFSG.HardMathSupport.Timmesfeld.Torality.canonicalRep_mem_monomialSubgroup'
      ((coxeterSystem TwistTag.D4.tag).wordProd triWord)) 4

theorem diagramMap_comm_yElt {L : Type} [Field L] :
    diagramMap TwistTag.D4 L * yElt L = yElt L * diagramMap TwistTag.D4 L := by
  have h : Commute (diagramMap TwistTag.D4 L)
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd triWord)) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.diagramMap_comm_canonicalRep
      (L := L) triWord_mem_relWeylTwist_l7y
  change diagramMap TwistTag.D4 L * (cElt L ^ 4) = (cElt L ^ 4) * diagramMap TwistTag.D4 L
  exact h.pow_right 4

theorem yElt_fixed {L : Type} [Field L] (Fr : L →+* L)
    (eps : ℤ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps) *
        twistHom TwistTag.D4 L Fr (yElt L) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))⁻¹ = yElt L := by
  rw [twistHom_yElt_l7y]
  by_cases h : eps = 1
  · rw [show twEps eps = 1 by simp [twEps, h], canonicalRep_one, one_mul, inv_one, mul_one]
  · rw [show twEps eps = (coxeterSystem TwistTag.D4.tag).wordProd longWord by simp [twEps, h],
      canonicalRep_longWord_l7y, yElt]
    group

theorem orderOf_yElt {L : Type} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0) :
    orderOf (yElt L) = 3 := by
  have hy3 : yElt L ^ 3 = 1 :=
    @yElt_pow_three_l7y L _ IsAlgClosed.instInfinite
  refine orderOf_eq_prime hy3 ?_
  intro hy1
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_three_l7y (L := L) h3
  let z : Lˣ := Units.mk0 ζ (hζ.ne_zero (by norm_num))
  have hz1 : z ≠ 1 := by
    intro h
    exact hζ.ne_one (by norm_num) (congrArg Units.val h)
  have hact := (twActsAs_yElt (L := L)) (Pi.mulSingle (2 : Fin TwistTag.D4.tag.rank) z)
  rw [hy1, one_mul, inv_one, mul_one] at hact
  have hwt : weylTuple ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)
      (Pi.mulSingle (2 : Fin TwistTag.D4.tag.rank) z) =
      Pi.mulSingle (2 : Fin TwistTag.D4.tag.rank) z :=
    (rootDiagUnit_injective hact).symm
  have h0 := congrFun hwt (0 : Fin TwistTag.D4.tag.rank)
  rw [weylTuple_r4_zero_l7y (L := L) z] at h0
  have hz : z⁻¹ = 1 := by simpa [Pi.mulSingle] using h0
  exact hz1 (inv_eq_one.mp hz)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
