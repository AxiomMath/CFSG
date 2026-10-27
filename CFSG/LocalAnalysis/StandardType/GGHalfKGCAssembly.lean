module

public import CFSG.LocalAnalysis.StandardType.GGHalfNbrCentDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCReduce
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCFive
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCAMain
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCOm8
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCE6
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanO10CentOut
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoTransAux
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoLevi
public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.OmegaMinusCentModel
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

private theorem ggKGCCentSolv_of_mulEquiv {P P' : Type} [Group P] [Group P'] (e : P ≃* P')
    (n : ℕ) (h : GGKGCCentSolv P n) : GGKGCCentSolv P' n := by
  intro J' k' hJ' hk'3 hk'1 hk'J'
  let J : Subgroup P := J'.comap e.toMonoidHom
  let k : P := e.symm k'
  let eJ : ↥J ≃* ↥J' :=
    { toFun := fun x => ⟨e x.1, x.2⟩
      invFun := fun y => ⟨e.symm y.1, Subgroup.mem_comap.mpr (by simpa using y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hJ : Nonempty (↥J ≃* SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) := by
    obtain ⟨eJ'⟩ := hJ'
    exact ⟨eJ.trans eJ'⟩
  have hk3 : k ^ 3 = 1 := by
    show (e.symm k') ^ 3 = 1
    rw [← map_pow, hk'3, map_one]
  have hk1 : k ≠ 1 := by
    intro hk
    apply hk'1
    have hcongr := congrArg e hk
    simpa [k] using hcongr
  have hkJ : k ∈ Subgroup.centralizer (J : Set P) := by
    rw [Subgroup.mem_centralizer_iff] at hk'J' ⊢
    intro j hj
    have h2 := hk'J' (e j) hj
    apply e.injective
    simpa [k, map_mul, MulEquiv.apply_symm_apply] using h2
  have hsolvP : Group.IsSolvable ↥(Subgroup.centralizer (J : Set P)) :=
    h J k hJ hk3 hk1 hkJ
  have hJmap : e.toMonoidHom '' (J : Set P) = (J' : Set P') := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hy
      exact ⟨e.symm y, by
        show e.toMonoidHom (e.symm y) ∈ J'
        simpa using hy, by simp⟩
  have hcent : (Subgroup.centralizer (J : Set P)).map e.toMonoidHom =
      Subgroup.centralizer (J' : Set P') := by
    apply le_antisymm
    · rintro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_iff] at hz ⊢
      intro y' hy'
      rw [← hJmap] at hy'
      obtain ⟨j, hj, rfl⟩ := hy'
      rw [← map_mul, ← map_mul, hz j hj]
    · rintro y hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro j hj
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (e j) (hJmap ▸ ⟨j, hj, rfl⟩)
  let eC : ↥(Subgroup.centralizer (J : Set P)) ≃*
      ↥(Subgroup.centralizer (J' : Set P')) :=
    (Subgroup.equivMapOfInjective (Subgroup.centralizer (J : Set P)) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hcent)
  exact Group.isSolvable_of_surjective (f := eC.toMonoidHom) eC.surjective

private theorem ggHalfKGCAssembly_scalars_two (n : ℕ) :
    LinearFlag.scalars n (GaloisField 2 1) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  rw [LinearFlag.mem_scalars] at hA
  obtain ⟨c, _hc, hAeq⟩ := hA
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by norm_num)
  have hunits : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, hK]
  haveI : Subsingleton (GaloisField 2 1)ˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  have hc1 : c = 1 := Subsingleton.elim c 1
  subst c
  exact Subtype.ext (by simpa using hAeq)

private theorem ggHalfKGCAssembly_A_model {Q : Type} [Group Q] (n : ℕ) (hn : 5 ≤ n)
    (h : GGHasLabel ⟨.A, n, 1⟩ Q) :
    CFSG.Open.StatedClassicalModel Q .PSL (n + 1) 2 1 := by
  unfold GGHasLabel at h
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, hF, hFin, hK, hne⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨e⟩ := hne
  have hadm : CFSG.Open.StatedLieAdmissible .PSL (n + 1) 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
  have hSM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenSLGroup (Fin (n + 1)) K)) .PSL (n + 1) 2 1 :=
    statedClassicalModel_linear (n + 1) 1 hK hadm
  exact statedClassicalModel_of_mulEquiv' e.symm hSM

private theorem ggHalfKGCAssembly_twD_model {Q : Type} [Group Q]
    (h : GGHasLabel ⟨.twD, 4, 1⟩ Q) :
    CFSG.Open.StatedClassicalModel Q .POmegaMinus 4 2 1 := by
  obtain ⟨K, hF, hFin, hK, b, c, hbc, hne⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨e⟩ := hne
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaMinus 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, le_rfl⟩
  have hSM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (4 - 1) b c))) .POmegaMinus 4 2 1 :=
    statedClassicalModel_omegaMinus 4 1 hK b c hbc hadm
  refine ⟨hadm, K, hF, hFin, hK, b, c, hbc, ?_⟩
  exact ⟨e.trans (omegaMinusProjEquiv 4 b c)⟩

private theorem ggHalfKGCAssembly_E6_model {Q : Type} [Group Q]
    (h : GGHasLabel ⟨.E6, 0, 1⟩ Q) :
    CFSG.Blueprint.LieModel Q .E6 0 2 1 := by
  obtain ⟨K, _hF, _hfin, hK, ⟨e⟩⟩ := h
  refine CFSG.Blueprint.LieModel.of_mulEquiv e.symm ?_
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩,
    untwistedChevalleyModel_largeEven .E6 hK⟩)

private theorem ggHalfKGCAssembly_A {Q : Type} [Group Q] (n : ℕ) (hn : 5 ≤ n)
    (hlab : GGHasLabel ⟨.A, n, 1⟩ Q) :
    Nat.card (Outer Q) ≤ 2 ∧
      Nat.card (SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) < Nat.card Q ∧
      GGKGCCentSolv Q n := by
  have hmodel : CFSG.Open.StatedClassicalModel Q .PSL (n + 1) 2 1 :=
    ggHalfKGCAssembly_A_model n hn hlab
  obtain ⟨e1⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hmodel
  have hscal : LinearFlag.scalars (n + 1) (GaloisField 2 1) = ⊥ :=
    ggHalfKGCAssembly_scalars_two (n + 1)
  let eSL : Q ≃* SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1) :=
    (e1.trans
        (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL (n + 1) (GaloisField 2 1))).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.le_of_dvd (by norm_num)
      (CFSG.ComponentClassification.Foote5.card_outer_dvd_two_of_psl_field_two (S := Q)
        (n := n + 1) (by omega) hmodel)
  · rw [Nat.card_congr eSL.toEquiv]
    have hle : Nat.card (SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) ≤
        Nat.card (GeneralLinearGroup (Fin (n - 1)) (GaloisField 2 1)) :=
      Nat.card_le_card_of_injective
        (Matrix.SpecialLinearGroup.toGL :
          SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1) →*
            GeneralLinearGroup (Fin (n - 1)) (GaloisField 2 1))
        Matrix.SpecialLinearGroup.toGL_injective
    have hlt : Nat.card (GeneralLinearGroup (Fin (n - 1)) (GaloisField 2 1)) <
        Nat.card (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 1)) := by
      have h := ggKGCANum_card_aut_lt (W := Fin (n - 1) → GGKGCF) (m := n + 1)
        (by omega) (by rw [Module.finrank_fin_fun]; omega)
      rwa [ggKGCANum_card_aut, Module.finrank_fin_fun] at h
    exact lt_of_le_of_lt hle hlt
  · rcases eq_or_lt_of_le hn with hn5 | hn6
    · obtain rfl : n = 5 := hn5.symm
      exact ggKGCCentSolv_of_mulEquiv eSL.symm 5 ggKGCCentSolv_A_five
    · exact ggKGCCentSolv_of_mulEquiv eSL.symm n (ggKGCCentSolv_A_ge_six (by omega))

private theorem ggHalfKGCAssembly_Om8 {Q : Type} [Group Q]
    (hlab : GGHasLabel ⟨.twD, 4, 1⟩ Q) :
    Nat.card (Outer Q) ≤ 2 ∧
      Nat.card (SpecialLinearGroup (Fin 4) (GaloisField 2 1)) < Nat.card Q ∧
      GGKGCCentSolv Q 5 := by
  have hmodel : CFSG.Open.StatedClassicalModel Q .POmegaMinus 4 2 1 :=
    ggHalfKGCAssembly_twD_model hlab
  obtain ⟨e⟩ := CFSG.HardMathSupport.Foote.E27.nonempty_mulEquiv_omegaMinus hmodel
  have hbc : ∀ s : GaloisField 2 1, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    rcases CFSG.RankThree.PartTwo.Sec4.RonanK429F.gf2_eq_zero_or_one s with rfl | rfl
    · simp
    · rw [one_pow, one_mul, CFSG.RankThree.PartTwo.Sec4.RonanK429F.gf2_one_add_one, zero_add]
      exact one_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.le_of_dvd (by norm_num)
      (CFSG.AGLEmbedding.O10Cent.card_outer_dvd_two (L := Q) (n := 4) (by norm_num) hmodel)
  · have hSL : Nat.card (SpecialLinearGroup (Fin 4) (GaloisField 2 1)) = 20160 := by
      rw [CFSG.OrderReductions.LinearOrders.card_specialLinear (GaloisField 2 1) 4 (by norm_num)]
      have hK2 : Nat.card (GaloisField 2 1) = 2 := by
        simpa using GaloisField.card 2 1 (by norm_num)
      rw [hK2]
      decide +kernel
    have hcard : Nat.card Q = 197406720 := by
      rw [Nat.card_congr e.toEquiv]
      simpa using
        CFSG.RankThree.PartTwo.Sec4.RonanK429F.Om8.card_Om8 (b := 1) (c := 1) hbc
    rw [hSL, hcard]
    norm_num
  · exact ggKGCCentSolv_of_mulEquiv e.symm 5 ggKGCCentSolv_Om8

private theorem ggHalfKGCAssembly_E6
    {E : Type} [Group E] [Finite E]
    (hperf : commutator E = ⊤)
    (hlab : GGHasLabel ⟨.E6, 0, 1⟩ (E ⧸ Subgroup.center E)) :
    Nat.card (Outer (E ⧸ Subgroup.center E)) ≤ 2 ∧
      Nat.card (SpecialLinearGroup (Fin 6) (GaloisField 2 1)) <
        Nat.card (E ⧸ Subgroup.center E) ∧
      GGKGCCentSolv (E ⧸ Subgroup.center E) 7 := by
  have hLie : CFSG.Blueprint.LieModel (E ⧸ Subgroup.center E) .E6 0 2 1 :=
    ggHalfKGCAssembly_E6_model hlab
  have hZ : Subgroup.center E = ⊥ := ggSixE6A24_center_eq_bot E hperf hLie
  obtain ⟨e0⟩ := GGSixE6Two.nonempty_mulEquiv_EC hperf hLie
  let eX : (E ⧸ Subgroup.center E) ≃* GGSixE6Two.EC :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e0
  refine ⟨?_, ?_, ?_⟩
  · exact (CFSG.SeitzReduction.SeitzQ2.card_outer_le_two_of_mulEquiv_E6_two
      (K := GaloisField 2 1) (by simpa using GaloisField.card 2 1 (by norm_num)) eX).2
  · have hSL : Nat.card (SpecialLinearGroup (Fin 6) (GaloisField 2 1)) = 20158709760 := by
      rw [CFSG.OrderReductions.LinearOrders.card_specialLinear (GaloisField 2 1) 6 (by norm_num)]
      have hK2 : Nat.card (GaloisField 2 1) = 2 := by
        simpa using GaloisField.card 2 1 (by norm_num)
      rw [hK2]
      decide +kernel
    have hcard : Nat.card (E ⧸ Subgroup.center E) = CFSG.Open.ordE6 2 := by
      rw [Nat.card_congr eX.toEquiv, GGSixE6Two.card_EC]
    rw [hSL, hcard]
    decide +kernel
  · exact ggKGCCentSolv_of_mulEquiv eX.symm 7 ggKGCCentSolv_E6

theorem ggHalfNbrCentInput_holds :
    GGHalfNbrCentInput := by
  intro Y _ _ X J R x n lab hn hX hlabel hcases hx hx3 hJ hJc hR hRJ hRp
  rcases hcases with hA | ⟨hn5, htwD⟩ | ⟨hn7, hE6⟩
  · obtain rfl := hA
    obtain ⟨hOut, hlt, hcs⟩ := ggHalfKGCAssembly_A n hn hlabel
    exact ggHalfNbrCent_of_centSolv X J R x n hX hOut hlt hcs hx hx3 hJ hJc hR hRJ hRp
  · obtain rfl : n = 5 := hn5
    obtain rfl := htwD
    obtain ⟨hOut, hlt, hcs⟩ := ggHalfKGCAssembly_Om8 hlabel
    exact ggHalfNbrCent_of_centSolv X J R x 5 hX hOut hlt hcs hx hx3 hJ hJc hR hRJ hRp
  · obtain rfl : n = 7 := hn7
    obtain rfl := hE6
    obtain ⟨hOut, hlt, hcs⟩ := ggHalfKGCAssembly_E6 hX.1 hlabel
    exact ggHalfNbrCent_of_centSolv X J R x 7 hX hOut hlt hcs hx hx3 hJ hJc hR hRJ hRp

end CFSG.StandardType

end
