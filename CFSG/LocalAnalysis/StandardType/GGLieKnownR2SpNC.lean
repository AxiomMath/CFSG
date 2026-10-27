module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Filtration
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpNorm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpRad
public import CFSG.RankThree.GF2n.Tim79aClassicalSp
public import CFSG.CGT.T75E.Lemma26
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups.Linear.TwoCentres
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.GF2n.Tim79aCase1End
public import CFSG.RankThree.GF2n.Tim79aCentreClause
public import CFSG.RankThree.GF2n.Tim79aIdentU3
public import CFSG.RankThree.GF2n.Tim79aSec2
public import CFSG.RankThree.GF2n.Tim79aWCQInputs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.StandardType.LieKnownR2.PSp

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial TauCeti.GLSymplecticFin
open CFSG.StandardType.LieKnownR2.Short
open scoped Matrix

private theorem l10ss2_allEven_positiveLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.positiveLong i)) := by
  intro a
  simp only [stdVec, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem l10ss2_allEven_negativeLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.negativeLong i)) := by
  intro a
  simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem l10ss2_allEven_of_ggLongRoot {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    GGRootSp.AllEven (toStd n β) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  refine (GGRootSp.allEven_toStd_weylAction_iff w γ₀).2 ?_
  obtain ⟨r₀, hr₀⟩ := exists_stdVec_of_mem_roots hγ₀
  change GGRootSp.AllEven (toStd n γ₀)
  rw [← hr₀]
  have hn0 : 0 < n := by
    rcases r₀ with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hle : ht (ι := Fin n) θ ≤ ht (ι := Fin n) γ₀ := hmax θ hθ
  have hγ2 := two_mul_ht (n := n) γ₀
  rw [← hr₀] at hγ2
  have h4 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by omega
  by_cases hn2 : 2 ≤ n
  · rw [GGRootSp.stdVec_eq_of_lv_lt hn2 r₀ h4]
    exact l10ss2_allEven_positiveLong _
  · rcases r₀ with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
    · exact l10ss2_allEven_positiveLong i
    · exact l10ss2_allEven_negativeLong i
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    all_goals
      exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)

private theorem l10ss2_longIndex {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    ∃ i : Fin n, stdVec (.positiveLong i) = toStd n β ∨
      stdVec (.negativeLong i) = toStd n β := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  have hev := l10ss2_allEven_of_ggLongRoot hl
  change GGRootSp.AllEven (toStd n β) at hev
  rw [← hr] at hev
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact ⟨i, Or.inl hr⟩
  · exact ⟨i, Or.inr hr⟩
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij] at h
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij.ne] at h
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij.ne] at h

private theorem l10ss2_spForm_single_single {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (b c : Fin n ⊕ Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single b (1 : F)) (Pi.single c (1 : F)) =
      if c = b.swap then 1 else 0 := by
  rw [CFSG.Timmesfeld.ARS.CaseM.spForm, Matrix.mulVec_single_one, dotProduct,
    Finset.sum_eq_single b]
  · rcases b with i | i <;> rcases c with j | j <;>
      simp [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks, Matrix.one_apply, eq_comm,
        CharTwo.neg_eq]
  · intro a _ ha
    rw [Pi.single_eq_of_ne ha, zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

private theorem l10ss2_isTransGroup_pos {n : ℕ} {F : Type} [Field F] {i : Fin n}
    {γ : Fin n → ℤ} (hγ : Symplectic.toStd n γ = 2 • Pi.single i 1) :
    CFSG.Timmesfeld.ARS.CaseM.IsTransGroup (Pi.single (Sum.inl i) 1)
      ((Symplectic.rootDatum n F).rootGroup γ) :=
  ⟨fun x => CFSG.Timmesfeld.ARS.CaseM.mem_rootGroup_pos_iff hγ x,
    fun c => CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans _ c⟩

private theorem l10ss2_isTransGroup_neg {n : ℕ} {F : Type} [Field F] {i : Fin n}
    {γ : Fin n → ℤ} (hγ : Symplectic.toStd n γ = -(2 • Pi.single i 1)) :
    CFSG.Timmesfeld.ARS.CaseM.IsTransGroup (Pi.single (Sum.inr i) 1)
      ((Symplectic.rootDatum n F).rootGroup γ) :=
  ⟨fun x => CFSG.Timmesfeld.ARS.CaseM.mem_rootGroup_neg_iff hγ x,
    fun c => CFSG.Timmesfeld.Transvection.ModelRank.exists_mat_eq_spTrans _ c⟩

private def l10ss2_sel {n : ℕ} {F : Type} [Field F] (i j : Fin n) : Fin n ⊕ Fin n → F :=
  if j = i then Pi.single (Sum.inl j) 1 else Pi.single (Sum.inr j) 1

private def l10ss2_sel' {n : ℕ} {F : Type} [Field F] (i j : Fin n) : Fin n ⊕ Fin n → F :=
  if j = i then Pi.single (Sum.inr j) 1
  else Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1

private theorem l10ss2_spForm_inl_inl {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F))
      (Pi.single (Sum.inl j) (1 : F)) = 0 := by
  rw [l10ss2_spForm_single_single]
  simp [Sum.swap_inl]

private theorem l10ss2_spForm_inr_inr {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F))
      (Pi.single (Sum.inr j) (1 : F)) = 0 := by
  rw [l10ss2_spForm_single_single]
  simp [Sum.swap_inr]

private theorem l10ss2_spForm_inl_inr {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F))
      (Pi.single (Sum.inr j) (1 : F)) =
      if i = j then 1 else 0 := by
  rw [l10ss2_spForm_single_single]
  simp [Sum.swap_inl, Sum.inr.injEq, eq_comm]

private theorem l10ss2_spForm_inr_inl {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F))
      (Pi.single (Sum.inl j) (1 : F)) =
      if i = j then 1 else 0 := by
  rw [l10ss2_spForm_single_single]
  simp [Sum.swap_inr, Sum.inl.injEq, eq_comm]

private theorem l10ss2_sel_sel {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j k : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (l10ss2_sel (F := F) i j) (l10ss2_sel (F := F) i k) = 0 := by
  unfold l10ss2_sel
  by_cases hj : j = i
  · rw [if_pos hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      exact l10ss2_spForm_inl_inl j k
    · rw [if_neg hk]
      have hik : ¬ i = k := fun h => hk h.symm
      simp only [l10ss2_spForm_inl_inr, hj, hik, if_false, sub_self, ZeroHomClass.map_zero]
  · rw [if_neg hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      have hjk : ¬ j = k := fun h => hj (h.trans hk)
      simp only [l10ss2_spForm_inr_inl, hjk, if_false]
    · rw [if_neg hk]
      exact l10ss2_spForm_inr_inr j k

private theorem l10ss2_sel'_sel' {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j k : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (l10ss2_sel' (F := F) i j) (l10ss2_sel' (F := F) i k) =
      0 := by
  unfold l10ss2_sel'
  by_cases hj : j = i
  · rw [if_pos hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      exact l10ss2_spForm_inr_inr j k
    · rw [if_neg hk]
      have hik : ¬ i = k := fun h => hk h.symm
      simp only [l10ss2_spForm_inr_inl, l10ss2_spForm_inr_inr,
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
        CFSG.Timmesfeld.ARS.CaseM.spForm_self, hj, hik, if_false, add_zero]
  · rw [if_neg hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      have hjk : ¬ j = k := fun h => hj (h.trans hk)
      simp only [l10ss2_spForm_inl_inr, l10ss2_spForm_inr_inr,
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_left,
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
        CFSG.Timmesfeld.ARS.CaseM.spForm_self, hjk, if_false, add_zero, zero_add]
    · rw [if_neg hk]
      simp only [l10ss2_spForm_inl_inl, l10ss2_spForm_inl_inr, l10ss2_spForm_inr_inl,
        l10ss2_spForm_inr_inr, CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_left,
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
        CFSG.Timmesfeld.ARS.CaseM.spForm_self, hj, hk, CharTwo.add_self_eq_zero, add_zero,
        zero_add]

private theorem l10ss2_sel_sel' {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j k : Fin n) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (l10ss2_sel (F := F) i j) (l10ss2_sel' (F := F) i k) =
      if j = k then 1 else 0 := by
  unfold l10ss2_sel l10ss2_sel'
  by_cases hj : j = i
  · rw [if_pos hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      simp only [l10ss2_spForm_inl_inr, hj, hk, if_true]
    · rw [if_neg hk]
      have hik : ¬ i = k := fun h => hk h.symm
      simp only [l10ss2_spForm_inl_inl, l10ss2_spForm_inl_inr,
        CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
        CFSG.Timmesfeld.ARS.CaseM.spForm_self, hj, hik, if_false, add_zero]
  · rw [if_neg hj]
    by_cases hk : k = i
    · rw [if_pos hk]
      have hjk : ¬ j = k := fun h => hj (h.trans hk)
      simp only [l10ss2_spForm_inr_inr, hjk, if_false]
    · rw [if_neg hk]
      by_cases hjk : j = k
      · rw [if_pos hjk]
        simp only [l10ss2_spForm_inr_inl, l10ss2_spForm_inr_inr,
          CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
          CFSG.Timmesfeld.ARS.CaseM.spForm_self, hjk, if_true, add_zero]
      · rw [if_neg hjk]
        simp only [l10ss2_spForm_inr_inl, l10ss2_spForm_inr_inr,
          CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
          CFSG.Timmesfeld.ARS.CaseM.spForm_self, hjk, if_false, add_zero]

private theorem l10ss2_exists_h {n : ℕ} {F : Type} [Field F] [CharP F 2] (i : Fin n) :
    ∃ h : ↥(StatedSp n F), ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j :=
  CFSG.Timmesfeld.ARS.CaseM.exists_mem_statedSp_mulVec
    (fun j k => l10ss2_sel_sel i j k) (fun j k => l10ss2_sel'_sel' i j k)
    (fun j k => l10ss2_sel_sel' i j k)

private theorem l10ss2_h_plane {n : ℕ} {F : Type} [Field F] {i : Fin n} {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j) :
    (SpExtras.mat n F h *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1) ∧
      (SpExtras.mat n F h *ᵥ Pi.single (Sum.inr i) 1 = Pi.single (Sum.inr i) 1) := by
  refine ⟨?_, ?_⟩
  · rw [(hh i).1]
    unfold l10ss2_sel
    rw [if_pos rfl]
  · rw [(hh i).2]
    unfold l10ss2_sel'
    rw [if_pos rfl]

private theorem l10ss2_h_off {n : ℕ} {F : Type} [Field F] {i : Fin n} {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    {j : Fin n} (hj : j ≠ i) :
    SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inr j) 1 ∧
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 =
        Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1 := by
  refine ⟨?_, ?_⟩
  · rw [(hh j).1]
    unfold l10ss2_sel
    rw [if_neg hj]
  · rw [(hh j).2]
    unfold l10ss2_sel'
    rw [if_neg hj]

private theorem l10ss2_h_ne_one {n : ℕ} {F : Type} [Field F] {i : Fin n}
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (hn : 2 ≤ n) : h ≠ 1 := by
  obtain ⟨j, hj⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := Fin n) (by rw [Fintype.card_fin]; omega) i
  have h1 := (l10ss2_h_off (i := i) hh hj).1
  intro hh1
  rw [hh1, map_one, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 (Sum.inr j)
  simp at h2

private theorem l10ss2_h_order {n : ℕ} {F : Type} [Field F] [CharP F 2] {i : Fin n}
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (hn : 2 ≤ n) : orderOf h = 3 := by
  have hcube : h ^ 3 = 1 := by
    apply SpExtras.mat_injective
    apply Matrix.ext
    intro r c
    have key : SpExtras.mat n F (h ^ 3) *ᵥ Pi.single c (1 : F) = Pi.single c (1 : F) := by
      rw [map_pow]
      rw [show (SpExtras.mat n F h) ^ 3 =
          SpExtras.mat n F h * SpExtras.mat n F h * SpExtras.mat n F h by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
          show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one]]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rcases c with j | j
      · rcases eq_or_ne j i with hji | hj
        · rw [hji]
          simp only [(l10ss2_h_plane (i := i) hh).1]
        · have hE := (l10ss2_h_off (i := i) hh hj).1
          have hF := (l10ss2_h_off (i := i) hh hj).2
          simp only [hE, hF, Matrix.mulVec_add]
          have hff : (Pi.single (Sum.inr j) (1 : F) : Fin n ⊕ Fin n → F) +
              (Pi.single (Sum.inr j) (1 : F) : Fin n ⊕ Fin n → F) = 0 := by
            ext x; simp [CharTwo.add_self_eq_zero]
          linear_combination (norm := abel) hff
      · rcases eq_or_ne j i with hji | hj
        · rw [hji]
          simp only [(l10ss2_h_plane (i := i) hh).2]
        · have hE := (l10ss2_h_off (i := i) hh hj).1
          have hF := (l10ss2_h_off (i := i) hh hj).2
          simp only [hE, hF, Matrix.mulVec_add]
          have hff : (Pi.single (Sum.inr j) (1 : F) : Fin n ⊕ Fin n → F) +
              (Pi.single (Sum.inr j) (1 : F) : Fin n ⊕ Fin n → F) = 0 := by
            ext x; simp [CharTwo.add_self_eq_zero]
          have hee : (Pi.single (Sum.inl j) (1 : F) : Fin n ⊕ Fin n → F) +
              (Pi.single (Sum.inl j) (1 : F) : Fin n ⊕ Fin n → F) = 0 := by
            ext x; simp [CharTwo.add_self_eq_zero]
          linear_combination (norm := abel) hee + hff
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply, Matrix.one_apply]
      using congrFun key r
  exact orderOf_eq_prime hcube (l10ss2_h_ne_one hh hn)

private theorem l10ss2_mat_apply_eq {n : ℕ} {F : Type} [Field F] {h : ↥(StatedSp n F)}
    {a b : Fin n ⊕ Fin n} {v : Fin n ⊕ Fin n → F}
    (hv : SpExtras.mat n F h *ᵥ Pi.single b (1 : F) = v) :
    SpExtras.mat n F h a b = v a := by
  have h1 := congrFun hv a
  rw [Matrix.mulVec_single_one] at h1
  exact h1

private theorem l10ss2_h_mulVec_inl {n : ℕ} {F : Type} [Field F] {i : Fin n}
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (x : Fin n ⊕ Fin n → F) {j : Fin n} (hj : j ≠ i) :
    (SpExtras.mat n F h *ᵥ x) (Sum.inl j) = x (Sum.inr j) := by
  have hcol : ∀ a : Fin n ⊕ Fin n,
      SpExtras.mat n F h (Sum.inl j) a = (if a = Sum.inr j then (1 : F) else 0) := by
    intro a
    rcases a with k | k
    · rw [l10ss2_mat_apply_eq (hh k).1]
      by_cases hk : k = i
      · subst hk; simp [l10ss2_sel, Pi.single_apply, hj, eq_comm]
      · simp [l10ss2_sel, hk, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, eq_comm]
    · rw [l10ss2_mat_apply_eq (hh k).2]
      by_cases hk : k = i
      · subst hk; simp [l10ss2_sel', Pi.single_apply, hj, eq_comm]
      · by_cases hkj : k = j
        · subst hkj; simp [l10ss2_sel', hk, Pi.single_apply, eq_comm]
        · simp [l10ss2_sel', hk, hkj, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, eq_comm]
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (Sum.inr j)]
  · rw [hcol (Sum.inr j)]; simp
  · intro a _ ha
    rw [hcol a]
    by_cases haj : a = Sum.inr j
    · exact absurd haj ha
    · rw [if_neg haj, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private theorem l10ss2_h_mulVec_inr {n : ℕ} {F : Type} [Field F] {i : Fin n}
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (x : Fin n ⊕ Fin n → F) {j : Fin n} (hj : j ≠ i) :
    (SpExtras.mat n F h *ᵥ x) (Sum.inr j) = x (Sum.inl j) + x (Sum.inr j) := by
  have hcol : ∀ a : Fin n ⊕ Fin n,
      SpExtras.mat n F h (Sum.inr j) a =
        (if a = Sum.inl j then (1 : F) else 0) + (if a = Sum.inr j then (1 : F) else 0) := by
    intro a
    rcases a with k | k
    · rw [l10ss2_mat_apply_eq (hh k).1]
      by_cases hk : k = i
      · subst hk; simp [l10ss2_sel, Pi.single_apply, hj, eq_comm]
      · by_cases hkj : k = j
        · subst hkj; simp [l10ss2_sel, hk, Pi.single_apply, eq_comm]
        · simp [l10ss2_sel, hk, hkj, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, eq_comm]
    · rw [l10ss2_mat_apply_eq (hh k).2]
      by_cases hk : k = i
      · subst hk; simp [l10ss2_sel', Pi.single_apply, hj, eq_comm]
      · by_cases hkj : k = j
        · subst hkj; simp [l10ss2_sel', hk, Pi.single_apply, eq_comm]
        · simp [l10ss2_sel', hk, hkj, Pi.single_apply, Sum.inl_ne_inr, Sum.inr_ne_inl, eq_comm]
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_add (Sum.inl j) (Sum.inr j) (by simp)]
  · rw [hcol (Sum.inl j), hcol (Sum.inr j)]; simp
  · intro a _ ha
    rw [hcol a]
    by_cases ha1 : a = Sum.inl j
    · exact absurd ha1 ha.1
    · by_cases ha2 : a = Sum.inr j
      · exact absurd ha2 ha.2
      · rw [if_neg ha1, if_neg ha2, add_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem l10ss2_h_no_fix_perp {n : ℕ} {F : Type} [Field F] [CharP F 2] {i : Fin n}
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    {x : Fin n ⊕ Fin n → F} (hxi : x (Sum.inl i) = 0) (hxi' : x (Sum.inr i) = 0)
    (hfix : SpExtras.mat n F h *ᵥ x = x) : x = 0 := by
  funext z
  rcases z with k | k
  · by_cases hk : k = i
    · rw [hk]; exact hxi
    · have h1 := l10ss2_h_mulVec_inl hh x hk
      have h2 := l10ss2_h_mulVec_inr hh x hk
      rw [hfix] at h1 h2
      have h5 : x (Sum.inr k) = 0 := by
        rw [h1] at h2
        rwa [CharTwo.add_self_eq_zero] at h2
      simp [h1, h5]
  · by_cases hk : k = i
    · rw [hk]; exact hxi'
    · have h1 := l10ss2_h_mulVec_inl hh x hk
      have h2 := l10ss2_h_mulVec_inr hh x hk
      rw [hfix] at h1 h2
      have h5 : x (Sum.inr k) = 0 := by
        rw [h1] at h2
        rwa [CharTwo.add_self_eq_zero] at h2
      exact h5

private theorem l10ss2_spForm_inl {n : ℕ} {F : Type} [Field F] (i : Fin n)
    (x : Fin n ⊕ Fin n → F) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) x = x (Sum.inr i) := by
  rw [CFSG.Timmesfeld.ARS.CaseM.spForm, single_dotProduct, one_mul, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (Sum.inr i)]
  · simp [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks, Matrix.one_apply]
  · intro a _ ha
    rcases a with k | k
    · simp [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks]
    · have hk : k ≠ i := fun h => ha (by rw [h])
      have hik : i ≠ k := fun h => hk h.symm
      rw [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks_apply₁₂, Matrix.one_apply,
        if_neg hik, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem l10ss2_spForm_inr {n : ℕ} {F : Type} [Field F] [CharP F 2] (i : Fin n)
    (x : Fin n ⊕ Fin n → F) :
    CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) x = x (Sum.inl i) := by
  rw [CFSG.Timmesfeld.ARS.CaseM.spForm, single_dotProduct, one_mul, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (Sum.inl i)]
  · simp [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq]
  · intro a _ ha
    rcases a with k | k
    · have hk : k ≠ i := fun h => ha (by rw [h])
      have hik : i ≠ k := fun h => hk h.symm
      have hz : CFSG.Timmesfeld.ARS.CaseM.spGram n F (Sum.inr i) (Sum.inl k) = 0 := by
        rw [CFSG.Timmesfeld.ARS.CaseM.spGram]
        simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.neg_apply, if_neg hik]
      rw [hz, zero_mul]
    · simp [CFSG.Timmesfeld.ARS.CaseM.spGram, Matrix.fromBlocks]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem l10ss2_long_fix_pos {n : ℕ} {F : Type} [Field F] [CharP F 2] {i : Fin n}
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup (Pi.single (Sum.inl i) (1 : F))
      ((Symplectic.rootDatum n F).rootGroup β))
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (hfixv : SpExtras.mat n F h *ᵥ Pi.single (Sum.inl i) (1 : F) =
      Pi.single (Sum.inl i) (1 : F))
    (hfixw : SpExtras.mat n F h *ᵥ Pi.single (Sum.inr i) (1 : F) =
      Pi.single (Sum.inr i) (1 : F))
    {y : ↥(StatedSp n F)}
    (hy : y ∈ CFSG.Timmesfeld.Transvection.ModelRank.spRad
      (Pi.single (Sum.inl i) (1 : F)))
    (hycomm : h * y = y * h) :
    y ∈ (Symplectic.rootDatum n F).rootGroup β := by
  have hvi : (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F) ≠ 0 := by
    intro h0; have := congrFun h0 (Sum.inl i); simp at this
  have hvw : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F))
      (Pi.single (Sum.inr i) (1 : F)) = 1 := by
    rw [l10ss2_spForm_inl_inr]; simp
  obtain ⟨w', l, hvw', hparam⟩ :=
    CFSG.Timmesfeld.Transvection.ModelRank.exists_param_of_mem_spRad hvi hy
  have hconj : SpExtras.mat n F h * SpExtras.mat n F y =
      SpExtras.mat n F y * SpExtras.mat n F h := by
    rw [← map_mul, ← map_mul, hycomm]
  have h1 : SpExtras.mat n F h *ᵥ (SpExtras.mat n F y *ᵥ Pi.single (Sum.inr i) 1) =
      SpExtras.mat n F y *ᵥ Pi.single (Sum.inr i) 1 := by
    rw [Matrix.mulVec_mulVec, hconj, ← Matrix.mulVec_mulVec, hfixw]
  rw [hparam (Pi.single (Sum.inr i) (1 : F))] at h1
  simp only [hvw, one_smul, mul_one, Matrix.mulVec_add, Matrix.mulVec_smul, hfixv, hfixw] at h1
  have hw'fix : SpExtras.mat n F h *ᵥ w' = w' := by
    linear_combination h1
  set c : F := CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) w' with hc
  set x : Fin n ⊕ Fin n → F := w' + c • Pi.single (Sum.inl i) (1 : F) with hx
  have hxv : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) x = 0 := by
    rw [hx, CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hvw',
      CFSG.Timmesfeld.ARS.CaseM.spForm_self]
    simp
  have hxw : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) x = 0 := by
    rw [hx, CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hc]
    rw [show CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F))
        (Pi.single (Sum.inl i) (1 : F)) = 1 from by rw [l10ss2_spForm_inr_inl]; simp, mul_one]
    rw [CharTwo.add_self_eq_zero]
  have hxc2 : x (Sum.inl i) = 0 := by
    rw [← l10ss2_spForm_inr i x]; exact hxw
  have hxc1 : x (Sum.inr i) = 0 := by
    rw [← l10ss2_spForm_inl i x]; exact hxv
  have hxfix : SpExtras.mat n F h *ᵥ x = x := by
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, hw'fix, hfixv]
  have hx0 : x = 0 := l10ss2_h_no_fix_perp (i := i) hh hxc2 hxc1 hxfix
  have hw'rep : w' = c • Pi.single (Sum.inl i) (1 : F) := by
    have hcc : (c • (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F)) +
        (c • (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F)) = 0 := by
      rw [← add_smul, show c + c = (0 : F) from CharTwo.add_self_eq_zero c, zero_smul]
    rw [hx] at hx0
    calc w' = w' + (c • Pi.single (Sum.inl i) (1 : F) +
          c • Pi.single (Sum.inl i) (1 : F)) := by rw [hcc, add_zero]
      _ = (w' + c • Pi.single (Sum.inl i) (1 : F)) + c • Pi.single (Sum.inl i) (1 : F) := by
          abel
      _ = 0 + c • Pi.single (Sum.inl i) (1 : F) := by rw [hx0]
      _ = c • Pi.single (Sum.inl i) (1 : F) := zero_add _
  have hyT : SpExtras.mat n F y =
      CFSG.Timmesfeld.ARS.CaseM.spTrans (Pi.single (Sum.inl i) (1 : F)) l := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    rw [hparam u, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hw'rep,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul]
    have h2 : (CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) u * c) •
          (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F) +
        (c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) u) •
          (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F) = 0 := by
      rw [mul_comm (CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) u) c,
        ← add_smul, show c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) u +
          c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) u = (0 : F) from
          CharTwo.add_self_eq_zero _, zero_smul]
    linear_combination (norm := abel) h2
  exact (hT.1 y).2 ⟨l, hyT⟩

private theorem l10ss2_long_fix_neg {n : ℕ} {F : Type} [Field F] [CharP F 2] {i : Fin n}
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup (Pi.single (Sum.inr i) (1 : F))
      ((Symplectic.rootDatum n F).rootGroup β))
    {h : ↥(StatedSp n F)}
    (hh : ∀ j : Fin n,
      SpExtras.mat n F h *ᵥ Pi.single (Sum.inl j) 1 = l10ss2_sel (F := F) i j ∧
        SpExtras.mat n F h *ᵥ Pi.single (Sum.inr j) 1 = l10ss2_sel' (F := F) i j)
    (hfixv : SpExtras.mat n F h *ᵥ Pi.single (Sum.inr i) (1 : F) =
      Pi.single (Sum.inr i) (1 : F))
    (hfixw : SpExtras.mat n F h *ᵥ Pi.single (Sum.inl i) (1 : F) =
      Pi.single (Sum.inl i) (1 : F))
    {y : ↥(StatedSp n F)}
    (hy : y ∈ CFSG.Timmesfeld.Transvection.ModelRank.spRad
      (Pi.single (Sum.inr i) (1 : F)))
    (hycomm : h * y = y * h) :
    y ∈ (Symplectic.rootDatum n F).rootGroup β := by
  have hvi : (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F) ≠ 0 := by
    intro h0; have := congrFun h0 (Sum.inr i); simp at this
  have hvw : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F))
      (Pi.single (Sum.inl i) (1 : F)) = 1 := by
    rw [l10ss2_spForm_inr_inl]; simp
  obtain ⟨w', l, hvw', hparam⟩ :=
    CFSG.Timmesfeld.Transvection.ModelRank.exists_param_of_mem_spRad hvi hy
  have hconj : SpExtras.mat n F h * SpExtras.mat n F y =
      SpExtras.mat n F y * SpExtras.mat n F h := by
    rw [← map_mul, ← map_mul, hycomm]
  have h1 : SpExtras.mat n F h *ᵥ (SpExtras.mat n F y *ᵥ Pi.single (Sum.inl i) 1) =
      SpExtras.mat n F y *ᵥ Pi.single (Sum.inl i) 1 := by
    rw [Matrix.mulVec_mulVec, hconj, ← Matrix.mulVec_mulVec, hfixw]
  rw [hparam (Pi.single (Sum.inl i) (1 : F))] at h1
  simp only [hvw, one_smul, mul_one, Matrix.mulVec_add, Matrix.mulVec_smul, hfixv, hfixw] at h1
  have hw'fix : SpExtras.mat n F h *ᵥ w' = w' := by
    linear_combination h1
  set c : F := CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) w' with hc
  set x : Fin n ⊕ Fin n → F := w' + c • Pi.single (Sum.inr i) (1 : F) with hx
  have hxv : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) x = 0 := by
    rw [hx, CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hvw',
      CFSG.Timmesfeld.ARS.CaseM.spForm_self]
    simp
  have hxw : CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F)) x = 0 := by
    rw [hx, CFSG.Timmesfeld.Transvection.ModelRank.spForm_add_right,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_right', hc]
    rw [show CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inl i) (1 : F))
        (Pi.single (Sum.inr i) (1 : F)) = 1 from by rw [l10ss2_spForm_inl_inr]; simp, mul_one]
    rw [CharTwo.add_self_eq_zero]
  have hxc2 : x (Sum.inl i) = 0 := by
    rw [← l10ss2_spForm_inr i x]; exact hxv
  have hxc1 : x (Sum.inr i) = 0 := by
    rw [← l10ss2_spForm_inl i x]; exact hxw
  have hxfix : SpExtras.mat n F h *ᵥ x = x := by
    rw [hx, Matrix.mulVec_add, Matrix.mulVec_smul, hw'fix, hfixv]
  have hx0 : x = 0 := l10ss2_h_no_fix_perp (i := i) hh hxc2 hxc1 hxfix
  have hw'rep : w' = c • Pi.single (Sum.inr i) (1 : F) := by
    have hcc : (c • (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F)) +
        (c • (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F)) = 0 := by
      rw [← add_smul, show c + c = (0 : F) from CharTwo.add_self_eq_zero c, zero_smul]
    rw [hx] at hx0
    calc w' = w' + (c • Pi.single (Sum.inr i) (1 : F) +
          c • Pi.single (Sum.inr i) (1 : F)) := by rw [hcc, add_zero]
      _ = (w' + c • Pi.single (Sum.inr i) (1 : F)) + c • Pi.single (Sum.inr i) (1 : F) := by
          abel
      _ = 0 + c • Pi.single (Sum.inr i) (1 : F) := by rw [hx0]
      _ = c • Pi.single (Sum.inr i) (1 : F) := zero_add _
  have hyT : SpExtras.mat n F y =
      CFSG.Timmesfeld.ARS.CaseM.spTrans (Pi.single (Sum.inr i) (1 : F)) l := by
    refine Matrix.ext_iff_mulVec.2 fun u => ?_
    rw [hparam u, CFSG.Timmesfeld.Transvection.ModelRank.spTrans_mulVec, hw'rep,
      CFSG.Timmesfeld.Transvection.ModelRank.spForm_smul_left', smul_smul]
    have h2 : (CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) u * c) •
          (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F) +
        (c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) u) •
          (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F) = 0 := by
      rw [mul_comm (CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) u) c,
        ← add_smul, show c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) u +
          c * CFSG.Timmesfeld.ARS.CaseM.spForm (Pi.single (Sum.inr i) (1 : F)) u = (0 : F) from
          CharTwo.add_self_eq_zero _, zero_smul]
    linear_combination (norm := abel) h2
  exact (hT.1 y).2 ⟨l, hyT⟩

private theorem l10ss2_fpf_long {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 2 ≤ n) {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) :
    ∃ h ∈ Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) : Set ↥(StatedSp n F)),
      orderOf h = 3 ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F))), h * y = y * h → y ∈ (Symplectic.rootDatum n F).rootGroup β := by
  obtain ⟨i, hpos | hneg⟩ := l10ss2_longIndex hβ hl
  · obtain ⟨h, hh⟩ := l10ss2_exists_h (F := F) i
    have hT := l10ss2_isTransGroup_pos (n := n) (F := F) (γ := β) hpos.symm
    have hfix := l10ss2_h_plane (i := i) hh
    have hvi : (Pi.single (Sum.inl i) (1 : F) : Fin n ⊕ Fin n → F) ≠ 0 := by
      intro h0; have := congrFun h0 (Sum.inl i); simp at this
    have hmem : h ∈ Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F)) := by
      rw [CFSG.Timmesfeld.Transvection.ModelRank.normalizer_eq_spLine hvi hT]
      exact ⟨1, one_ne_zero, by rw [hfix.1, one_smul]⟩
    refine ⟨h, hmem, l10ss2_h_order hh hn, fun y hy hyc => ?_⟩
    rw [CFSG.RankThree.GF2n.Tim79a.spCoreStmt_holds n F hvi hT] at hy
    exact l10ss2_long_fix_pos hT hh hfix.1 hfix.2 hy hyc
  · obtain ⟨h, hh⟩ := l10ss2_exists_h (F := F) i
    have hT := l10ss2_isTransGroup_neg (n := n) (F := F) (γ := β) hneg.symm
    have hfix := l10ss2_h_plane (i := i) hh
    have hvi : (Pi.single (Sum.inr i) (1 : F) : Fin n ⊕ Fin n → F) ≠ 0 := by
      intro h0; have := congrFun h0 (Sum.inr i); simp at this
    have hmem : h ∈ Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F)) := by
      rw [CFSG.Timmesfeld.Transvection.ModelRank.normalizer_eq_spLine hvi hT]
      exact ⟨1, one_ne_zero, by rw [hfix.2, one_smul]⟩
    refine ⟨h, hmem, l10ss2_h_order hh hn, fun y hy hyc => ?_⟩
    rw [CFSG.RankThree.GF2n.Tim79a.spCoreStmt_holds n F hvi hT] at hy
    exact l10ss2_long_fix_neg hT hh hfix.2 hfix.1 hy hyc

private theorem l10ss2_ggLongRoot_of_allEven {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hev : GGRootSp.AllEven (toStd n β)) : GGLongRoot (Symplectic.rootDatum n F) β := by
  have hn0 : 0 < n := by
    obtain ⟨r, -⟩ := exists_stdVec_of_mem_roots hβ
    rcases r with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hθe : GGRootSp.AllEven (toStd n θ) := by
    rw [hθstd]
    exact l10ss2_allEven_positiveLong _
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hmax : ∀ δ ∈ (Symplectic.rootDatum n F).roots, ∑ i, δ i ≤ ∑ i, θ i := by
    intro δ hδ
    obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hδ
    have h1 := two_mul_ht (n := n) δ
    rw [← hr'] at h1
    have h2 := GGRootSp.lv_stdVec_le r
    change ht (ι := Fin n) δ ≤ ht (ι := Fin n) θ
    omega
  have hθ' := hθ
  rcases hθ' with ⟨wθ, kθ, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hβ' : β ∈ roots (isFiniteType_cartanC n) ∅ := hβ
  rcases hβ' with ⟨w, k, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hkθ : ¬ kθ.val + 1 < n :=
    (GGRootSp.allEven_toStd_single_iff kθ).1
      ((GGRootSp.allEven_toStd_weylAction_iff wθ _).1 hθe)
  have hk : ¬ k.val + 1 < n :=
    (GGRootSp.allEven_toStd_single_iff k).1
      ((GGRootSp.allEven_toStd_weylAction_iff w _).1 hev)
  obtain rfl : k = kθ := Fin.ext (by have := k.isLt; have := kθ.isLt; omega)
  refine ⟨w * wθ⁻¹, _, hθ, hmax, ?_⟩
  exact (by rw [weylAction_mul_apply, weylAction_inv_apply_apply] :
    weylAction (isFiniteType_cartanC n) (w * wθ⁻¹)
      (weylAction (isFiniteType_cartanC n) wθ (Pi.single k 1)) =
        weylAction (isFiniteType_cartanC n) w (Pi.single k 1)).symm

private theorem l10ss2_shortIndex {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum n F) β) :
    (∃ i j : Fin n, ∃ hij : i ≠ j, stdVec (.difference i j hij) = toStd n β) ∨
      (∃ i j : Fin n, ∃ hij : i < j, stdVec (.positiveSum i j hij) = toStd n β) ∨
      (∃ i j : Fin n, ∃ hij : i < j, stdVec (.negativeSum i j hij) = toStd n β) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact absurd (l10ss2_ggLongRoot_of_allEven hβ
      (by rw [← hr]; exact l10ss2_allEven_positiveLong i)) hs
  · exact absurd (l10ss2_ggLongRoot_of_allEven hβ
      (by rw [← hr]; exact l10ss2_allEven_negativeLong i)) hs
  · exact Or.inl ⟨i, j, hij, hr⟩
  · exact Or.inr (Or.inl ⟨i, j, hij, hr⟩)
  · exact Or.inr (Or.inr ⟨i, j, hij, hr⟩)

private theorem l10ss2b_beta_symm {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u v : Fin n ⊕ Fin n → F) : (spForm n F).β u v = (spForm n F).β v u := by
  rw [ReflForm.β_swap_of_alt (spForm n F) (spForm_self n F) v u, CharTwo.neg_eq]

private theorem l10ss2b_beta_eq {n : ℕ} {F : Type} [Field F]
    (u v : Fin n ⊕ Fin n → F) :
    (spForm n F).β u v = CFSG.Timmesfeld.ARS.CaseM.spForm u v := by
  rw [CFSG.LieType.BorelTits.spForm_β, CFSG.Timmesfeld.ARS.CaseM.spForm]

private theorem l10ss2b_spJ_mulVec_single {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (b : Fin n ⊕ Fin n) :
    (spJ n F) *ᵥ Pi.single b (1 : F) = Pi.single b.swap 1 := by
  ext k
  rcases b with i | i <;> rcases k with k | k <;>
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, spJ, Matrix.fromBlocks,
      Fintype.sum_sum_type, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem l10ss2b_add_self {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) : v + v = 0 := by
  have h2 : (2 : F) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rwa [two_smul F v] at h2

private theorem l10ss2b_sigma {n : ℕ} {F : Type} [Field F] (c : F) :
    (spForm n F).σ c = c := rfl

private theorem l10ss2b_exists_h {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂) :
    ∃ h : ↥(StatedSp n F),
      (∀ v : Fin n ⊕ Fin n → F, natRep (StatedSp n F) h v =
        v + (spForm n F).β b₁ v • (a₁ + a₂) + (spForm n F).β b₂ v • a₁ +
          (spForm n F).β a₂ v • b₁ +
            ((spForm n F).β a₁ v + (spForm n F).β a₂ v) • b₂) ∧
      natRep (StatedSp n F) h a₁ = a₂ ∧ natRep (StatedSp n F) h a₂ = a₁ + a₂ ∧
        natRep (StatedSp n F) h b₁ = b₁ + b₂ ∧ natRep (StatedSp n F) h b₂ = b₁ := by
  have hB_a1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
  have hB_a2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
  have hB_a1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
  have hB_b1b2 : (spForm n F).β b₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.1
  have hB_a1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
  have hB_a2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
  have hB_b1a1 : (spForm n F).β b₁ a₁ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a1b1
  have hB_b2a2 : (spForm n F).β b₂ a₂ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a2b2
  have hB_b2b1 : (spForm n F).β b₂ b₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_b1b2
  have hB_a2a1 : (spForm n F).β a₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a1a2
  have hB_b1a2 : (spForm n F).β b₁ a₂ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a2b1
  have hB_b2a1 : (spForm n F).β b₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a1b2
  have hB_a1a1 : (spForm n F).β a₁ a₁ = 0 := spForm_self n F a₁
  have hB_a2a2 : (spForm n F).β a₂ a₂ = 0 := spForm_self n F a₂
  have hB_b1b1 : (spForm n F).β b₁ b₁ = 0 := spForm_self n F b₁
  have hB_b2b2 : (spForm n F).β b₂ b₂ = 0 := spForm_self n F b₂
  obtain ⟨s₁, hs₁⟩ :=
    CFSG.QuasithinUnique.B113Lie.Sp.exists_siegel (r := n) (K := F) b₁ a₂ hB_b1a2
  obtain ⟨s₂, hs₂⟩ :=
    CFSG.QuasithinUnique.B113Lie.Sp.exists_siegel (r := n) (K := F) b₂ a₁ hB_b2a1
  have hformula : ∀ v : Fin n ⊕ Fin n → F, natRep (StatedSp n F) (s₂ * s₁) v =
      v + (spForm n F).β b₁ v • (a₁ + a₂) + (spForm n F).β b₂ v • a₁ +
        (spForm n F).β a₂ v • b₁ +
          ((spForm n F).β a₁ v + (spForm n F).β a₂ v) • b₂ := by
    intro v
    rw [map_mul, Module.End.mul_apply, hs₂]
    have hb2s1 : (spForm n F).β b₂ (natRep (StatedSp n F) s₁ v) =
        (spForm n F).β b₂ v + (spForm n F).β b₁ v := by
      rw [hs₁, (spForm n F).add_right, (spForm n F).add_right, (spForm n F).smul_right,
        (spForm n F).smul_right, hB_b2a2, hB_b2b1]
      ring
    have ha1s1 : (spForm n F).β a₁ (natRep (StatedSp n F) s₁ v) =
        (spForm n F).β a₁ v + (spForm n F).β a₂ v := by
      rw [hs₁, (spForm n F).add_right, (spForm n F).add_right, (spForm n F).smul_right,
        (spForm n F).smul_right, hB_a1a2, hB_a1b1]
      ring
    rw [hb2s1, ha1s1, hs₁]
    module
  refine ⟨s₂ * s₁, hformula, ?_, ?_, ?_, ?_⟩
  · rw [hformula a₁]
    simp only [hB_b1a1, hB_b2a1, hB_a2a1, hB_a1a1, hB_a2a1, one_smul, zero_smul, add_zero,
      zero_add]
    rw [← add_assoc, l10ss2b_add_self, zero_add]
  · rw [hformula a₂]
    simp only [hB_b1a2, hB_b2a2, hB_a2a2, hB_a1a2, hB_a2a2, one_smul, zero_smul, add_zero,
      zero_add]
    exact add_comm a₂ a₁
  · rw [hformula b₁]
    simp only [hB_b1b1, hB_b2b1, hB_a2b1, hB_a1b1, hB_a2b1, one_smul, zero_smul, add_zero,
      zero_add]
  · rw [hformula b₂]
    simp only [hB_b1b2, hB_b2b2, hB_a2b2, hB_a1b2, hB_a2b2, one_smul, zero_smul, add_zero,
      zero_add]
    rw [add_comm b₂ b₁, add_assoc, l10ss2b_add_self, add_zero]

private theorem l10ss2b_perp_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (hW : (spForm n F).IsTotallyIsotropic
      (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)))) :
    (spForm n F).perp (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) =
      Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) ⊔
        (spForm n F).perp
          (Submodule.span F ({a₁, a₂, b₁, b₂} : Set (Fin n ⊕ Fin n → F))) ∧
      (spForm n F).perp (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) ⊔
        Submodule.span F ({b₁, b₂} : Set (Fin n ⊕ Fin n → F)) = ⊤ := by
  have hB_a1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
  have hB_a2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
  have hB_a1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
  have hB_a1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
  have hB_a2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
  have hB_b1a1 : (spForm n F).β b₁ a₁ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a1b1
  have hB_b2a2 : (spForm n F).β b₂ a₂ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a2b2
  have hB_a2a1 : (spForm n F).β a₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a1a2
  have hB_b1a2 : (spForm n F).β b₁ a₂ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a2b1
  have hB_b2a1 : (spForm n F).β b₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a1b2
  have hB_a1a1 : (spForm n F).β a₁ a₁ = 0 := spForm_self n F a₁
  have hB_a2a2 : (spForm n F).β a₂ a₂ = 0 := spForm_self n F a₂
  constructor
  · refine le_antisymm ?_ ?_
    · intro v hv
      have hv1 : (spForm n F).β a₁ v = 0 := hv a₁ (Submodule.subset_span (by simp))
      have hv2 : (spForm n F).β a₂ v = 0 := hv a₂ (Submodule.subset_span (by simp))
      set y := (spForm n F).β b₁ v • a₁ + (spForm n F).β b₂ v • a₂ with hy
      refine Submodule.mem_sup.mpr
        ⟨y, Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))), v - y, ?_, by abel⟩
      rw [(spForm n F).mem_perp]
      intro w hw
      refine Submodule.span_induction
        (p := fun w _ => (spForm n F).β w (v - y) = 0) ?_ ?_ ?_ ?_ hw
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [(spForm n F).β_sub_right, hy, (spForm n F).add_right,
            (spForm n F).smul_right, (spForm n F).smul_right, hB_a1a1, hB_a1a2, hv1]
          ring
        · rw [(spForm n F).β_sub_right, hy, (spForm n F).add_right,
            (spForm n F).smul_right, (spForm n F).smul_right, hB_a2a1, hB_a2a2, hv2]
          ring
        · rw [(spForm n F).β_sub_right, hy, (spForm n F).add_right,
            (spForm n F).smul_right, (spForm n F).smul_right, hB_b1a1, hB_b1a2]
          ring
        · rw [(spForm n F).β_sub_right, hy, (spForm n F).add_right,
            (spForm n F).smul_right, (spForm n F).smul_right, hB_b2a1, hB_b2a2]
          ring
      · exact (spForm n F).β_zero_left (v - y)
      · intro x z _ _ hx hz
        rw [(spForm n F).add_left, hx, hz, add_zero]
      · intro c x _ hx
        rw [(spForm n F).smul_left, hx, mul_zero]
    · refine sup_le hW ?_
      · exact ReflForm.perp_antitone (spForm n F)
          (Submodule.span_mono (by
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
            tauto))
  · refine eq_top_iff.mpr fun v _ => ?_
    set b := (spForm n F).β a₁ v • b₁ + (spForm n F).β a₂ v • b₂ with hb
    refine Submodule.mem_sup.mpr
      ⟨v - b, ?_, b, Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))), by abel⟩
    rw [(spForm n F).mem_perp]
    intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [(spForm n F).add_left, (spForm n F).smul_left, (spForm n F).β_sub_right, hb,
      (spForm n F).add_right, (spForm n F).smul_right, hB_a1b1, hB_a2b2, hB_a1a2, hB_a2b1,
      hB_a1b2, l10ss2b_sigma]
    ring

private theorem l10ss2b_order {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (hW : (spForm n F).IsTotallyIsotropic
      (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))))
    {h : ↥(StatedSp n F)}
    (hha₁ : natRep (StatedSp n F) h a₁ = a₂)
    (hha₂ : natRep (StatedSp n F) h a₂ = a₁ + a₂)
    (hhb₁ : natRep (StatedSp n F) h b₁ = b₁ + b₂)
    (hhb₂ : natRep (StatedSp n F) h b₂ = b₁)
    (hfixZ : ∀ v ∈ (spForm n F).perp
      (Submodule.span F ({a₁, a₂, b₁, b₂} : Set (Fin n ⊕ Fin n → F))),
      natRep (StatedSp n F) h v = v) :
    orderOf h = 3 := by
  set H : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) h with hH
  have htop := (l10ss2b_perp_eq hp hW).2
  have hYperp := (l10ss2b_perp_eq hp hW).1
  have hHa₁ : H a₁ = a₂ := hha₁
  have hHa₂ : H a₂ = a₁ + a₂ := hha₂
  have hHb₁ : H b₁ = b₁ + b₂ := hhb₁
  have hHb₂ : H b₂ = b₁ := hhb₂
  have h3 : H ^ 3 = H * H * H := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one]
  have h3a₁ : (H ^ 3) a₁ = a₁ := by
    calc (H ^ 3) a₁ = H (H (H a₁)) := by rw [h3, Module.End.mul_apply, Module.End.mul_apply]
      _ = H (H a₂) := by rw [hHa₁]
      _ = H (a₁ + a₂) := by rw [hHa₂]
      _ = H a₁ + H a₂ := by rw [map_add]
      _ = a₂ + (a₁ + a₂) := by rw [hHa₁, hHa₂]
      _ = a₁ := by rw [add_comm a₂ (a₁ + a₂), add_assoc, l10ss2b_add_self, add_zero]
  have h3a₂ : (H ^ 3) a₂ = a₂ := by
    calc (H ^ 3) a₂ = H (H (H a₂)) := by rw [h3, Module.End.mul_apply, Module.End.mul_apply]
      _ = H (H (a₁ + a₂)) := by rw [hHa₂]
      _ = H (H a₁ + H a₂) := by rw [map_add]
      _ = H (a₂ + (a₁ + a₂)) := by rw [hHa₁, hHa₂]
      _ = H a₁ := by rw [show a₂ + (a₁ + a₂) = a₁ by
            rw [add_comm a₂ (a₁ + a₂), add_assoc, l10ss2b_add_self, add_zero]]
      _ = a₂ := by rw [hHa₁]
  have h3b₁ : (H ^ 3) b₁ = b₁ := by
    calc (H ^ 3) b₁ = H (H (H b₁)) := by rw [h3, Module.End.mul_apply, Module.End.mul_apply]
      _ = H (H (b₁ + b₂)) := by rw [hHb₁]
      _ = H (H b₁ + H b₂) := by rw [map_add]
      _ = H ((b₁ + b₂) + b₁) := by rw [hHb₁, hHb₂]
      _ = H b₂ := by rw [show (b₁ + b₂) + b₁ = b₂ by
            rw [add_comm (b₁ + b₂) b₁, ← add_assoc, l10ss2b_add_self, zero_add]]
      _ = b₁ := by rw [hHb₂]
  have h3b₂ : (H ^ 3) b₂ = b₂ := by
    calc (H ^ 3) b₂ = H (H (H b₂)) := by rw [h3, Module.End.mul_apply, Module.End.mul_apply]
      _ = H (H b₁) := by rw [hHb₂]
      _ = H (b₁ + b₂) := by rw [hHb₁]
      _ = H b₁ + H b₂ := by rw [map_add]
      _ = (b₁ + b₂) + b₁ := by rw [hHb₁, hHb₂]
      _ = b₂ := by rw [add_comm (b₁ + b₂) b₁, ← add_assoc, l10ss2b_add_self, zero_add]
  have h3z : ∀ z ∈ (spForm n F).perp
      (Submodule.span F ({a₁, a₂, b₁, b₂} : Set (Fin n ⊕ Fin n → F))), (H ^ 3) z = z := by
    intro z hz
    rw [h3, Module.End.mul_apply, Module.End.mul_apply]
    simp only [hfixZ z hz]
  have hcube : h ^ 3 = 1 := by
    apply natRep_injective (StatedSp n F)
    rw [map_pow, map_one]
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ (spForm n F).perp (Submodule.span F ({a₁, a₂} : Set _)) ⊔
        Submodule.span F ({b₁, b₂} : Set _) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    congr 1
    · have hw' : w ∈ Submodule.span F ({a₁, a₂} : Set _) ⊔
          (spForm n F).perp
            (Submodule.span F ({a₁, a₂, b₁, b₂} : Set _)) := by rw [← hYperp]; exact hw
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw'
      rw [map_add]
      congr 1
      · obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hy
        rw [map_add, map_smul, map_smul]
        rw [show ((natRep (StatedSp n F)) h ^ 3) a₁ = a₁ from h3a₁,
          show ((natRep (StatedSp n F)) h ^ 3) a₂ = a₂ from h3a₂]
      · exact h3z z hz
    · obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hb
      rw [map_add, map_smul, map_smul]
      rw [show ((natRep (StatedSp n F)) h ^ 3) b₁ = b₁ from h3b₁,
        show ((natRep (StatedSp n F)) h ^ 3) b₂ = b₂ from h3b₂]
  have ha12 : a₁ ≠ a₂ := by
    intro h12
    have hb1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
    have hb2 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
    rw [← h12, hb1] at hb2
    exact zero_ne_one hb2.symm
  refine orderOf_eq_prime hcube ?_
  intro h1
  have hthis := hha₁
  rw [hH] at hthis
  rw [h1, map_one, Module.End.one_apply] at hthis
  exact ha12 hthis

private theorem l10ss2b_fix_short {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {h : ↥(StatedSp n F)}
    (hh : ∀ v : Fin n ⊕ Fin n → F, natRep (StatedSp n F) h v =
      v + (spForm n F).β b₁ v • (a₁ + a₂) + (spForm n F).β b₂ v • a₁ +
        (spForm n F).β a₂ v • b₁ +
          ((spForm n F).β a₁ v + (spForm n F).β a₂ v) • b₂)
    (hha₁ : natRep (StatedSp n F) h a₁ = a₂)
    (hha₂ : natRep (StatedSp n F) h a₂ = a₁ + a₂)
    (hhb₁ : natRep (StatedSp n F) h b₁ = b₁ + b₂)
    (hhb₂ : natRep (StatedSp n F) h b₂ = b₁)
    {hW : (spForm n F).IsTotallyIsotropic
      (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)))}
    {y : ↥(StatedSp n F)}
    (hy : y ∈ CFSG.QuasithinUnique.B113Lie.Sp.sprad
      (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) hW)
    (hycomm : h * y = y * h) :
    y ∈ spAltSiegel n F a₁ a₂ := by
  set Y : Submodule F (Fin n ⊕ Fin n → F) :=
    Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) with hY
  set W4 : Submodule F (Fin n ⊕ Fin n → F) :=
    Submodule.span F ({a₁, a₂, b₁, b₂} : Set (Fin n ⊕ Fin n → F)) with hW4
  set Z : Submodule F (Fin n ⊕ Fin n → F) := (spForm n F).perp W4 with hZ
  set T : Module.End F (Fin n ⊕ Fin n → F) := natRep (StatedSp n F) y - 1 with hT
  have ha₁ : a₁ ∈ Y := Submodule.subset_span (by simp)
  have ha₂ : a₂ ∈ Y := Submodule.subset_span (by simp)
  have hB_a1b1 : (spForm n F).β a₁ b₁ = 1 := by rw [spForm_β]; exact hp.1
  have hB_a2b2 : (spForm n F).β a₂ b₂ = 1 := by rw [spForm_β]; exact hp.2.1
  have hB_a1a2 : (spForm n F).β a₁ a₂ = 0 := by rw [spForm_β]; exact hp.2.2.1
  have hB_a1b2 : (spForm n F).β a₁ b₂ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.1
  have hB_a2b1 : (spForm n F).β a₂ b₁ = 0 := by rw [spForm_β]; exact hp.2.2.2.2.2
  have hB_b1a1 : (spForm n F).β b₁ a₁ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a1b1
  have hB_b2a2 : (spForm n F).β b₂ a₂ = 1 := by rw [l10ss2b_beta_symm]; exact hB_a2b2
  have hB_b2a1 : (spForm n F).β b₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a1b2
  have hB_b1a2 : (spForm n F).β b₁ a₂ = 0 := by rw [l10ss2b_beta_symm]; exact hB_a2b1
  have hYfix : ∀ w ∈ Y, natRep (StatedSp n F) y w = w := hy.1
  have hTY : ∀ w ∈ Y, T w = 0 := by
    intro w hw
    rw [hT]
    simp only [LinearMap.sub_apply, Module.End.one_apply, hYfix w hw, sub_self]
  have hYperp_mod : ∀ v ∈ (spForm n F).perp Y,
      natRep (StatedSp n F) h v - v ∈ Y := by
    intro v hv
    have hv1 : (spForm n F).β a₁ v = 0 := hv a₁ ha₁
    have hv2 : (spForm n F).β a₂ v = 0 := hv a₂ ha₂
    have hval : natRep (StatedSp n F) h v - v =
        (spForm n F).β b₁ v • (a₁ + a₂) + (spForm n F).β b₂ v • a₁ := by
      rw [hh v, hv1, hv2]
      simp only [zero_smul, zero_add, add_zero]
      abel
    rw [hval]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ ha₁ ha₂))
      (Submodule.smul_mem _ _ ha₁)
  have hfixZh : ∀ z ∈ Z, natRep (StatedSp n F) h z = z := by
    intro z hz
    have hz1 : (spForm n F).β a₁ z = 0 := hz a₁ (Submodule.subset_span (by simp))
    have hz2 : (spForm n F).β a₂ z = 0 := hz a₂ (Submodule.subset_span (by simp))
    have hz3 : (spForm n F).β b₁ z = 0 := hz b₁ (Submodule.subset_span (by simp))
    have hz4 : (spForm n F).β b₂ z = 0 := hz b₂ (Submodule.subset_span (by simp))
    rw [hh z]
    simp only [hz1, hz2, hz3, hz4, zero_smul, zero_add, add_zero]
  have hnoFixY : ∀ u ∈ Y, natRep (StatedSp n F) h u = u → u = 0 := by
    intro u hu hueq
    have hu1 : (spForm n F).β a₁ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW ha₁) u hu
    have hu2 : (spForm n F).β a₂ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW ha₂) u hu
    have hmod : (spForm n F).β b₁ u • (a₁ + a₂) + (spForm n F).β b₂ u • a₁ = 0 := by
      have hthis := congrArg (fun w => w - u) hueq
      rw [hh u, hu1, hu2] at hthis
      simp only [zero_smul, zero_add, add_zero] at hthis
      abel_nf at hthis
      exact hthis
    have hb1u : (spForm n F).β b₁ u = 0 := by
      have h := congrArg (fun w => (spForm n F).β b₂ w) hmod
      simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b2a1, hB_b2a2,
        (spForm n F).β_zero_right, mul_zero, mul_one, add_zero, zero_add] at h
      exact h
    have hb2u : (spForm n F).β b₂ u = 0 := by
      have h := congrArg (fun w => (spForm n F).β b₁ w) hmod
      simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b1a1, hB_b1a2,
        (spForm n F).β_zero_right, hb1u, mul_zero, mul_one, add_zero, zero_add] at h
      exact h
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
    have hα : α = 0 := by
      have h : (spForm n F).β b₁ (α • a₁ + β • a₂) = 0 := hb1u
      simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b1a1, hB_b1a2,
        mul_one, mul_zero, add_zero] at h
      exact h
    have hβ : β = 0 := by
      have h : (spForm n F).β b₂ (α • a₁ + β • a₂) = 0 := hb2u
      simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b2a1, hB_b2a2,
        mul_zero, mul_one, add_zero, zero_add] at h
      exact h
    rw [hα, hβ, zero_smul, zero_smul, add_zero]
  have hTVperp : ∀ v, T v ∈ (spForm n F).perp Y := by
    intro v
    rw [(spForm n F).mem_perp]
    intro w hw
    have hyinv : natRep (StatedSp n F) y⁻¹ w = w := (inv_mem hy).1 w hw
    have hiso := isIsometric_natRep_statedSp n F y (natRep (StatedSp n F) y⁻¹ w) v
    rw [show natRep (StatedSp n F) y (natRep (StatedSp n F) y⁻¹ w) = w by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]] at hiso
    rw [hyinv] at hiso
    rw [hT]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [(spForm n F).β_sub_right, hiso, sub_self]
  have hcommT : T * natRep (StatedSp n F) h = natRep (StatedSp n F) h * T := by
    rw [hT]
    have hcommY : natRep (StatedSp n F) y * natRep (StatedSp n F) h =
        natRep (StatedSp n F) h * natRep (StatedSp n F) y := by
      rw [← map_mul, ← map_mul, hycomm]
    rw [sub_mul, one_mul, mul_sub, mul_one, hcommY]
  have hYmaps : ∀ u ∈ Y, natRep (StatedSp n F) h u ∈ Y := by
    intro u hu
    have hu1 : (spForm n F).β a₁ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW ha₁) u hu
    have hu2 : (spForm n F).β a₂ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW ha₂) u hu
    have hval : natRep (StatedSp n F) h u =
        u + (spForm n F).β b₁ u • (a₁ + a₂) + (spForm n F).β b₂ u • a₁ := by
      rw [hh u, hu1, hu2]
      simp only [zero_smul, zero_add, add_zero]
    rw [hval]
    exact Submodule.add_mem _ (Submodule.add_mem _ hu
      (Submodule.smul_mem _ _ (Submodule.add_mem _ ha₁ ha₂)))
      (Submodule.smul_mem _ _ ha₁)
  have hfixZ : ∀ z ∈ Z, T z = 0 := by
    intro z hz
    have hzY : z ∈ (spForm n F).perp Y := by
      rw [hZ] at hz
      exact ReflForm.perp_antitone (spForm n F)
        (Submodule.span_mono (by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
          tauto)) hz
    have hzT : T z ∈ Y := hy.2 z hzY
    have h1 : T z = T (natRep (StatedSp n F) h z) := by rw [hfixZh z hz]
    have h2 : T (natRep (StatedSp n F) h z) = natRep (StatedSp n F) h (T z) := by
      have hthis := congrArg (fun (f : Module.End F (Fin n ⊕ Fin n → F)) => f z) hcommT
      simpa only [Module.End.mul_apply] using hthis
    exact hnoFixY (T z) hzT (h1.trans h2).symm
  have hTb₂ : T b₂ ∈ Y := by
    have hthis := congrArg (fun (f : Module.End F (Fin n ⊕ Fin n → F)) => f b₁) hcommT
    simp only [Module.End.mul_apply] at hthis
    rw [show natRep (StatedSp n F) h b₁ = b₁ + b₂ from hhb₁, map_add] at hthis
    have h2 : T b₂ = natRep (StatedSp n F) h (T b₁) - T b₁ := by rw [← hthis]; abel
    rw [h2]
    exact hYperp_mod (T b₁) (hTVperp b₁)
  have hTb₁ : T b₁ ∈ Y := by
    have hthis := congrArg (fun (f : Module.End F (Fin n ⊕ Fin n → F)) => f b₂) hcommT
    simp only [Module.End.mul_apply] at hthis
    rw [show natRep (StatedSp n F) h b₂ = b₁ from hhb₂] at hthis
    rw [hthis]
    exact hYmaps (T b₂) hTb₂
  have hTV : ∀ v, T v ∈ Y := by
    intro v
    have hv : v ∈ (spForm n F).perp Y ⊔ Submodule.span F ({b₁, b₂} : Set _) := by
      rw [(l10ss2b_perp_eq hp hW).2]; exact Submodule.mem_top
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    refine Submodule.add_mem _ (hy.2 w hw) ?_
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hb
    rw [map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hTb₁) (Submodule.smul_mem _ _ hTb₂)
  have hself : ∀ x w, (spForm n F).β (T x) w = (spForm n F).β x (T w) := by
    intro x w
    have hzero : (spForm n F).β (T x) (T w) = 0 := by
      rw [l10ss2b_beta_symm]
      exact (hW (hTV x)) (T w) (hTV w)
    have hx : natRep (StatedSp n F) y x = x + T x := by
      rw [hT]; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
    have hw : natRep (StatedSp n F) y w = w + T w := by
      rw [hT]; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
    have h := isIsometric_natRep_statedSp n F y x w
    rw [hx, hw, (spForm n F).add_left, (spForm n F).add_right, (spForm n F).add_right,
      hzero, add_zero] at h
    have hsum : (spForm n F).β (T x) w + (spForm n F).β x (T w) = 0 := by
      have h3 := h
      rw [add_assoc] at h3
      have h4 : (spForm n F).β x (T w) + (spForm n F).β (T x) w = 0 :=
        add_left_cancel (by rw [add_zero]; exact h3)
      rwa [add_comm] at h4
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
    exact hsum
  have hframe₁ : T b₁ + T b₂ = natRep (StatedSp n F) h (T b₁) := by
    have hthis := congrArg (fun (f : Module.End F (Fin n ⊕ Fin n → F)) => f b₁) hcommT
    simp only [Module.End.mul_apply] at hthis
    rw [show natRep (StatedSp n F) h b₁ = b₁ + b₂ from hhb₁, map_add] at hthis
    exact hthis
  have hframe₂ : T b₁ = natRep (StatedSp n F) h (T b₂) := by
    have hthis := congrArg (fun (f : Module.End F (Fin n ⊕ Fin n → F)) => f b₂) hcommT
    simp only [Module.End.mul_apply] at hthis
    rw [show natRep (StatedSp n F) h b₂ = b₁ from hhb₂] at hthis
    exact hthis
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hTb₁
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp hTb₂
  have hHpq : natRep (StatedSp n F) h (T b₁) = q • a₁ + (p + q) • a₂ := by
    rw [← hpq, map_add, map_smul, map_smul, hha₁, hha₂]
    module
  have hHrs : natRep (StatedSp n F) h (T b₂) = s • a₁ + (r + s) • a₂ := by
    rw [← hrs, map_add, map_smul, map_smul, hha₁, hha₂]
    module
  have hs_eq_p : s = p := by
    have h := congrArg (fun w => (spForm n F).β b₁ w) hframe₂
    rw [← hpq, hHrs] at h
    simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b1a1, hB_b1a2,
      mul_one, mul_zero, add_zero, zero_add] at h
    exact h.symm
  have hq_eq_rs : q = r + s := by
    have h := congrArg (fun w => (spForm n F).β b₂ w) hframe₂
    rw [← hpq, hHrs] at h
    simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b2a1, hB_b2a2,
      mul_zero, mul_one, add_zero, zero_add] at h
    exact h
  have hp_add_r : p + r = q := by
    have h := congrArg (fun w => (spForm n F).β b₁ w) hframe₁
    rw [hHpq] at h
    rw [← hpq, ← hrs] at h
    simp only [(spForm n F).add_right, (spForm n F).smul_right, hB_b1a1, hB_b1a2,
      mul_one, mul_zero, add_zero, zero_add] at h
    exact h
  have hq_eq_r : q = r := by
    have h := hself b₁ b₂
    rw [← hpq, ← hrs] at h
    simp only [(spForm n F).add_left, (spForm n F).add_right, (spForm n F).smul_left,
      (spForm n F).smul_right, hB_a1b2, hB_a2b2, hB_b1a1, hB_b1a2, mul_zero, mul_one,
      add_zero, zero_add, l10ss2b_sigma] at h
    exact h
  have hp0 : p = 0 := by
    have h := hp_add_r
    rw [hq_eq_r] at h
    exact add_right_cancel (by rw [zero_add]; exact h)
  have hs0 : s = 0 := by rw [hs_eq_p, hp0]
  have hTb₁' : T b₁ = q • a₂ := by
    rw [← hpq, hp0, zero_smul, zero_add]
  have hTb₂' : T b₂ = q • a₁ := by
    rw [← hrs, hs0, zero_smul, add_zero, ← hq_eq_r]
  have hT_eq : ∀ v, T v =
      (q * (spForm n F).β a₂ v) • a₁ + (q * (spForm n F).β a₁ v) • a₂ := by
    intro v
    have hv : v ∈ (spForm n F).perp Y ⊔ Submodule.span F ({b₁, b₂} : Set _) := by
      rw [(l10ss2b_perp_eq hp hW).2]; exact Submodule.mem_top
    obtain ⟨w, hw, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have hTw : T w = 0 := by
      have hw' : w ∈ Y ⊔ Z := by
        rw [← (l10ss2b_perp_eq hp hW).1]; exact hw
      obtain ⟨y', hy', z, hz, hwz⟩ := Submodule.mem_sup.mp hw'
      rw [← hwz, map_add, hTY y' hy', hfixZ z hz, add_zero]
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hb
    rw [map_add, hTw, zero_add, map_add, map_smul, map_smul, hTb₁', hTb₂']
    simp only [(spForm n F).add_right, (spForm n F).smul_right, hw a₁ ha₁, hw a₂ ha₂,
      hB_a1b1, hB_a2b2, hB_a1b2, hB_a2b1]
    module
  have hyv : ∀ v, natRep (StatedSp n F) y v = v + T v := by
    intro v
    rw [hT]; simp only [LinearMap.sub_apply, Module.End.one_apply]; abel
  refine mem_spAltSiegel_of_mulVec q (fun v => ?_)
  rw [← natRep_apply, hyv v, hT_eq v, spForm_β, spForm_β]
  ring

private theorem l10ss2b_beta_inl_inl {n : ℕ} {F : Type} [Field F] [CharP F 2] (i j : Fin n) :
    (spForm n F).β (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inl j) 1) = 0 := by
  rw [l10ss2b_beta_eq]; exact l10ss2_spForm_inl_inl i j

private theorem l10ss2b_beta_inr_inr {n : ℕ} {F : Type} [Field F] [CharP F 2] (i j : Fin n) :
    (spForm n F).β (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inr j) 1) = 0 := by
  rw [l10ss2b_beta_eq]; exact l10ss2_spForm_inr_inr i j

private theorem l10ss2b_beta_inl_inr {n : ℕ} {F : Type} [Field F] [CharP F 2] (i j : Fin n) :
    (spForm n F).β (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) =
      if i = j then 1 else 0 := by
  rw [l10ss2b_beta_eq]; exact l10ss2_spForm_inl_inr i j

private theorem l10ss2b_beta_inr_inl {n : ℕ} {F : Type} [Field F] [CharP F 2] (i j : Fin n) :
    (spForm n F).β (Pi.single (Sum.inr i) 1) (Pi.single (Sum.inl j) 1) =
      if i = j then 1 else 0 := by
  rw [l10ss2b_beta_eq]; exact l10ss2_spForm_inr_inl i j

private theorem l10ss2b_isTotallyIsotropic {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F}
    (h11 : (spForm n F).β a₁ a₁ = 0) (h12 : (spForm n F).β a₁ a₂ = 0)
    (h22 : (spForm n F).β a₂ a₂ = 0) :
    (spForm n F).IsTotallyIsotropic (Submodule.span F ({a₁, a₂} : Set _)) := by
  have h21 : (spForm n F).β a₂ a₁ = 0 := by rw [l10ss2b_beta_symm]; exact h12
  intro x hx y hy
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨e, f, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp only [(spForm n F).add_left, (spForm n F).add_right, (spForm n F).smul_left,
    (spForm n F).smul_right, h11, h12, h21, h22, l10ss2b_sigma]
  ring

private theorem l10ss2b_vecMulVec_single_single {ι F : Type} [Field F] [DecidableEq ι]
    (i j : ι) (c d : F) :
    Matrix.vecMulVec (Pi.single i c) (Pi.single j d) = Matrix.single i j (c * d) := by
  ext a b
  change (Pi.single i c : ι → F) a * (Pi.single j d : ι → F) b = Matrix.single i j (c * d) a b
  simp only [Pi.single_apply, Matrix.single_apply]
  split_ifs <;> simp_all [mul_zero, zero_mul, mul_one]

private theorem l10ss2b_rootGroup_eq_spAltSiegel {n : ℕ} {F : Type} [Field F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n β) {a₁ a₂ : Fin n ⊕ Fin n → F}
    (hE : E F r = Matrix.vecMulVec a₁ ((spJ n F) *ᵥ a₂) +
      Matrix.vecMulVec a₂ ((spJ n F) *ᵥ a₁)) :
    (Symplectic.rootDatum n F).rootGroup β = spAltSiegel n F a₁ a₂ := by
  rw [show (Symplectic.rootDatum n F).rootGroup β = rootGroup n F β from rfl]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_rootGroup_iff hr] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [spAltSiegel]
    refine Subgroup.mem_comap.mpr ?_
    refine Subgroup.subset_closure ⟨c, ?_⟩
    change SpExtras.mat n F (elt r c) = 1 + c • (Matrix.vecMulVec a₁ ((spJ n F) *ᵥ a₂) +
      Matrix.vecMulVec a₂ ((spJ n F) *ᵥ a₁))
    rw [SpExtras.mat_elt, hE]
  · intro x hx
    rw [spAltSiegel, Subgroup.mem_comap] at hx
    have hle : Subgroup.closure {g : GL (Fin n ⊕ Fin n) F | ∃ c : F,
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          1 + c • (Matrix.vecMulVec a₁ ((spJ n F) *ᵥ a₂) +
            Matrix.vecMulVec a₂ ((spJ n F) *ᵥ a₁))} ≤
        (rootGroup n F β).map (StatedSp n F).subtype := by
      rw [Subgroup.closure_le]
      rintro g ⟨c, hc⟩
      refine ⟨elt r c, ?_, ?_⟩
      · exact (mem_rootGroup_iff hr).2 ⟨c, rfl⟩
      · refine Units.ext ?_
        rw [hc]
        change SpExtras.mat n F (elt r c) = 1 + c •
          (Matrix.vecMulVec a₁ ((spJ n F) *ᵥ a₂) + Matrix.vecMulVec a₂ ((spJ n F) *ᵥ a₁))
        rw [SpExtras.mat_elt, hE]
    obtain ⟨y, hy, hyx⟩ := hle hx
    rw [← Subtype.ext hyx]
    exact hy

private theorem l10ss2b_short_case {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    (hW : (spForm n F).IsTotallyIsotropic
      (Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))))
    (hroot : (Symplectic.rootDatum n F).rootGroup β = spAltSiegel n F a₁ a₂) :
    ∃ h ∈ Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F)),
      orderOf h = 3 ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F))), h * y = y * h →
        y ∈ (Symplectic.rootDatum n F).rootGroup β := by
  obtain ⟨h, hh, hha₁, hha₂, hhb₁, hhb₂⟩ := l10ss2b_exists_h hp
  have hfixZ : ∀ v ∈ (spForm n F).perp
      (Submodule.span F ({a₁, a₂, b₁, b₂} : Set (Fin n ⊕ Fin n → F))),
      natRep (StatedSp n F) h v = v := by
    intro v hv
    rw [hh v]
    have hv1 : (spForm n F).β a₁ v = 0 := hv a₁ (Submodule.subset_span (by simp))
    have hv2 : (spForm n F).β a₂ v = 0 := hv a₂ (Submodule.subset_span (by simp))
    have hv3 : (spForm n F).β b₁ v = 0 := hv b₁ (Submodule.subset_span (by simp))
    have hv4 : (spForm n F).β b₂ v = 0 := hv b₂ (Submodule.subset_span (by simp))
    simp only [hv1, hv2, hv3, hv4, zero_smul, zero_add, add_zero]
  have hord : orderOf h = 3 := l10ss2b_order hp hW hha₁ hha₂ hhb₁ hhb₂ hfixZ
  have hYmaps : ∀ u ∈ Submodule.span F ({a₁, a₂} : Set _),
      natRep (StatedSp n F) h u ∈ Submodule.span F ({a₁, a₂} : Set _) := by
    intro u hu
    have hu1 : (spForm n F).β a₁ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW (Submodule.subset_span (by simp))) u hu
    have hu2 : (spForm n F).β a₂ u = 0 := by
      rw [l10ss2b_beta_symm]; exact (hW (Submodule.subset_span (by simp))) u hu
    rw [hh u, hu1, hu2]
    simp only [zero_smul, zero_add, add_zero]
    exact Submodule.add_mem _ (Submodule.add_mem _ hu
      (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp)))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  refine ⟨h, ?_, hord, fun y hy hyc => ?_⟩
  · rw [hroot, normalizer_spAltSiegel_eq_stabilizer hp]
    refine SymplecticFlag.mem_stabilizer_of_mulVec_mem ?_ ?_
    · intro v hv
      rw [← natRep_apply]
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
      rw [map_add, map_smul, map_smul, hha₁, hha₂]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp))))
    · intro v hv
      rw [← natRep_apply]
      have hcube : h ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one h
      have hinv : (h⁻¹ : ↥(StatedSp n F)) = h * h := by
        rw [inv_eq_iff_mul_eq_one]
        rw [show h * (h * h) = h ^ 3 by
          rw [← mul_assoc, show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
            show (2 : ℕ) = 1 + 1 by norm_num, pow_succ, pow_one], hcube]
      rw [hinv, map_mul, Module.End.mul_apply]
      exact hYmaps (natRep (StatedSp n F) h v) (hYmaps v hv)
  · rw [hroot] at hy
    rw [normalizer_spAltSiegel_eq_stabilizer hp] at hy
    rw [hroot]
    exact l10ss2b_fix_short (hW := hW) hp hh hha₁ hha₂ hhb₁ hhb₂
      (pCoreOf_stabilizer_le_sprad hp hy) hyc

private theorem l10ss2_fpf_short {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ}
    (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum n F) β) :
    ∃ h ∈ Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) : Set ↥(StatedSp n F)),
      orderOf h = 3 ∧ ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
          Set ↥(StatedSp n F))), h * y = y * h → y ∈ (Symplectic.rootDatum n F).rootGroup β := by
  obtain ⟨i, j, hij, hβstd⟩ | ⟨i, j, hij, hβstd⟩ | ⟨i, j, hij, hβstd⟩ :=
    l10ss2_shortIndex hβ hs
  ·
    refine l10ss2b_short_case (a₁ := Pi.single (Sum.inl i) 1) (a₂ := Pi.single (Sum.inr j) 1)
      (b₁ := Pi.single (Sum.inr i) 1) (b₂ := Pi.single (Sum.inl j) 1) ?_ ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← spForm_β]
      · rw [l10ss2b_beta_inl_inr]; simp
      · rw [l10ss2b_beta_inr_inl]; simp
      · rw [l10ss2b_beta_inl_inr]; simp [hij]
      · rw [l10ss2b_beta_inr_inl]; simp [hij]
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inr_inr]
    · refine l10ss2b_isTotallyIsotropic ?_ ?_ ?_
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inl_inr]; simp [hij]
      · rw [l10ss2b_beta_inr_inr]
    · refine l10ss2b_rootGroup_eq_spAltSiegel hβstd ?_
      rw [show E F (.difference i j hij) = Matrix.single (Sum.inl i) (Sum.inl j) 1 +
        Matrix.single (Sum.inr j) (Sum.inr i) 1 by
          ext a b; simp [E, CharTwo.sub_eq_add]]
      rw [l10ss2b_spJ_mulVec_single, l10ss2b_spJ_mulVec_single,
        l10ss2b_vecMulVec_single_single, l10ss2b_vecMulVec_single_single]
      simp
  ·
    refine l10ss2b_short_case (a₁ := Pi.single (Sum.inl i) 1) (a₂ := Pi.single (Sum.inl j) 1)
      (b₁ := Pi.single (Sum.inr i) 1) (b₂ := Pi.single (Sum.inr j) 1) ?_ ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← spForm_β]
      · rw [l10ss2b_beta_inl_inr]; simp
      · rw [l10ss2b_beta_inl_inr]; simp
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inr_inr]
      · rw [l10ss2b_beta_inl_inr]; simp [hij.ne]
      · rw [l10ss2b_beta_inl_inr]; simp [hij.ne.symm]
    · refine l10ss2b_isTotallyIsotropic ?_ ?_ ?_
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inl_inl]
    · refine l10ss2b_rootGroup_eq_spAltSiegel hβstd ?_
      rw [show E F (.positiveSum i j hij) = Matrix.single (Sum.inl i) (Sum.inr j) 1 +
        Matrix.single (Sum.inl j) (Sum.inr i) 1 from rfl]
      rw [l10ss2b_spJ_mulVec_single, l10ss2b_spJ_mulVec_single,
        l10ss2b_vecMulVec_single_single, l10ss2b_vecMulVec_single_single]
      simp
  ·
    refine l10ss2b_short_case (a₁ := Pi.single (Sum.inr i) 1) (a₂ := Pi.single (Sum.inr j) 1)
      (b₁ := Pi.single (Sum.inl i) 1) (b₂ := Pi.single (Sum.inl j) 1) ?_ ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← spForm_β]
      · rw [l10ss2b_beta_inr_inl]; simp
      · rw [l10ss2b_beta_inr_inl]; simp
      · rw [l10ss2b_beta_inr_inr]
      · rw [l10ss2b_beta_inl_inl]
      · rw [l10ss2b_beta_inr_inl]; simp [hij.ne]
      · rw [l10ss2b_beta_inr_inl]; simp [hij.ne.symm]
    · refine l10ss2b_isTotallyIsotropic ?_ ?_ ?_
      · rw [l10ss2b_beta_inr_inr]
      · rw [l10ss2b_beta_inr_inr]
      · rw [l10ss2b_beta_inr_inr]
    · refine l10ss2b_rootGroup_eq_spAltSiegel hβstd ?_
      rw [show E F (.negativeSum i j hij) = Matrix.single (Sum.inr i) (Sum.inl j) 1 +
        Matrix.single (Sum.inr j) (Sum.inl i) 1 from rfl]
      rw [l10ss2b_spJ_mulVec_single, l10ss2b_spJ_mulVec_single,
        l10ss2b_vecMulVec_single_single, l10ss2b_vecMulVec_single_single]
      simp

private theorem l10ss2_fpf_map {K : Type*} [Group K] (e : K ≃* K) {X : Subgroup K} {h : K}
    (hhN : h ∈ Subgroup.normalizer (X : Set K))
    (hfix : ∀ y ∈ pCoreOf 2 (Subgroup.normalizer (X : Set K)), h * y = y * h → y ∈ X) :
    e h ∈ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup K) : Set K)),
        e h * y = y * e h → y ∈ X.map e.toMonoidHom := by
  constructor
  · rw [GGRootNorm.normalizer_map_mulEquiv e X, Subgroup.mem_map_equiv]
    simpa using hhN
  · intro y hy hcomm
    refine Subgroup.mem_map.mpr ⟨e.symm y, hfix (e.symm y) ?_ ?_, e.apply_symm_apply y⟩
    · rw [GGRootNorm.normalizer_map_mulEquiv e X,
        GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (X : Set K)),
        Subgroup.mem_map_equiv] at hy
      exact hy
    · apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hcomm

private theorem l10ss2_noCentral {n : ℕ} {F : Type} [Field F] [Finite F]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} {h : ↥(StatedSp n F)}
    (hhN : h ∈ Subgroup.normalizer
      (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
        Set ↥(StatedSp n F)))
    (hord : orderOf h = 3)
    (hfix : ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
      (((Symplectic.rootDatum n F).rootGroup β : Subgroup ↥(StatedSp n F)) :
        Set ↥(StatedSp n F))), h * y = y * h →
      y ∈ (Symplectic.rootDatum n F).rootGroup β)
    (u : ↥(StatedSp n F)) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(StatedSp n F))
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  haveI : Finite ↥(StatedSp n F) := by
    haveI : Fintype F := Fintype.ofFinite F
    infer_instance
  obtain ⟨hhN', hfix'⟩ := l10ss2_fpf_map (MulAut.conj u) hhN hfix
  refine noCentral_of_fixedPoint (X := ↥(StatedSp n F)) (K := ⊤)
    (R := (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom))
    (r := 3) (h := (MulAut.conj u) h) Nat.prime_three (by decide) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]; exact hord
  · exact ⟨Subgroup.mem_top _, hhN'⟩
  · intro y hy hcomm
    exact hfix' y (by simpa only [top_inf_eq] using hy) hcomm

theorem ggRootNoCentral_sp {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hn : 2 ≤ n)
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (u : ↥(StatedSp n F)) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(StatedSp n F))
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  by_cases hl : GGLongRoot (Symplectic.rootDatum n F) β
  · obtain ⟨h, hhN, hord, hfix⟩ := l10ss2_fpf_long hn hβ hl
    exact l10ss2_noCentral hhN hord hfix u
  · obtain ⟨h, hhN, hord, hfix⟩ := l10ss2_fpf_short hβ hl
    exact l10ss2_noCentral hhN hord hfix u

end CFSG.StandardType.LieKnownR2.PSp
