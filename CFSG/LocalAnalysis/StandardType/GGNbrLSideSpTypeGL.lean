module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.Open.StatedDefs
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI

private theorem typeGL_isSolvable_gl_of_le_one {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1) :
    Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) E) := by
  refine Group.isSolvable_of_comm fun a b => Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact Matrix.ext fun i => i.elim0
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one,
      Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact mul_comm _ _

private theorem typeGL_range_eq_commutator_of_perfect {X B Ab : Type*} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

theorem GGNbrLSideKit.commutator_generalLinear_eq_statedSL {r : ℕ} {K : Type} [Field K] [Finite K]
    (hr : 2 ≤ r) (hcond : 3 ≤ r ∨ ∃ s : Finset K, s.card = 4) :
    commutator (Matrix.GeneralLinearGroup (Fin r) K) = StatedSL r K := by
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin r) K) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hr hcond
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin r) K) = ⊤ :=
    Group.isPerfect_def.mp hqSL.1
  let θ : Matrix.SpecialLinearGroup (Fin r) K →* Matrix.GeneralLinearGroup (Fin r) K :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (Matrix.GeneralLinearGroup (Fin r) K) := by
    refine typeGL_range_eq_commutator_of_perfect θ hperf
      (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin r) K →* Kˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin r) (Fin r) K).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  rw [← hθ, ← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]

private theorem typeGL_equiv_of_range {G X : Type} [Group G] [Group X] {A : Subgroup G}
    (ψ : X →* G) (hψ : Function.Injective ψ) (h : ψ.range = A) :
    Nonempty (↥A ≃* X) :=
  ⟨((Subgroup.equivMapOfInjective (⊤ : Subgroup X) ψ hψ).trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_top, h]))).symm.trans Subgroup.topEquiv⟩

theorem GGNbrLSideKit.lieModel_commutator_generalLinear {n r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hq : CFSG.IsQuasisimple ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K))) :
    CFSG.Blueprint.LieModel
      (↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) ⧸
        Subgroup.center ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K))) .PSL r 2 n := by
  classical
  haveI := Fintype.ofFinite K
  have hnotSolv : ¬ Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) := by
    intro hs
    haveI := hs
    haveI : Group.IsSolvable ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (commutator (Matrix.GeneralLinearGroup (Fin r) K)).subtype)
        Subtype.val_injective
    haveI : Group.IsPerfect ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) := hq.1
    haveI : Nontrivial ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isSolvable
      ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) inferInstance
  have hr2 : 2 ≤ r := by
    by_contra hlt
    haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin r) K) :=
      typeGL_isSolvable_gl_of_le_one (E := K) (by omega)
    exact hnotSolv inferInstance
  have hcond : 3 ≤ r ∨ ∃ t : Finset K, t.card = 4 := by
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · have hr : r = 2 := by omega
      subst hr
      right
      by_contra hno
      have hle : Nat.card K ≤ 3 := by
        by_contra hlt
        have h4 : 4 ≤ Nat.card K := by omega
        have h4' : 4 ≤ (Finset.univ : Finset K).card := by
          simpa [Nat.card_eq_fintype_card] using h4
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
        exact hno ⟨t, ht⟩
      have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
      have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
      haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K hcard
      exact hnotSolv inferInstance
    · exact Or.inl h3
  have hcomm : commutator (Matrix.GeneralLinearGroup (Fin r) K) = StatedSL r K :=
    GGNbrLSideKit.commutator_generalLinear_eq_statedSL hr2 hcond
  obtain ⟨eSL⟩ := typeGL_equiv_of_range (Matrix.SpecialLinearGroup.toGL)
    Matrix.SpecialLinearGroup.toGL_injective (CFSG.Open.StatedAPI.statedSL_eq_range_toGL r K).symm
  have e : ↥(commutator (Matrix.GeneralLinearGroup (Fin r) K)) ≃*
      Matrix.SpecialLinearGroup (Fin r) K :=
    (MulEquiv.subgroupCongr hcomm).trans eSL
  obtain ⟨eZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sl r e
  have hadm : StatedLieAdmissible .PSL r 2 n := by
    refine ⟨Nat.prime_two, hn, hr2, ?_, ?_⟩
    · intro h
      obtain ⟨hr, h2⟩ := Prod.mk.inj h
      have h4 : 4 ≤ Nat.card K := by
        rcases hcond with h3 | ⟨t, ht⟩
        · omega
        · have hle := Finset.card_le_univ t
          rw [ht] at hle
          simpa [Nat.card_eq_fintype_card] using hle
      rw [hK] at h4
      omega
    · intro h
      obtain ⟨-, h3⟩ := Prod.mk.inj h
      have hdvd : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      rw [h3] at hdvd
      norm_num at hdvd
  exact Or.inl ⟨by decide, ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eZ⟩⟩⟩

theorem ggNbrLSideSp_typeGL {n : ℕ} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {A : Subgroup G} {r : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (φ : ↥A ≃* GL (Fin r) K)
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆) :
    CFSG.Blueprint.LieModel (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) .PSL r 2 n := by
  have hqB : CFSG.IsQuasisimple ↥(commutator (GL (Fin r) K)) :=
    (GGNbrLSideKit.quasisimple_commutator_iff φ).1 hq
  exact GGNbrLSideKit.lieModel_quot_commutator_of_mulEquiv φ
    (GGNbrLSideKit.lieModel_commutator_generalLinear hK hn hqB)

end CFSG.StandardType
