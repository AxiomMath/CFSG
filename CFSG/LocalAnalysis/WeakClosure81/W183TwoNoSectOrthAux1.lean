module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectBase
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthPlus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.RankThree.PartOne.K159.Klein
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)
open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open Matrix (SpecialLinearGroup)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open scoped commutatorElement

theorem w183b5_noPsp45Factor_of_statedProj (hO : LieOrderFormulasInput) {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] (H : Subgroup (GL ι K))
    (h : NoPsp45Factor (StatedProj H)) : NoPsp45Factor ↥H := by
  refine NoPsp45Factor.of_normal ((StatedScalars ι K).subgroupOf H)
    (NoPsp45Factor.of_commute hO fun a b => ?_) h
  have hc : StatedScalars ι K = Subgroup.center (GL ι K) := by
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have ha : a.1.1 ∈ Subgroup.center (GL ι K) := hc ▸ a.2
  exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp ha b.1.1).symm)

theorem w183b5_noPsp45Factor_of_lieModel_two (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    [IsSimpleGroup Y] {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hY : LieModel Y t n 2 f)
    (hne : ¬ ((t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1))) : NoPsp45Factor Y := by
  refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  obtain ⟨-, hM, -⟩ := hO Y t n 2 f hadm hY
  refine hne (hT.crossChar hO hadm ?_)
  rw [← Nat.card_congr e.toEquiv]
  exact hM

theorem w183b5_noPsp45Factor_orthogonalPlus_of_statedOmega (hO : LieOrderFormulasInput) (k : ℕ)
    {F : Type} [Field F] [Finite F] (h : NoPsp45Factor ↥(StatedOmega (StatedQuadPlus k F))) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalPlus k F) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin k ⊕ Fin k) F) := inferInstance
  exact NoPsp45Factor.of_commutator hO
    (h.of_mulEquiv (commutatorOrthogonalPlusEquiv k F).symm)

theorem w183b5_noPsp45Factor_orthogonalMinus_of_statedOmega (hO : LieOrderFormulasInput) (k : ℕ)
    {F : Type} [Field F] [Finite F] (b c : F)
    (h : NoPsp45Factor ↥(StatedOmega (StatedQuadMinus (k + 1) F b c))) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalMinus k F b c) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin k ⊕ Fin k ⊕ Fin 2) F) := inferInstance
  exact NoPsp45Factor.of_commutator hO
    (h.of_mulEquiv (commutatorOrthogonalMinusEquiv k F b c).symm)

private def w183b5_kerFstMulEquiv (A B : Type) [Group A] [Group B] :
    ↥(MonoidHom.fst A B).ker ≃* B where
  toFun x := x.1.2
  invFun b := ⟨(1, b), MonoidHom.mem_ker.mpr rfl⟩
  left_inv x := by
    obtain ⟨⟨a, b⟩, hx⟩ := x
    have ha : a = 1 := hx
    subst ha
    rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem w183b5_noPsp45Factor_prod {A B : Type} [Group A] [Group B]
    (hA : NoPsp45Factor A) (hB : NoPsp45Factor B) : NoPsp45Factor (A × B) :=
  NoPsp45Factor.of_normal (MonoidHom.fst A B).ker
    (NoPsp45Factor.of_mulEquiv (w183b5_kerFstMulEquiv A B).symm hB)
    (NoPsp45Factor.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst A B)
      fun a => ⟨(a, 1), rfl⟩).symm hA)

private theorem w183b5_noPsp45Factor_sl2 (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoPsp45Factor (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      lieOrderNumerator .PSL 2 (2 ^ n) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    rfl
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · refine NoPsp45Factor.of_not_dvd fun T _ hT hd => ?_
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [hcard]
      simp [lieOrderNumerator]
    rw [h6] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := (hT.card_facts hO).1
    omega
  · have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup h4
    refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    have hadm : StatedLieAdmissible .PSL 2 2 n :=
      ⟨Nat.prime_two, hn, le_rfl, fun h => by simp at h; omega,
        fun h => by simp at h; omega⟩
    have hM : Nat.card T * lieOrderDivisor .PSL 2 (2 ^ n) = lieOrderNumerator .PSL 2 (2 ^ n) := by
      rw [lieOrderDivisor_psl_two_two_pow hn, mul_one, ← Nat.card_congr e.toEquiv, hcard]
    rcases hT.crossChar hO hadm hM with ⟨-, -, h2⟩ | ⟨-, h3, -⟩ | ⟨h1, -⟩
    · subst h2
      have : Nat.card T = 60 := by
        rw [← Nat.card_congr e.toEquiv, hcard]
        simp [lieOrderNumerator]
      have := (hT.card_facts hO).1
      omega
    · omega
    · exact absurd h1 (by decide)

theorem w183b5_noPsp45Factor_orthogonalPlus_two (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalPlus 2 F) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hle : (OmegaPlusCell.jProd (F := F)).range ≤ orthGroup (StatedQuadPlus 2 F) := by
    rintro _ ⟨x, rfl⟩
    exact OmegaPlusCell.jProd_mem_orthGroup x
  show NoPsp45Factor ↥(orthGroup (StatedQuadPlus 2 F))
  refine NoPsp45Factor.of_index_two hO
    ((OmegaPlusCell.jProd (F := F)).range.subgroupOf (orthGroup (StatedQuadPlus 2 F)))
    OmegaPlusCell.relIndex_jProd_range ?_
  exact NoPsp45Factor.of_mulEquiv
    ((MonoidHom.ofInjective OmegaPlusCell.jProd_injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm)
    (w183b5_noPsp45Factor_prod (w183b5_noPsp45Factor_sl2 hO hF)
      (w183b5_noPsp45Factor_sl2 hO hF))

theorem w183b5_noPsp45Factor_statedOmega_quadPlus_three (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadPlus 3 F)) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨hnd, hts⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := 3) le_rfl
  obtain ⟨eK⟩ := kleinCommutatorOrthogonalSix (quadPlus 3 F) hnd (by simp) hts
  let E : ↥(StatedOmega (StatedQuadPlus 3 F)) ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    (statedOmegaEquivCommutator (coe_quadPlus 3 F)).trans
      (eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F).symm)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)).1
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 F)) := E.isSimpleGroup
  refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  have hadm : StatedLieAdmissible .PSL 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  have hM : Nat.card T * lieOrderDivisor .PSL 4 (2 ^ n) = lieOrderNumerator .PSL 4 (2 ^ n) := by
    rw [lieOrderDivisor_psl_four_two_pow hn, mul_one, ← Nat.card_congr e.toEquiv,
      Nat.card_congr E.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    rfl
  rcases hT.crossChar hO hadm hM with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
  · omega
  · omega
  · exact absurd h (by decide)

theorem w183b5_noPsp45Factor_orthogonalPlus_three (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoPsp45Factor ↥(CFSG.PGLModel.orthogonalPlus 3 F) :=
  w183b5_noPsp45Factor_orthogonalPlus_of_statedOmega hO 3
    (w183b5_noPsp45Factor_statedOmega_quadPlus_three hO hF)

end CFSG.LocalAnalysis.WeakClosure81

end
