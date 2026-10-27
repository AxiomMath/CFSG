module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectBase
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel OddLieType)
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)
open scoped commutatorElement

private def w183b5_piFinSuccMulEquiv (L : Type) [Group L] (m : ℕ) :
    (Fin (m + 1) → L) ≃* L × (Fin m → L) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by simp
  map_mul' _ _ := rfl

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

namespace NoPsp45Factor

theorem prod {A B : Type} [Group A] [Group B] (hA : NoPsp45Factor A)
    (hB : NoPsp45Factor B) : NoPsp45Factor (A × B) :=
  of_normal (MonoidHom.fst A B).ker (of_mulEquiv (w183b5_kerFstMulEquiv A B).symm hB)
    (of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst A B)
      fun a => ⟨(a, 1), rfl⟩).symm hA)

theorem pi_fin {L : Type} [Group L] (hL : NoPsp45Factor L) (hO : LieOrderFormulasInput)
    (m : ℕ) : NoPsp45Factor (Fin m → L) := by
  induction m with
  | zero => exact of_commute hO fun a b => Subsingleton.elim _ _
  | succ m ih => exact of_mulEquiv (w183b5_piFinSuccMulEquiv L m).symm (hL.prod ih)

end NoPsp45Factor

private theorem w183b5_noPsp45Factor_perm (hO : LieOrderFormulasInput) (n : ℕ) :
    NoPsp45Factor (Equiv.Perm (Fin n)) := by
  by_cases hn : n ≤ 6
  · refine NoPsp45Factor.of_not_dvd fun T _ hT hd => ?_
    have h720 : Nat.card (Equiv.Perm (Fin n)) ∣ 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact (Nat.factorial_dvd_factorial hn : Nat.factorial n ∣ Nat.factorial 6)
    exact (hT.card_facts hO).2.1 (hd.trans h720)
  · have h7 : 7 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    refine NoPsp45Factor.of_index_two hO (alternatingGroup (Fin n))
      alternatingGroup.index_eq_two ?_
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    obtain ⟨t, m, p, f, hp, hp2, hadm, hY⟩ := hT.oddLieType
    have hodd : CFSG.Blueprint.OddLieType (alternatingGroup (Fin n)) :=
      ⟨t, m, p, f, hp, hp2, hadm, hY.of_mulEquiv e.symm⟩
    rcases (by omega : n = 7 ∨ n = 8 ∨ 9 ≤ n) with rfl | rfl | h9
    · exact CFSG.ComponentClassification.CatFC.not_oddLieType_alt7 hO hodd
    · have : Nat.card T = 20160 := by
        rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      exact (hT.card_facts hO).2.2.1 this
    · exact CFSG.OddStandard.AltStdSec.not_oddLieType_alt hO h9 hodd

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

private theorem w183b5_noPsp45Factor_pi_sl2 (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (m : ℕ) :
    NoPsp45Factor (Fin m → Matrix.SpecialLinearGroup (Fin 2) F) :=
  (w183b5_noPsp45Factor_sl2 hO hF).pi_fin hO m

private theorem w183b5_noPsp45Factor_wreathSym (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (m : ℕ) :
    NoPsp45Factor (WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m) := by
  refine NoPsp45Factor.of_normal
    (SemidirectProduct.rightHom : WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m →*
      Equiv.Perm (Fin m)).ker ?_ ?_
  · exact NoPsp45Factor.of_mulEquiv
      ((MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
        (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom))
      (w183b5_noPsp45Factor_pi_sl2 hO hF m)
  · exact NoPsp45Factor.of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective SemidirectProduct.rightHom
        SemidirectProduct.rightHom_surjective).symm (w183b5_noPsp45Factor_perm hO m)

theorem noPsp45Factor_of_isL2WrSymGp (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] {n m : ℕ} (h : IsL2WrSymGp Y n m) :
    NoPsp45Factor Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact (w183b5_noPsp45Factor_wreathSym hO hF m).of_mulEquiv e.symm

private theorem w183b5_noPsp45Factor_statedOmega_quadMinus_three_of_card_eq_three
    (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(StatedOmega (StatedQuadMinus 3 F b c)) := by
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 F hbc
  have hdim : Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) = 6 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hno : ¬ ∃ T : Submodule F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F),
      Module.finrank F T = 3 ∧ ∀ x ∈ T, quadMinus 3 F b c x = 0 := by
    rintro ⟨T, hT, hTQ⟩
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by norm_num) hbc
      ⟨T, by omega, hTQ⟩
  obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd (quadMinus 3 F b c)
      hQ hdim hno
  have hM : CFSG.IsComponent
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c))) :=
    ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩
  have hmodel :=
    (CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_six
      (p := 3) (e := 1) Nat.prime_three (by norm_num) le_rfl (by rw [hF]; norm_num)
      (quadMinus 3 F b c) hQ hdim hno hM).2
  have hcard : Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 3 F b c))) ⧸ Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (quadMinus 3 F b c)))) = 3265920 := by
    have h := CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1) (by norm_num)
      (by norm_num) hmodel
    rw [show CFSG.Open.ordTwistedA (4 - 1) (3 ^ 1) = 3265920 by decide] at h
    exact h
  let e := statedOmegaEquivCommutator (coe_quadMinus 3 F b c)
  haveI : Finite ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c))) :=
    Finite.of_equiv _ e.toEquiv
  haveI := hq.2.1
  refine NoPsp45Factor.of_mulEquiv e.symm (NoPsp45Factor.of_normal _
    (NoPsp45Factor.of_commute hO fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1))
    (NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun eT => ?_⟩))
  have hT3 : Nat.card T = 3265920 := by
    rw [← Nat.card_congr eT.toEquiv, hcard]
  exact (hT.card_facts hO).2.2.2.2 hT3

private theorem w183b5_noPsp45Factor_projOmegaMinus_two_of_card_eq_three
    (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoPsp45Factor ↥(CFSG.PGLModel.projOmegaMinus 2 F b c) :=
  NoPsp45Factor.of_surjective
    ((Matrix.ProjGenLinGroup.mk : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F →* _).subgroupMap
      (StatedOmega (StatedQuadMinus 3 F b c)))
    (MonoidHom.subgroupMap_surjective _ _)
    (w183b5_noPsp45Factor_statedOmega_quadMinus_three_of_card_eq_three hO hF hbc)

theorem noPsp45Factor_of_isOrth6MinusMod (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] (h : IsOrth6MinusMod Y) :
    NoPsp45Factor Y := by
  obtain ⟨F, _, _, hF3, b, c, hbc, N, hPN, hNO, ⟨e⟩⟩ := h
  refine NoPsp45Factor.of_mulEquiv e.symm ?_
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := inferInstance
  have hkey : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ CFSG.PGLModel.projOmegaMinus 2 F b c := by
    intro x hx y hy
    obtain ⟨g, hg, rfl⟩ := hNO hx
    obtain ⟨h, hh, rfl⟩ := hNO hy
    rw [← map_commutatorElement Matrix.ProjGenLinGroup.mk]
    exact Subgroup.mem_map_of_mem _ (Subgroup.commutator_mem_commutator hg hh)
  haveI : ((CFSG.PGLModel.projOmegaMinus 2 F b c).subgroupOf N).Normal := by
    refine ⟨fun a ha n => ?_⟩
    have h1 : ⁅(n : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F),
        (a : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F)⁆ ∈
        CFSG.PGLModel.projOmegaMinus 2 F b c := hkey n n.2 a a.2
    have h2 : (a : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) ∈
        CFSG.PGLModel.projOmegaMinus 2 F b c := ha
    have h3 := mul_mem h1 h2
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def, mul_assoc] using h3
  refine NoPsp45Factor.of_normal ((CFSG.PGLModel.projOmegaMinus 2 F b c).subgroupOf N) ?_ ?_
  · exact NoPsp45Factor.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPN).symm
      (w183b5_noPsp45Factor_projOmegaMinus_two_of_card_eq_three hO hF3 hbc)
  · refine NoPsp45Factor.of_commute hO fun a b => ?_
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have := hkey ((b⁻¹ : N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) (b⁻¹ : N).2
      ((a⁻¹ : N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) (a⁻¹ : N).2
    simpa [commutatorElement_def, mul_assoc] using this

end CFSG.LocalAnalysis.WeakClosure81

end
