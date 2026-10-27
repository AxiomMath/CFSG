module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBridge
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldType
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHBlocks
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUniBlock
import CFSG.LieType.SeitzGeneration.UnitaryNonCubeAlgebra
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.Subnormal
import CFSG.HardMathSupport.Curtis.UnitaryLevi.RankTwoTwistedA
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDual
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniTorusDiag
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.HardMathSupport.Curtis.UnitaryLevi.CoverTransportE
import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftedData
import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlockCommute
import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitPlane
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryDiag
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryFamily
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
import CFSG.RankThree.PartOne.Census3.Assembly
import CFSG.RankThree.PartOne.FOC.Assemble
import CFSG.RankThree.PartOne.FOC.CentralQuot
import CFSG.RankThree.PartOne.FOC.ListBridge
import CFSG.RankThree.PartOne.FOC.PSUModel
import CFSG.RankThree.PartOne.S11d.LayerDecomp
import CFSG.RankThree.PartTwo.Census.Spin.Main
import Certificates.Certificate8153
import Certificates.Certificate8156
import Certificates.Certificate8157
import Certificates.Certificate8160
import Certificates.Certificate8171

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section UniNonCubeCompHelpers

open Matrix Module Polynomial
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open scoped commutatorElement

private noncomputable def uniNCComp_quotientCenterMulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)

private noncomputable def uniNCComp_quotientCenterMapEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) :
    (K.map e.toMonoidHom) ⧸ Subgroup.center (K.map e.toMonoidHom) ≃* K ⧸ Subgroup.center K :=
  uniNCComp_quotientCenterMulEquiv (e.subgroupMap K).symm

private theorem uniNCComp_nonempty_quotient_center_equiv_of_surjective
    {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (φ : G →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) :
    Nonempty (G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H) := by
  let ψ : G →* H ⧸ Subgroup.center H := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hkerψ : ψ.ker = Subgroup.center G := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
      have hxH : φ x ∈ Subgroup.center H := by
        change (QuotientGroup.mk (φ x) : H ⧸ Subgroup.center H) = 1 at hx1
        exact (QuotientGroup.eq_one_iff (φ x)).mp hx1
      have hmem : ∀ y : G, ⁅x, y⁆ ∈ Subgroup.center G := by
        intro y
        apply hker
        rw [MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_center_iff.mp hxH) (φ y)).symm
      have hZ2 : Subgroup.upperCentralSeries G 2 = Subgroup.center G := by
        rw [show (2 : ℕ) = 1 + 1 from rfl,
          ← Subgroup.comap_upperCentralSeries_quotient_center (G := G) 1,
          Subgroup.upperCentralSeries_one, Group.IsPerfect.center_quotient_center_eq_bot,
          MonoidHom.comap_bot, QuotientGroup.ker_mk']
      have hxZ2 : x ∈ Subgroup.upperCentralSeries G 2 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff,
          Subgroup.upperCentralSeries_one]
        exact hmem
      rwa [hZ2] at hxZ2
    · intro x hx
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk (φ x) : H ⧸ Subgroup.center H) = 1
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.map_center_le_center hφ (Subgroup.mem_map_of_mem φ hx)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

private theorem uniNCComp_isPerfectSL (m : ℕ) (E : Type) [Field E] (hm : 2 ≤ m)
    (hmE : m = 2 → 4 ≤ Nat.card E) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) E) := by
  rcases lt_or_eq_of_le hm with h3 | h2
  · exact CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  · subst m
    have hcard : 4 ≤ Nat.card E := hmE rfl
    haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
    letI : Fintype E := Fintype.ofFinite E
    have h4 : ∃ s : Finset E, s.card = 4 := by
      have h : 4 ≤ (Finset.univ : Finset E).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hcard
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h
      exact ⟨t, ht⟩
    exact CFSG.LinearGroups.special_linear_isPerfect le_rfl (Or.inr h4)

private theorem uniNCComp_nonempty_SL_centerQuot_equiv_PSLg (m : ℕ) (E : Type) [Field E] :
    Nonempty (Matrix.SpecialLinearGroup (Fin m) E ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) ≃* PSLg m E) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center (n := m) (K := E)).symm).trans
    (CFSG.StandardType.TypeA.recipeEquiv m E).symm⟩

private theorem uniNCComp_nonempty_statedSU_centerQuot_equiv_PSUg {E : Type} [Field E] [Finite E]
    {f m : ℕ} (hcard : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (hne : (m, 2 ^ f) ≠ (3, 2)) :
    Nonempty (StatedSU m (2 ^ f) E ⧸ Subgroup.center (StatedSU m (2 ^ f) E) ≃*
      PSUg m E (2 ^ f)) := by
  have hcenter := CFSG.HardMathSupport.Curtis.UnitaryLevi.center_statedSU_eq_scalars_of_ne
    (K := E) (f := f) hcard hm hne
  change Nonempty (StatedSU m (2 ^ f) E ⧸ Subgroup.center (StatedSU m (2 ^ f) E) ≃*
    StatedSU m (2 ^ f) E ⧸ (StatedScalars (Fin m) E).subgroupOf (StatedSU m (2 ^ f) E))
  exact ⟨QuotientGroup.quotientMulEquivOfEq hcenter⟩

end UniNonCubeCompHelpers

section Main

open Matrix Module Polynomial
open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem uniR_noncube_comp {K : Type} [Field K] [Finite K] [CharP K 2] {q N : ℕ} (hK : Nat.card K = q ^ 2)
    (hq3 : 3 ∣ q + 1) (hN : 4 ≤ N)
    {Ā : Subgroup (MulAut (PSUg N K q))} {δ' : MulAut (PSUg N K q)}
    {J' : Subgroup (PSUg N K q)} (hR : RDatum Ā δ' J') {d : GL (Fin N) K}
    (hd : IsHermIsometry q (d : Matrix (Fin N) (Fin N) K)) {c : Kˣ}
    (hdc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c) (hc : c ^ (q + 1) = 1)
    (hnc : ∀ s : Kˣ, s ^ (q + 1) = 1 → s ^ 3 ≠ c) (hδ : IsConjBy d δ') :
    (N = 6 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 3 ∧
        Nonempty (J' ⧸ Subgroup.center J' ≃* PSLg 2 F)) ∨
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), Nat.card E = (q ^ 3) ^ 2 ∧ 3 ≤ m ∧ N = 3 * m ∧
        Nonempty (J' ⧸ Subgroup.center J' ≃* PSUg m E (q ^ 3)) := by
  classical
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst q
  have h : UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  have hn1 : 1 ≤ N := by omega
  have hdU : d ∈ primeFormUnitary h (idGram K N) := uni_cube_mem_primeFormUnitary h rfl hd
  let A : primeFormUnitary h (idGram K N) := ⟨d, hdU⟩
  have hA3 : (A : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c := hdc
  let e : PSUg N K (2 ^ f) ≃* primeFormP h (idGram K N) :=
    CFSG.StandardType.InndiagSU.projEquiv h hn1
  let T : Subgroup (primeFormP h (idGram K N)) := J'.map e.toMonoidHom
  have hfixmap : (ggAutFixedSubgroup δ').map e.toMonoidHom =
      fixSubgroup (primeFormConjHom h (idGram K N) ⟨d, hdU⟩) := by
    ext y
    have h1 := Subgroup.mem_map_iff_mem (f := e.toMonoidHom)
      (K := ggAutFixedSubgroup δ') e.injective (x := e.symm y)
    change e (e.symm y) ∈ Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ') ↔
      e.symm y ∈ ggAutFixedSubgroup δ' at h1
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1, uni_cube_fixSubgroup_projEquiv h hn1 hδ hdU (e.symm y),
      MulEquiv.apply_symm_apply]
  have hT : CFSG.Open.IsComponentOf T (fixSubgroup (primeFormConjHom h (idGram K N) A)) := by
    have h1 := CFSG.StandardType.isComponentOf_map_mulEquiv' e hR.comp
    rw [show J'.map e.toMonoidHom = T from rfl] at h1
    rw [hfixmap] at h1
    exact CFSG.Assembly.isComponentOf_iff_open.mp h1
  have hnotcube : ∀ b : K, b ^ 3 ≠ (c : K) := by
    intro b hb
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at hb
      exact c.ne_zero (by simpa using hb.symm)
    have hnormc : h.bar (c : K) * (c : K) = 1 := by
      have h1 : ((c : K) ^ (2 ^ f + 1)) = 1 := by
        have h2 := congrArg Units.val hc
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
      rw [UnitaryFieldData.bar_apply, ← pow_succ]
      exact h1
    have hnormb : h.bar b * b = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.CanonU3.norm_eq_one_of_pow_three_eq h hq3 hb hnormc
    have hs1 : (Units.mk0 b hb0) ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      change b ^ (2 ^ f + 1) = (1 : K)
      rw [pow_succ, ← UnitaryFieldData.bar_apply]
      exact hnormb
    have hs3 : (Units.mk0 b hb0) ^ 3 = c := by
      apply Units.ext
      change b ^ 3 = (c : K)
      exact hb
    exact hnc (Units.mk0 b hb0) hs1 hs3
  obtain ⟨hdvd, -, -, hcases⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_fieldType_component
      Nat.prime_three h (by norm_num : (3 : ℕ) ≠ 2) A hA3 hnotcube hT
  rcases hcases with ⟨hm2, F, hF, hFt, hcardF, g, hgsurj, hgker⟩ |
      ⟨hm3, E, hE, hEt, hcardE, g, hgsurj, hgker⟩
  ·
    letI : Field F := hF
    letI : Fintype F := hFt
    have hN6 : N = 6 := by
      have h3 := Nat.mul_div_cancel' hdvd
      omega
    have h4 : 4 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card, hcardF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      uniNCComp_isPerfectSL 2 F le_rfl (fun _ => h4)
    have eJS : J' ⧸ Subgroup.center J' ≃* T ⧸ Subgroup.center T :=
      (uniNCComp_quotientCenterMapEquiv e J').symm
    obtain ⟨eST⟩ := uniNCComp_nonempty_quotient_center_equiv_of_surjective g hgsurj hgker
    obtain ⟨eSL⟩ := uniNCComp_nonempty_SL_centerQuot_equiv_PSLg 2 F
    left
    refine ⟨hN6, F, inferInstance, inferInstance, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card, hcardF, pow_mul]
    · exact ⟨(eJS.trans eST.symm).trans eSL⟩
  ·
    letI : Field E := hE
    letI : Fintype E := hEt
    have hcardE' : Nat.card E = ((2 ^ f) ^ 3) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hcardE, pow_mul]
    have hcardE'' : Nat.card E = (2 ^ (f * 3)) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hcardE]
    have hN3m : N = 3 * (N / 3) := (Nat.mul_div_cancel' hdvd).symm
    have h2ne : (2 : ℕ) ^ (f * 3) ≠ 2 := by
      intro heq
      have hle : 2 ^ 3 ≤ 2 ^ (f * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [heq] at hle
      norm_num at hle
    have hne : (N / 3, 2 ^ (f * 3)) ≠ (3, 2) := fun hc => h2ne (congrArg Prod.snd hc)
    haveI : Group.IsPerfect (StatedSU (N / 3) (2 ^ (f * 3)) E) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := E) hcardE'' hm3 hne
    have eJS : J' ⧸ Subgroup.center J' ≃* T ⧸ Subgroup.center T :=
      (uniNCComp_quotientCenterMapEquiv e J').symm
    obtain ⟨eST⟩ := uniNCComp_nonempty_quotient_center_equiv_of_surjective g hgsurj hgker
    obtain ⟨eSU⟩ := uniNCComp_nonempty_statedSU_centerQuot_equiv_PSUg (E := E) (f := f * 3) (m := N / 3)
      hcardE'' hm3 hne
    right
    refine ⟨E, inferInstance, inferInstance, N / 3, hcardE', hm3, hN3m, ?_⟩
    refine ⟨?_⟩
    rw [← pow_mul]
    exact (eJS.trans eST.symm).trans eSU

end Main

end CFSG.StandardType.TablePThreeKG

end
