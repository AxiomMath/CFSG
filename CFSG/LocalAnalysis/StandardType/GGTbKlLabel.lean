module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2L4
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalType
import CFSG.RankThree.PartOne.S15K.OrthMult
import CFSG.RankThree.PartOne.K159.RowFourFixed
import CFSG.LocalAnalysis.GLTheoremA.CatA.I112DiagL2
import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TableL2
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.GroupTheory.WeirSylow


private def tbkls3_projPlane (i : Fin 3) :
    ModelSpace (ZMod 2) →ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun x := x.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem tbkls3_tor_ne_one {u : Fin 3 → ZMod 3} (hu : Two.weight u = 1) :
    Two.tor u ≠ 1 := by
  intro h
  have h1 : Multiplicative.ofAdd u = 1 :=
    cm_injective (K := ZMod 2) (by
      show cm (ZMod 2) (Multiplicative.ofAdd u) = cm (ZMod 2) 1
      rw [show cm (ZMod 2) (Multiplicative.ofAdd u) = 1 from h, map_one])
  have h0 : u = 0 := by
    simpa using congrArg Multiplicative.toAdd h1
  rw [h0] at hu
  simp [Two.weight] at hu

private theorem tbkls3_hx {u : Fin 3 → ZMod 3} (hu : Two.weight u = 1) :
    OddOrderIsometry (modelForm (1 : ZMod 2) 1) 3 (Two.tor u) := by
  have h3 : (3 : ZMod 2) ≠ 0 := by decide +kernel
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
  have hQ : (QuadraticMap.polarBilin (modelForm (1 : ZMod 2) 1)).Nondegenerate :=
    nondegenerate_polarBilin_modelForm h3 hbc
  have hxO : Two.tor u ∈ TauCeti.QuadraticMap.orthogonalGroup (modelForm (1 : ZMod 2) 1) :=
    cm_mem_modelO (1 : ZMod 2) 1 (Multiplicative.ofAdd u)
  refine CFSG.RankThree.PartOne.S15K.oddOrderIsometry_of_order hQ Nat.prime_three
    (by rw [ringChar.eq (ZMod 2) 2]; norm_num) hxO ?_
  have h3u : u + u + u = 0 := by
    funext i
    have h3z : (3 : ZMod 3) = 0 := by decide
    calc u i + u i + u i = 3 * u i := by ring
      _ = 0 := by rw [h3z, zero_mul]
  have hpow : (Two.tor u) ^ 3 = 1 := by
    change (cmEquiv (ZMod 2) u) ^ 3 = 1
    rw [pow_succ, pow_succ, pow_one, ← cmEquiv_add, ← cmEquiv_add, h3u, cmEquiv_zero]
  have hne : Two.tor u ≠ 1 := tbkls3_tor_ne_one hu
  have hdvd : orderOf (Two.tor u) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

private theorem tbkls3_fixedSpace_eq {u : Fin 3 → ZMod 3} {i : Fin 3}
    (hi : u i ≠ 0) (huniq : ∀ j, u j ≠ 0 → j = i) :
    fixedSpace (Two.tor u) = LinearMap.ker (tbkls3_projPlane i) := by
  ext x
  rw [mem_fixedSpace, LinearMap.mem_ker]
  change cmEquiv (ZMod 2) u x = x ↔ tbkls3_projPlane i x = 0
  rw [cmEquiv_apply_eq_self_iff (K := ZMod 2) (by decide) u x]
  constructor
  · intro h
    show x.1 i = 0
    exact h i hi
  · intro h j hj
    show x.1 j = 0
    rw [huniq j hj]
    exact h

private theorem tbkls3_finrank_fixedSpace {u : Fin 3 → ZMod 3} (hu : Two.weight u = 1) :
    Module.finrank (ZMod 2) (fixedSpace (Two.tor u)) = 6 := by
  have hu' : (Finset.univ.filter (fun j => u j ≠ 0)).card = 1 := hu
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hu'
  have hmem : i ∈ Finset.univ.filter (fun j => u j ≠ 0) := by rw [hi]; simp
  have hi0 : u i ≠ 0 := by simpa using hmem
  have huniq : ∀ j, u j ≠ 0 → j = i := by
    intro j hj
    have hjmem : j ∈ Finset.univ.filter (fun j => u j ≠ 0) := by simpa using hj
    rw [hi] at hjmem
    simpa using hjmem
  rw [tbkls3_fixedSpace_eq hi0 huniq]
  have hfin := LinearMap.finrank_range_add_finrank_ker (tbkls3_projPlane i)
  have hrange : (tbkls3_projPlane i).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro p
    exact ⟨planeVec i p, by simp [tbkls3_projPlane, planeVec]⟩
  have htarget : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hmodel : Module.finrank (ZMod 2) (ModelSpace (ZMod 2)) = 8 := by
    rw [finrank_modelSpace]
  rw [hrange, finrank_top, htarget, hmodel] at hfin
  omega

private theorem tbkls3_isPlusType {u : Fin 3 → ZMod 3} (hu : Two.weight u = 1) :
    IsPlusType ((modelForm (1 : ZMod 2) 1).comp (fixedSpace (Two.tor u)).subtype) := by
  have hx := tbkls3_hx hu
  have h3 : (3 : ZMod 2) ≠ 0 := by decide +kernel
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
  have hnotplus : ¬ IsPlusType (modelForm (1 : ZMod 2) 1) := not_isPlusType_modelForm h3 hbc
  have hdim : Module.finrank (ZMod 2) (ModelSpace (ZMod 2)) = 8 := by
    rw [finrank_modelSpace]
  have hcard : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  have hpq : 3 ∣ Nat.card (ZMod 2) + 1 := by rw [hcard]
  rcases CFSG.RankThree.PartOne.K159.fixed_type hx Nat.prime_three (by decide) hpq hdim
      hnotplus (tbkls3_tor_ne_one hu) with h2 | ⟨h4, _⟩ | ⟨h6, hplus⟩
  · rw [tbkls3_finrank_fixedSpace hu] at h2; omega
  · rw [tbkls3_finrank_fixedSpace hu] at h4; omega
  · exact hplus

private theorem tbkls3_isometry {u : Fin 3 → ZMod 3} (hu : Two.weight u = 1) :
    Nonempty (((modelForm (1 : ZMod 2) 1).comp
      (fixedSpace (Two.tor u)).subtype).IsometryEquiv
        (CFSG.LieType.Universal.Spin.quadPlus 3 (ZMod 2))) :=
  CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus (K := ZMod 2) (n := 3)
    (tbkls3_hx hu).polarBilin_fixed_nondegenerate
    (by rw [tbkls3_finrank_fixedSpace hu]) (tbkls3_isPlusType hu)

private theorem tbkls3_ggHasLabel_alt8 {R : Type} [Group R]
    (e : R ≃* alternatingGroup (Fin 8)) : GGHasLabel ⟨.A, 3, 1⟩ R := by
  unfold GGHasLabel
  change CFSG.Assembly.LargeEvenRawDatum ⟨.A, 3, 1⟩
    (fun R' _ _ _ => Nonempty (R ≃* R'))
  rw [CFSG.LocalAnalysis.GLTheoremA.i112d_rawDatum_A_iff]
  obtain ⟨e8⟩ := nonempty_recipe_mulEquiv_alt8L4 (K := ZMod 2) (by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2)
  refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  · exact ⟨e.trans e8.symm⟩

theorem hasLabel_supportedFixedDerived_twoTor_of_weight_eq_one {u : Fin 3 → ZMod 3}
    (hu : Two.weight u = 1) :
    GGHasLabel ⟨.A, 3, 1⟩ (↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) ⧸
      Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u))) ∧
    Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) = ⊥ := by
  have hx := tbkls3_hx hu
  obtain ⟨iso⟩ := tbkls3_isometry hu
  let e2 := CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr iso
  let e3 := (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
    (CFSG.LieType.Universal.Spin.coe_quadPlus (n := 3) (K := ZMod 2))).symm
  let e4 :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8
  let eA8 : ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) ≃*
      alternatingGroup (Fin 8) :=
    (supportedFixedDerivedEquiv hx).trans (e2.trans (e3.trans e4))
  have hcenter : Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1)
      (Two.tor u)) = ⊥ := by
    have h1 : Subgroup.map (eA8 : ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1)
        (Two.tor u)) →* ↥(alternatingGroup (Fin 8)))
        (Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1)
          (Two.tor u))) = ⊥ := by
      rw [Subgroup.map_center_eq eA8,
        alternatingGroup.center_eq_bot (α := Fin 8) (by simp [Nat.card_eq_fintype_card])]
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := (eA8 : ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1)
        (Two.tor u)) →* ↥(alternatingGroup (Fin 8)))) eA8.injective).mp h1
  have hqiso : (↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u)) ⧸
      Subgroup.center ↥(supportedFixedDerived (modelForm (1 : ZMod 2) 1) (Two.tor u))) ≃*
      ↥(alternatingGroup (Fin 8)) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans eA8
  exact ⟨tbkls3_ggHasLabel_alt8 hqiso, hcenter⟩

end CFSG.StandardType

end
