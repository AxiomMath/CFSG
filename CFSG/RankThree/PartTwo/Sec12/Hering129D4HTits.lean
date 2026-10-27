module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HWeyl
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenF4QPlus CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Nw

variable (Ω : Type) [Field Ω]

@[expose] noncomputable def nw (ω : List (Fin TwistTag.D4.tag.rank)) :
    ModGL TwistTag.D4.tag Ω :=
  (ω.map fun i => weylElt TwistTag.D4.tag Ω i 1).prod

variable {Ω}

theorem nw_nil : nw Ω [] = 1 := rfl

theorem nw_cons (i : Fin TwistTag.D4.tag.rank) (ω : List (Fin TwistTag.D4.tag.rank)) :
    nw Ω (i :: ω) = weylElt TwistTag.D4.tag Ω i 1 * nw Ω ω := by
  simp [nw]

theorem nw_append (ω ω' : List (Fin TwistTag.D4.tag.rank)) :
    nw Ω (ω ++ ω') = nw Ω ω * nw Ω ω' := by
  simp [nw]

theorem nw_mem_adjointGroup (ω : List (Fin TwistTag.D4.tag.rank)) :
    nw Ω ω ∈ adjointGroup TwistTag.D4.tag Ω := by
  induction ω with
  | nil => exact one_mem _
  | cons i ω ih =>
    rw [nw_cons]
    exact mul_mem (weylElt_mem_adjointGroup i 1) ih

theorem nw_eq_canonicalRep [CharP Ω 2] (ω : List (Fin TwistTag.D4.tag.rank)) :
    nw Ω ω = canonicalRep (coxeterSystem TwistTag.D4.tag) Ω
      ((coxeterSystem TwistTag.D4.tag).wordProd ω) :=
  (canonicalRep_wordProd_of_charTwo (τ := TwistTag.D4.tag) (M := Ω) ω).symm

theorem nw_inv [CharP Ω 2] (ω : List (Fin TwistTag.D4.tag.rank)) :
    (nw Ω ω)⁻¹ = nw Ω ω.reverse := by
  rw [nw_eq_canonicalRep, nw_eq_canonicalRep, canonicalRep_inv_of_charTwo,
    CoxeterSystem.wordProd_reverse]

theorem weylElt_one_inv [CharP Ω 2] (i : Fin TwistTag.D4.tag.rank) :
    (weylElt TwistTag.D4.tag Ω i 1)⁻¹ = weylElt TwistTag.D4.tag Ω i 1 := by
  rw [weylElt_inv]
  congr 1
  exact Units.ext (CharTwo.neg_eq (1 : Ω))

theorem diagramMap_conj_weylElt (i : Fin TwistTag.D4.tag.rank) :
    diagramMap TwistTag.D4 Ω * weylElt TwistTag.D4.tag Ω i 1 * (diagramMap TwistTag.D4 Ω)⁻¹ =
      weylElt TwistTag.D4.tag Ω (rhoL i) 1 := by
  rw [diagramMap_mul_weylElt_one]
  rw [mul_inv_cancel_right]
  rfl

theorem diagramMap_conj_nw (ω : List (Fin TwistTag.D4.tag.rank)) :
    diagramMap TwistTag.D4 Ω * nw Ω ω * (diagramMap TwistTag.D4 Ω)⁻¹ = nw Ω (ω.map rhoL) := by
  induction ω with
  | nil => simp [nw_nil]
  | cons i ω ih =>
    rw [List.map_cons, nw_cons, nw_cons, ← ih, ← diagramMap_conj_weylElt]
    group

theorem entrywise_weylElt_one (Fr : Ω →+* Ω) (i : Fin TwistTag.D4.tag.rank) :
    Units.map (entrywiseHom Fr) (weylElt TwistTag.D4.tag Ω i 1) =
      weylElt TwistTag.D4.tag Ω i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul,
    units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit]
  simp

theorem entrywise_nw (Fr : Ω →+* Ω) (ω : List (Fin TwistTag.D4.tag.rank)) :
    Units.map (entrywiseHom Fr) (nw Ω ω) = nw Ω ω := by
  induction ω with
  | nil => simp [nw_nil]
  | cons i ω ih => rw [nw_cons, map_mul, entrywise_weylElt_one, ih]

theorem trialityFrob_nw (Fr : Ω →+* Ω) (ω : List (Fin TwistTag.D4.tag.rank)) :
    trialityFrob Ω Fr (nw Ω ω) = nw Ω (ω.map rhoL) := by
  rw [trialityFrob_apply, entrywise_nw, diagramMap_conj_nw]

theorem trialityM_conj_nw [CharP Ω 2] (ω : List (Fin TwistTag.D4.tag.rank)) :
    trialityM Ω * nw Ω ω * (trialityM Ω)⁻¹ = nw Ω (deltaW ω) := by
  have h20 : nw Ω [2, 0] = weylElt TwistTag.D4.tag Ω 2 1 * weylElt TwistTag.D4.tag Ω 0 1 := by
    simp [nw]
  have h02 : nw Ω [0, 2] = weylElt TwistTag.D4.tag Ω 0 1 * weylElt TwistTag.D4.tag Ω 2 1 := by
    simp [nw]
  unfold deltaW
  rw [nw_append, nw_append, h20, h02, ← diagramMap_conj_nw]
  rw [trialityM, trialityTwistN, mul_inv_rev, mul_inv_rev, weylElt_one_inv, weylElt_one_inv]
  group

theorem trialityM_pow_conj_nw [CharP Ω 2] (k : ℕ) (ω : List (Fin TwistTag.D4.tag.rank)) :
    trialityM Ω ^ k * nw Ω ω * (trialityM Ω ^ k)⁻¹ = nw Ω (deltaW^[k] ω) := by
  induction k generalizing ω with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ← ih, ← trialityM_conj_nw, pow_succ, mul_inv_rev]
    group

theorem threeSixFrob_nw [CharP Ω 2] (Fr : Ω →+* Ω) (ε : ℤ)
    (ω : List (Fin TwistTag.D4.tag.rank)) :
    threeSixFrob Ω Fr ε (nw Ω ω) = nw Ω (deltaW^[threeSixExp ε] ω) := by
  rw [threeSixFrob_apply, trialityFrob_nw, ← trialityM_pow_conj_nw, threeSixN]
  have h : (diagramMap TwistTag.D4 Ω)⁻¹ * nw Ω (ω.map rhoL) * diagramMap TwistTag.D4 Ω =
      nw Ω ω := by
    rw [← diagramMap_conj_nw ω]
    group
  calc trialityM Ω ^ threeSixExp ε * (diagramMap TwistTag.D4 Ω)⁻¹ * nw Ω (ω.map rhoL) *
        (trialityM Ω ^ threeSixExp ε * (diagramMap TwistTag.D4 Ω)⁻¹)⁻¹
      = trialityM Ω ^ threeSixExp ε *
        ((diagramMap TwistTag.D4 Ω)⁻¹ * nw Ω (ω.map rhoL) * diagramMap TwistTag.D4 Ω) *
          (trialityM Ω ^ threeSixExp ε)⁻¹ := by group
    _ = _ := by rw [h]

theorem threeSixFrob_nw_eq [CharP Ω 2] (Fr : Ω →+* Ω) (ε : ℤ)
    (ω : List (Fin TwistTag.D4.tag.rank))
    (h : (coxeterSystem TwistTag.D4.tag).wordProd (deltaW^[threeSixExp ε] ω) =
      (coxeterSystem TwistTag.D4.tag).wordProd ω) :
    threeSixFrob Ω Fr ε (nw Ω ω) = nw Ω ω := by
  rw [threeSixFrob_nw, nw_eq_canonicalRep, nw_eq_canonicalRep ω, h]

theorem nw_conj_rootDiagUnit [CharP Ω 2] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (ω : List (Fin TwistTag.D4.tag.rank)) (β : Exp3) :
    nw Ω ω * rootDiagUnit TwistTag.D4.tag (tup ζ β) * (nw Ω ω)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (tup ζ (wordExp ω β)) := by
  have h := rootDiagUnit_tup_eq_conj (L := Ω) hζ ω β
  rw [nw_eq_canonicalRep, h]
  group

end Nw

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
