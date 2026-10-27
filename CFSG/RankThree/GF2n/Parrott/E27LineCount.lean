module

public import CFSG.RankThree.GF2n.Parrott.FixDimIII
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge
public import CFSG.RankThree.GF2n.Parrott.SpinE27Fixed
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.FixedFreeThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LinearAlgebra.F2Cube (fixedCount fixedDim FixedFreeRep)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem qH_sigma1Nine_eq_spinE27a : qH D (sigma1Nine (z := z) D) = spinE27a :=
  (qH_sigma1Nine (z := z) D).trans (Subtype.ext spinE27a_coe.symm)

omit [Finite G] in
theorem qH_eq_spinE27b {σ₂ : ↥(H z)}
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    qH (z := z) D σ₂ = spinE27b :=
  hq₂.trans (Subtype.ext spinE27b_coe.symm)

theorem fixedCount_actionQA45_qH (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    fixedCount ((actionQA45 (z := z) h D (qH D x) : GL8) : Mat8) = 2 ^ fixDimV h x :=
  (card_autFixedSubgroup_conjV_eq_fixCard D h x).symm.trans (card_fix h x)

theorem fixedDim_actionQA45_qH (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    fixedDim ((actionQA45 (z := z) h D (qH D x) : GL8) : Mat8) = fixDimV h x := by
  unfold fixedDim
  rw [fixedCount_actionQA45_qH, Nat.log_pow (by norm_num)]

theorem eq_zero_of_actionQA45_fixed (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    {w : Fin 8 → ZMod 2}
    (h₁ : ((actionQA45 (z := z) h D (qH D (sigma1Nine (z := z) D)) : GL8) : Mat8).mulVec w = w)
    (h₂ : ((actionQA45 (z := z) h D (qH D σ₂) : GL8) : Mat8).mulVec w = w) : w = 0 := by
  let : CommGroup (QuotientV.V z) := commGroupV h
  let : Module (ZMod 2) (Additive (QuotientV.V z)) := moduleV h
  have hbot := invariants_zpowers_sup_eq_bot_of_not_equalityBranch (z := z) D h hIII hσ₂ hq₂ hc₂
  rw [CFSG.SolvableHall.invariants_comp_subtype_sup, invariants_zpowers_eq_fixSubmodule,
    invariants_zpowers_eq_fixSubmodule] at hbot
  let v : QuotientV.V z := (mulEquivV h).symm (Multiplicative.ofAdd w)
  have hvw : Multiplicative.toAdd (mulEquivV h v) = w := by simp [v]
  have hfix : ∀ x : ↥(H z),
      ((actionQA45 (z := z) h D (qH D x) : GL8) : Mat8).mulVec w = w → conjV h x v = v := by
    intro x hx
    rw [actionQA45_qH D h x] at hx
    have h3 := mulVec_mulAutVEquivGL h (conjV h x) v
    rw [hvw, hx] at h3
    apply (mulEquivV h).injective
    apply Multiplicative.toAdd.injective
    rw [← h3, hvw]
  have hmem : Additive.ofMul v ∈
      fixSubmodule h (sigma1Nine (z := z) D) ⊓ fixSubmodule h σ₂ := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_fixSubmodule_iff]
      exact mem_autFixedSubgroup.2 (hfix _ h₁)
    · rw [mem_fixSubmodule_iff]
      exact mem_autFixedSubgroup.2 (hfix _ h₂)
  rw [hbot, Submodule.mem_bot] at hmem
  have hv1 : v = 1 := hmem
  rw [← hvw, hv1, map_one]
  rfl

theorem actionQA45_spinE27_eq_zero_of_fixed (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    ∀ v : Fin 8 → ZMod 2,
      (∀ t, ((actionQA45 (z := z) h D (spinE27Elt t) : GL8) : Mat8).mulVec v = v) → v = 0 := by
  intro v hv
  refine eq_zero_of_actionQA45_fixed D h hIII hσ₂ hq₂ hc₂ ?_ ?_
  · rw [qH_sigma1Nine_eq_spinE27a, ← spinE27Elt_one_zero_zero]
    exact hv _
  · rw [qH_eq_spinE27b D hq₂, ← spinE27Elt_zero_one_zero]
    exact hv _

theorem e27LineCountData_of_not_equalityBranch (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    E27LineCountData (z := z) (D := D) h σ₂ := by
  have hρ := actionQA45_spinE27_eq_zero_of_fixed D h hIII hσ₂ hq₂ hc₂
  have hsum := (spinE27FixedFreeRep (actionQA45 (z := z) h D) hρ).sum_fixedDim
  have hcls := sum_fixedDim_spinE27 (actionQA45 (z := z) h D)
  have e1 : fixedDim ((actionQA45 (z := z) h D spinE27a : GL8) : Mat8) = 2 := by
    rw [← qH_sigma1Nine_eq_spinE27a D, fixedDim_actionQA45_qH, fixDimV_sigma1Nine]
  have e2 : fixedDim ((actionQA45 (z := z) h D (spinE27a * spinE27b) : GL8) : Mat8) =
      fixDimV h (sigma1Nine (z := z) D * σ₂) := by
    have h' := fixedDim_actionQA45_qH D h (sigma1Nine (z := z) D * σ₂)
    rw [map_mul, qH_sigma1Nine_eq_spinE27a, qH_eq_spinE27b D hq₂] at h'
    exact h'
  have e3 : fixedDim ((actionQA45 (z := z) h D (spinE27a * spinE27b⁻¹) : GL8) : Mat8) =
      fixDimV h (sigma1Nine (z := z) D * σ₂⁻¹) := by
    have h' := fixedDim_actionQA45_qH D h (sigma1Nine (z := z) D * σ₂⁻¹)
    rw [map_mul, map_inv, qH_sigma1Nine_eq_spinE27a, qH_eq_spinE27b D hq₂] at h'
    exact h'
  rw [e1, e2, e3] at hcls
  have h64 := hcls.symm.trans hsum
  unfold E27LineCountData
  omega

end CFSG.RankThree.GF2n.Parrott
