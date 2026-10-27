
module

public import CFSG.Sporadic.ThSchreier.CentralCentralizerBase

public import CFSG.Sporadic.ThSchreier.PlaneStabilizerBase1
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase1
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem smul_mem_planeUA
    {c : J} (hc : c * a = a * c) {w : RowV} (hw : w ∈ planeUA) :
    c • w ∈ planeUA := by
  obtain ⟨r, rfl⟩ := hw
  refine ⟨toRow (Matrix.vecMul (ofRow r) (toMat c⁻¹)), ?_⟩
  have hc' : a * c⁻¹ = c⁻¹ * a := by
    calc a * c⁻¹ = c⁻¹ * (c * a) * c⁻¹ := by group
      _ = c⁻¹ * (a * c) * c⁻¹ := by rw [hc]
      _ = c⁻¹ * a := by group
  have hcomm : (toMat a - 1) * toMat c⁻¹ = toMat c⁻¹ * (toMat a - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, ← toMat_mul, ← toMat_mul,
      hc']
  rw [rowSmul_def]
  simp only [ofRow_toRow]
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hcomm]

theorem smul_subset_planeUA
    {c : J} (hc : c * a = a * c) {P : Set RowV}
    (hP : P ⊆ (planeUA : Set RowV)) : c • P ⊆ (planeUA : Set RowV) := by
  rintro _ ⟨w, hw, rfl⟩
  exact smul_mem_planeUA hc (hP hw)

theorem smul_mem_planeY
    {c : J} (hc : c * a = a * c) {P : Set RowV} (hP : P ∈ planeY) :
    c • P ∈ planeY := by
  obtain ⟨⟨g, rfl⟩, hsub⟩ := hP
  exact ⟨⟨c * g, mul_smul c g planeWSet⟩, smul_subset_planeUA hc hsub⟩

theorem conj_injective
    (g : J) : Function.Injective (MulAut.conj g).toMonoidHom := by
  intro x y h
  have h' : g * x * g⁻¹ = g * y * g⁻¹ := h
  simpa using h'

theorem centralizer_a_inf_conj :
    (Subgroup.centralizer {involT} ⊓ localH).map (MulAut.conj transporterV).toMonoidHom =
      Subgroup.centralizer {a} ⊓ localH.map (MulAut.conj transporterV).toMonoidHom := by
  have hvt : transporterV * involT * transporterV⁻¹ = a := by
    rw [involT]
    group
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨hx, hxH⟩, rfl⟩
    refine ⟨?_, x, hxH, rfl⟩
    rw [← hvt]
    calc transporterV * x * transporterV⁻¹ * (transporterV * involT * transporterV⁻¹) =
          transporterV * (x * involT) * transporterV⁻¹ := by group
      _ = transporterV * (involT * x) * transporterV⁻¹ := by rw [hx]
      _ = _ := by group
  · rintro ⟨hg, x, hxH, rfl⟩
    refine ⟨x, ⟨?_, hxH⟩, rfl⟩
    rw [← hvt] at hg
    calc x * involT = transporterV⁻¹ * (transporterV * x * transporterV⁻¹ *
          (transporterV * involT * transporterV⁻¹)) * transporterV := by group
      _ = transporterV⁻¹ * (transporterV * involT * transporterV⁻¹ *
          (transporterV * x * transporterV⁻¹)) * transporterV := by rw [hg]
      _ = involT * x := by group

section Facts

variable {c : ℕ} (hC : CertFacts c) (hS : ThScanFacts)
include hC hS

end Facts

end CFSG.Sporadic.ThSchreier
