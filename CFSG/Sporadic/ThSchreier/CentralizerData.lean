
module

public import CFSG.Sporadic.ThSchreier.CentralizerDataBase

public import CFSG.Sporadic.ThSchreier.GlobalData
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public import Certificates.Certificate2309
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def planeUA : Submodule (ZMod 2) RowV where
  carrier := {w | ∃ r : RowV, w = toRow (Matrix.vecMul (ofRow r) (toMat a - 1))}
  add_mem' := by
    rintro _ _ ⟨r, rfl⟩ ⟨s, rfl⟩
    exact ⟨r + s, (Matrix.add_vecMul _ (ofRow r) (ofRow s)).symm⟩
  zero_mem' := ⟨0, (Matrix.zero_vecMul _).symm⟩
  smul_mem' := by
    rintro c _ ⟨r, rfl⟩
    exact ⟨c • r, (Matrix.smul_vecMul c (ofRow r) _).symm⟩

@[expose] noncomputable def planeY : Set (Set RowV) := {P | P ∈ planeX ∧ P ⊆ (planeUA : Set RowV)}

@[expose] noncomputable def transporterV : J := wordG (pairLetters a b) transporterWord

@[expose] noncomputable def planeStar : Set RowV := transporterV • planeWSet

@[expose] noncomputable def involT : J := transporterV⁻¹ * a * transporterV

private theorem native_cent_lists :
    centFixedIdx.length = 10200 ∧ centImageIdx.length = 120 ∧ centImageRows.length = 240 ∧
    (∀ n ∈ centImageRows, n < 2 ^ 248) ∧ centOrbitPar.length = 819 ∧
    centOrbitLab.length = 819 ∧ centOrbitEdges.length = 1638 :=
  Certificates.certificate2309

theorem ctuc_Th_centralizer_plane_data :
    planeY ⊆ planeX ∧ (∀ l ∈ transporterWord, l = 1 ∨ l = 2) ∧ planeStar ∈ planeX ∧
    planeStar = transporterV • planeWSet ∧ involT = transporterV⁻¹ * a * transporterV ∧
    centFixedIdx.length = 10200 ∧ centImageIdx.length = 120 ∧ centImageRows.length = 240 ∧
    (∀ n ∈ centImageRows, n < 2 ^ 248) ∧ centOrbitPar.length = 819 ∧
    centOrbitLab.length = 819 ∧ centOrbitEdges.length = 1638 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := native_cent_lists
  exact ⟨fun P hP => hP.1, by decide, ⟨transporterV, rfl⟩, rfl, rfl, h1, h2, h3, h4, h5, h6, h7⟩

end CFSG.Sporadic.ThSchreier
