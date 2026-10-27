module

public import CFSG.Sporadic.HS.Chain
public import CFSG.Sporadic.Fi23.SlpSpec
public import Certificates.Data.CFSGNative.Co1Sub.Check

public section

namespace CFSG.Sporadic.Co1Sub

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Fi23
open CFSG.Sporadic.Co1Sub.Native

abbrev co1D : VecData := Co1.Native.co1Data ()

@[expose] noncomputable def auxElt (i : ℕ) : J co1D := slpG (genG co1D) (aux ()) i

@[expose] noncomputable def subOf (idx : List ℕ) : Subgroup (J co1D) :=
  Subgroup.closure {g | ∃ i ∈ idx, auxElt i = g}

theorem auxElt_mem_subOf {idx : List ℕ} {i : ℕ} (hi : i ∈ idx) : auxElt i ∈ subOf idx :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem subOf_mono {idx idx' : List ℕ} (h : ∀ i ∈ idx, i ∈ idx') : subOf idx ≤ subOf idx' := by
  rw [subOf, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact auxElt_mem_subOf (h i hi)

noncomputable abbrev T₀ : Subgroup (J co1D) := subOf tIdx

noncomputable abbrev A₀ : Subgroup (J co1D) := subOf aIdx

noncomputable abbrev B₀ : Subgroup (J co1D) := subOf bIdx

theorem T₀_le_A₀ : T₀ ≤ A₀ := subOf_mono (by decide)

theorem T₀_le_B₀ : T₀ ≤ B₀ := subOf_mono (by decide)

end CFSG.Sporadic.Co1Sub

end
