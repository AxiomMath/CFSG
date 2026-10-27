
module

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase

public import CFSG.Sporadic.ThSchreier.GlobalTransportBase1
public import CFSG.Sporadic.ThSchreier.ScanCheck
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

theorem planeGens_length : planeGens.length = 2 := rfl

theorem discPos_eq (j : ℕ) :
    discPos planeGens parIdx colLab j = discOf (readU32 thSt.par j) := by
  simp only [discPos, colLab, discOf, parIdx, labIdx, planeGens_length]
  omega

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF

theorem colPlane_inj :
    ∀ i < nX, ∀ j < nX, colPlane i = colPlane j → i = j :=
  fun i hi j hj h => planeAt_injective hF i hi j hj (psiSet_injective h)

theorem colPlane_img :
    ∀ i < nX, ∀ (k : ℕ) (hk : k < planeGens.length),
    colImg k i < nX ∧ planeGens[k] (colPlane i) = colPlane (colImg k i) := by
  intro i hi k hk
  rw [planeGens_length] at hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [colImg_zero]
    refine ⟨hF.αlt i hi, ?_⟩
    show a • colPlane i = colPlane (αIdx i)
    rw [colPlane, colPlane, ← psiSet_smul, (a_smul_planeAt hF i hi).2]
  · rw [colImg_one]
    refine ⟨hF.βlt i hi, ?_⟩
    show b • colPlane i = colPlane (βIdx i)
    rw [colPlane, colPlane, ← psiSet_smul, (b_smul_planeAt hF i hi).2]

theorem colPlane_tree : ∀ j, 1 ≤ j → j < nX →
    parIdx j < j ∧ colLab j < planeGens.length ∧ colImg (colLab j) (parIdx j) = j := by
  intro j hj1 hjn
  obtain ⟨hp, hcase⟩ := hF.tree j hjn (by omega)
  refine ⟨hp, ?_, ?_⟩
  · rw [planeGens_length, colLab]
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · rcases hcase with ⟨h, he⟩ | ⟨h, he⟩
    · rw [colLab, h]; exact (colImg_zero _).trans he
    · rw [colLab, h]; exact (colImg_one _).trans he

include hS

omit hF in
theorem colPlane_mono : ∀ j, 1 ≤ j → j + 1 < nX →
    discPos planeGens parIdx colLab j < discPos planeGens parIdx colLab (j + 1) := by
  intro j hj1 hj
  rw [discPos_eq, discPos_eq]
  exact ScanFacts.mono hS j hj1 hj

theorem colPlane_disc : ∀ i < nX, ∀ k < planeGens.length,
    colImg k i = 0 ∨ discPos planeGens parIdx colLab (colImg k i) ≤ i * planeGens.length + k := by
  intro i hi k hk
  rw [planeGens_length] at hk ⊢
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rcases ScanFacts.discA hS i hi (hF.αlt i hi) with h0 | hle
    · exact Or.inl (by simp only [colImg, ite_true]; exact h0)
    · right
      have hle' : discOf (readU32 thSt.par (αIdx i)) ≤ 2 * i := hle
      rw [discPos_eq]
      simp only [colImg, ite_true]
      omega
  · rcases ScanFacts.discB hS i hi (hF.βlt i hi) with h0 | hle
    · exact Or.inl (by simp only [colImg, one_ne_zero, ite_false]; exact h0)
    · right
      have hle' : discOf (readU32 thSt.par (βIdx i)) ≤ 2 * i + 1 := hle
      rw [discPos_eq]
      simp only [colImg, one_ne_zero, ite_false]
      omega

end Facts

end CFSG.Sporadic.ThSchreier
