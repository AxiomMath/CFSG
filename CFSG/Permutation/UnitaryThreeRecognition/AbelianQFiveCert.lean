module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveModel
public meta import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveModel
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Logic.Function.Iterate
public import Certificates.Certificate8052

public section

namespace CFSG.UnitaryThreeRecognition.AbelianQFive

theorem search_all : ∀ ν α β : ZMod 5, ∀ m ∈ [3, 7], ν * ν = -1 →
    (gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) → (gen ν α β)^[4] (0, 0, 1) = (0, 0, -1) →
    (tablesOKb ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) && g8b ⟨ν, α, β, m⟩ &&
      search ⟨ν, α, β, m⟩ (orbitData ⟨ν, α, β, m⟩) 17
        (Array.replicate (orbitData ⟨ν, α, β, m⟩).reps.size none)) = true :=
  Certificates.certificate8052

theorem not_validTau (ν α β : ZMod 5) (m : ℕ) (hν : ν * ν = -1)
    (hA4 : (gen ν α β)^[4] (0, 1, 0) = (0, -1, 0) ∧ (gen ν α β)^[4] (0, 0, 1) = (0, 0, -1))
    (hm : m = 3 ∨ m = 7) (τ : M → M) : ¬ ValidTau ν α β m τ := by
  intro hv
  have hmem : m ∈ [3, 7] := by
    rcases hm with rfl | rfl <;> simp
  have h := search_all ν α β m hmem hν hA4.1 hA4.2
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hT, h8⟩, hs⟩ := h
  refine search_sound (P := ⟨ν, α, β, m⟩) (tablesOK_of_tablesOKb hT) hv (g8_of_g8b h8) 17 _
    (by simp) (fun i hi v hv' => ?_) hs
  rw [Array.getElem?_replicate] at hv'
  split_ifs at hv'
  simp at hv'

end CFSG.UnitaryThreeRecognition.AbelianQFive
