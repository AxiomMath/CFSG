module

public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

@[expose] def embVec (m i : ℕ) (v : Fin 2 → K) : Fin m → K :=
  fun l => if l.val = i then v 0 else if l.val = i + 1 then v 1 else 0

theorem embVec_blockIdx {i : ℕ} (h : i + 2 ≤ m) (v : Fin 2 → K) (x : Fin 2) :
    embVec m i v (blockIdx i h x) = v x := by
  fin_cases x
  · simp [embVec, blockIdx]
  · simp [embVec, blockIdx]

theorem embVec_of_not_mem {i : ℕ} (v : Fin 2 → K) {l : Fin m}
    (hl : ¬ (i ≤ l.val ∧ l.val < i + 2)) : embVec m i v l = 0 := by
  have h1 : l.val ≠ i := fun h => hl ⟨h.ge, by omega⟩
  have h2 : l.val ≠ i + 1 := fun h => hl ⟨by omega, by omega⟩
  simp [embVec, h1, h2]

theorem embVec_smul (i : ℕ) (c : K) (v : Fin 2 → K) :
    embVec m i (c • v) = c • embVec m i v := by
  funext l
  simp only [embVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem embVec_add (i : ℕ) (u v : Fin 2 → K) :
    embVec m i (u + v) = embVec m i u + embVec m i v := by
  funext l
  simp only [embVec, Pi.add_apply]
  split_ifs <;> simp

theorem herm_embVec_left {i : ℕ} (h : i + 2 ≤ m) (v : Fin 2 → K) (w : Fin m → K) :
    herm σ (embVec m i v) w = herm σ v (fun x => w (blockIdx i h x)) := by
  rw [herm_def, herm_def, Fin.sum_univ_two]
  have hinj : Function.Injective (blockIdx i h : Fin 2 → Fin m) := blockIdx_injective h
  have : ∑ l : Fin m, σ (embVec m i v l) * w l =
      ∑ x : Fin 2, σ (embVec m i v (blockIdx i h x)) * w (blockIdx i h x) := by
    rw [← Finset.sum_image (f := fun l => σ (embVec m i v l) * w l)
      (fun x _ y _ hxy => hinj hxy)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    have hl' : ¬ (i ≤ l.val ∧ l.val < i + 2) := by
      rintro ⟨h1, h2⟩
      apply hl
      rw [Finset.mem_image]
      refine ⟨⟨l.val - i, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      simp [blockIdx]
      omega
    rw [embVec_of_not_mem v hl', map_zero, zero_mul]
  rw [this, Fin.sum_univ_two, embVec_blockIdx h v 0, embVec_blockIdx h v 1]

theorem herm_embVec_embVec {i : ℕ} (h : i + 2 ≤ m) (u v : Fin 2 → K) :
    herm σ (embVec m i u) (embVec m i v) = herm σ u v := by
  rw [herm_embVec_left h]
  simp only [embVec_blockIdx h]

end CFSG.RankThree.PartOne.SEITZ2
