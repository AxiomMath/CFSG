module

public import CFSG.Monster.B.Cbar.Octads

public section

namespace CFSG.Monster.B.Classical.Mog22

open CFSG.Monster.Code

@[expose] def X₀ : Finset (Fin 24) := Finset.univ.filter fun i => 2 ≤ (i : ℕ)

@[expose] noncomputable def ℬ₀ : Finset (Finset (Fin 24)) :=
  (octads.filter fun O => 0 ∈ O ∧ 1 ∈ O).image fun O => O \ {0, 1}

abbrev V₀ : Type := X₀ → ZMod 2

@[expose] def e (i : X₀) : V₀ := Pi.single i 1

@[expose] def blockVec (B : Finset (Fin 24)) : V₀ :=
  ∑ i ∈ Finset.univ.filter fun i : X₀ => (i : Fin 24) ∈ B, e i

theorem blockVec_apply (B : Finset (Fin 24)) (j : X₀) :
    blockVec B j = if (j : Fin 24) ∈ B then 1 else 0 := by
  simp only [blockVec, e, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp

@[expose] noncomputable def E₀ : Submodule (ZMod 2) V₀ :=
  Submodule.span (ZMod 2) (blockVec '' (ℬ₀ : Set (Finset (Fin 24))))

@[expose] def pt (i : Fin 24) (hi : 2 ≤ (i : ℕ) := by decide) : X₀ :=
  ⟨i, by simp [X₀, hi]⟩

@[expose] def v₀ : V₀ :=
  e (pt 2) + e (pt 4) + e (pt 6) + e (pt 8) + e (pt 10) + e (pt 12) + e (pt 14)

@[expose] noncomputable def K₀ : Submodule (ZMod 2) V₀ :=
  E₀ ⊔ Submodule.span (ZMod 2) {v₀}

abbrev W₀ : Type := V₀ ⧸ K₀

end CFSG.Monster.B.Classical.Mog22
