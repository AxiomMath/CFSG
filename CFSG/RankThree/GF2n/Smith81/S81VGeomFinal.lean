module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD4
public import CFSG.RankThree.GF2n.Smith81.S81UTrans

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_frame [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ) :
    ∃ a b : Fin 3 → Fin 6 → F, Frame σ a b := by
  have hv : exteriorPower.ιMulti F 3 (e3uT0Vec (F := F)) ≠ 0 := by
    rw [← pt0_eq_ιMulti_T0]
    exact pt0_ne_zero
  have hiso : ∀ i j : Fin 3,
      ∑ k : Fin 6, σ (e3uT0Vec (F := F) i k) * e3uT0Vec (F := F) j k = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e3uT0Vec, Fin.sum_univ_six, CharTwo.add_self_eq_zero]
  obtain ⟨b, hab, hbb⟩ := exists_hyperbolic_partners hσ hv hiso
  exact ⟨e3uT0Vec, b, fun i j => hiso i j, fun i j => hbb i j, fun i j => hab i j⟩

theorem exists_theta (hσ : IsUnitaryInvolution σ) : ∃ θ : F, θ + σ θ ≠ 0 := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  exact ⟨ω, by rw [hω]; exact one_ne_zero⟩

theorem dh5_generated [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hq : 3 ≤ Nat.card (Fσ σ)) :
    ∃ Pi : Finset (Submodule F (Fin 6 → F)), Pi.card ≤ 20 ∧ (∀ W ∈ Pi, IsPt σ W) ∧
      ∀ W, IsPt σ W → GenPts σ (↑Pi : Set (Submodule F (Fin 6 → F))) W := by
  obtain ⟨a, b, hf⟩ := exists_frame hσ
  obtain ⟨θ, hθ⟩ := exists_theta hσ
  obtain ⟨hfin, hcard⟩ := genSet_finite_ncard_le (σ := σ) (a := a) (b := b) (θ := θ)
  have hcard' := Set.ncard_eq_toFinset_card _ hfin
  refine ⟨hfin.toFinset, by omega, ?_, ?_⟩
  · intro W hW
    have hW' := (Set.Finite.mem_toFinset hfin).1 hW
    simp only [genSet, Set.mem_union] at hW'
    rcases hW' with ((h | h) | h) | h
    · exact Recipe.isPt_all hσ.invol (recipe0 hσ.invol hf hθ) W h
    · exact Recipe.isPt_all hσ.invol (recipe1 hσ.invol hf hθ) W h
    · exact Recipe.isPt_all hσ.invol (recipe2 hσ.invol hf hθ) W h
    · have hX := X3_facts hσ.invol hf hθ
      simp only [X3, Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · rw [h]
        exact hX.1
      · rw [h]
        exact hX.2.1
  · intro W hW
    rw [Set.Finite.coe_toFinset]
    exact dh5_generated_of_frame hσ hq hf hθ W hW

end CFSG.RankThree.GF2n.Smith81.S81V
