module

public import CFSG.Quasithin.Background.SmithB45MatM22

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.CharacterTheory.SteinbergBY CFSG.Sporadic.Mathieu Module

abbrev m22BinDim44 : Fin 4 → ℕ := ![1, 10, 10, 34]

@[expose] noncomputable def m22BinRep44 :
    ∀ i : Fin 4, G22 →* Matrix (Fin (m22BinDim44 i)) (Fin (m22BinDim44 i)) (ZMod 2)
  | 0 => rep1
  | 1 => rep10a
  | 2 => rep10b
  | 3 => rep34


theorem m22_binary_small44 (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W ≤ 44) :
    ∃ i, Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) (m22BinRep44 i))) := by
  refine exists_binary_equiv m22BinRep44 (fun i => ?_) 44 (fun U _ _ _ σ hσ hU => ?_) W τ hτ hW
  · fin_cases i
    · exact isIrreducible_rep1 _
    · exact isIrreducible_rep10a _
    · exact isIrreducible_rep10b _
    · exact isIrreducible_rep34 _
  · obtain ⟨-, j, ⟨e⟩⟩ := m22ClosureRep_complete (AlgebraicClosure (ZMod 2)) U σ hσ
    have hdim : finrank (AlgebraicClosure (ZMod 2)) U = m22Dim j := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    fin_cases j
    · exact ⟨0, ⟨e⟩⟩
    · exact ⟨1, ⟨e⟩⟩
    · exact ⟨2, ⟨e⟩⟩
    · exact ⟨3, ⟨e⟩⟩
    all_goals
      exfalso
      simp only [m22Dim] at hdim
      norm_num [hdim] at hU

theorem m22_binary_rep34_of_le (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G22 W) (hτ : τ.IsIrreducible)
    (h34 : 34 ≤ finrank (ZMod 2) W) (hW : finrank (ZMod 2) W ≤ 44) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep34)) := by
  obtain ⟨i, ⟨e⟩⟩ := m22_binary_small44 W τ hτ hW
  have hdim : finrank (ZMod 2) W = m22BinDim44 i := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  fin_cases i
  · simp only [m22BinDim44] at hdim
    norm_num [hdim] at h34
  · simp only [m22BinDim44] at hdim
    norm_num [hdim] at h34
  · simp only [m22BinDim44] at hdim
    norm_num [hdim] at h34
  · exact ⟨e⟩

end CFSG.Quasithin.B45Mat.M22
