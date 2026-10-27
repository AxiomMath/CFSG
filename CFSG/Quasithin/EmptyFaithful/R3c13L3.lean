module

public import CFSG.Quasithin.EmptyFaithful.R3c13Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.R3c13

open Matrix CFSG.Assembly.LowTwoRank

section L3

abbrev S3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def uM3 (a b c : ZMod 2) : S3 :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by
    simp [Matrix.det_fin_three]
    decide⟩

@[expose] def l3cands : List S3 := [uM3 1 0 0, uM3 1 0 1, uM3 0 1 0, uM3 0 1 1]

set_option maxRecDepth 100000 in
theorem l3_invol_conj : ∀ σ : S3, σ ≠ 1 → σ * σ = 1 → ∃ ρ : S3, ρ * σ = uM3 0 0 1 * ρ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem l3_comm : ∀ y : S3, y * y = 1 → y ≠ 1 → y ≠ uM3 0 0 1 → y * uM3 0 0 1 = uM3 0 0 1 * y →
    y ∈ l3cands := by
  unfold l3cands
  decide +kernel

set_option maxRecDepth 100000 in
theorem l3_cent : ∀ u ∈ l3cands, ∀ g : S3, g * uM3 0 0 1 = uM3 0 0 1 * g → g * u = u * g →
    g = 1 ∨ g = uM3 0 0 1 ∨ g = u ∨ g = uM3 0 0 1 * u := by
  unfold l3cands
  decide +kernel

theorem kleinSelfCent_sl3 : KleinSelfCent S3 := by
  refine kleinSelfCent_of_conj (uM3 0 0 1) ?_ l3cands ?_ l3_comm l3_cent
  · intro h
    have := congrArg (fun g : S3 => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2) h
    simp [uM3] at this
  · intro a ha1 ha2
    exact l3_invol_conj a ha1 ha2

end L3

theorem kleinSelfCent_of_psl3 {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 2 1) : KleinSelfCent X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  let ψ : X ≃* S3 :=
    φ.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K hK2)
  exact kleinSelfCent_sl3.map ψ.symm

end CFSG.Quasithin.R3c13
