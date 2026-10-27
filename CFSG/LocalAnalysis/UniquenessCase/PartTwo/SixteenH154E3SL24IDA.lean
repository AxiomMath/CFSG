module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_model_aux (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L)
    (huniv : CFSG.ASVolI.ChIJK.IsUniversalCovering
      (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range
      ((commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L))) :
    ∃ (ψ : ↥(commSub ⊤ L) ≃* Orth3) (π : ↥(StatedSL 2 GF4) →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥(StatedSL 2 GF4)) (u : W) (hu : u ∈ commSub ⊤ L)
        (hu' : (π γ : MulAut W) u ∈ commSub ⊤ L),
        ψ ⟨(π γ : MulAut W) u, hu'⟩ =
          Multiplicative.ofAdd (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
            (Multiplicative.toAdd (ψ ⟨u, hu⟩)))) ∧
      (∀ u : ↥(commSub ⊤ L), (u : W) ∈ fixV L ↔ ψ u ∈ orth3Z) := by
  obtain ⟨ψ, π, A, hA, hπ, hAlin, hact, hker⟩ :=
    s16h_sl24_cover_plumb hW hrow hU huniv
  refine ⟨ψ.trans s16h_sl24_coordEquiv, π, hπ, ?_, ?_⟩
  · intro γ u hu hu'
    rw [MulEquiv.trans_apply, hact γ u hu hu', MulEquiv.trans_apply]
    exact s16h_sl24_liftHom_orth3 A hA hAlin γ (ψ ⟨u, hu⟩)
  · intro u
    rw [MulEquiv.trans_apply, ← hker u]
    set p : (Fin 2 → GF4) × GF4 := Multiplicative.toAdd (ψ u) with hp
    have hcoe : s16h_sl24_coordEquiv (ψ u) = Multiplicative.ofAdd (p.1 0, p.1 1, p.2) := by
      rw [show ψ u = Multiplicative.ofAdd p from by rw [hp, ofAdd_toAdd]]
      rw [s16h_sl24_coordEquiv_apply]
    rw [hcoe]
    change p.1 = 0 ↔ p.1 0 = 0 ∧ p.1 1 = 0
    constructor
    · intro h
      rw [h]
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext i
      fin_cases i
      · exact h1
      · exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
