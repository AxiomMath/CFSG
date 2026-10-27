module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24Univ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24IDA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.GH74.KGroups Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_cover_model (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L)) :
    ∃ (ψ : ↥(commSub ⊤ L) ≃* Orth3) (π : ↥(StatedSL 2 GF4) →* ↥L),
      Function.Surjective π ∧
      (∀ (γ : ↥(StatedSL 2 GF4)) (u : W) (hu : u ∈ commSub ⊤ L)
        (hu' : (π γ : MulAut W) u ∈ commSub ⊤ L),
        ψ ⟨(π γ : MulAut W) u, hu'⟩ =
          Multiplicative.ofAdd (orth3Act (γ : Matrix.GeneralLinearGroup (Fin 2) GF4)
            (Multiplicative.toAdd (ψ ⟨u, hu⟩)))) ∧
      (∀ u : ↥(commSub ⊤ L), (u : W) ∈ fixV L ↔ ψ u ∈ orth3Z) := by
  have hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L :=
    fun l hl u hu => commSub_inv_H L ⊤ l hl u hu
  exact s16h_sl24_cover_model_aux hW hrow hZ4 hU (s16h_sl24_univ hW hrow hZ4 hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
