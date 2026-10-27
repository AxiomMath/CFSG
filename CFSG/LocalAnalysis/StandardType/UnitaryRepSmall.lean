module

public import CFSG.LocalAnalysis.StandardType.A8LiftBlocks
public import CFSG.LocalAnalysis.StandardType.UnitaryWeightGram
public import CFSG.LocalAnalysis.StandardType.UnitaryBaseChange

public section

namespace CFSG.StandardType

namespace UnitaryRep

open Matrix

theorem eq_one_of_card_le_five {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F) {Γ : Type*} [Group Γ]
    [Finite Γ] (h7 : HasOrderSevenData Γ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 5) {G : Matrix ι ι F} (hG : IsUnit G) (ρ : Γ →* Matrix ι ι F)
    (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) (g : Γ) : ρ g = 1 := by
  have hG' : IsUnit (G.map (algebraMap F (AlgebraicClosure F))) :=
    hG.map (RingHom.mapMatrix (algebraMap F (AlgebraicClosure F)))
  obtain ⟨σ', hσ'⟩ := UnitaryAlg.exists_ringEquiv_extension σ
  have hmain : UnitaryBaseChange.baseChangeHom ρ g = 1 :=
    HasOrderSevenData.map_eq_one_of_card_le_five_of_form h7 σ'
      (fun η hη => UnitaryWeight.ringEquiv_apply_eq_two_pow_of_pow_seven σ' hη)
      hG' hι (UnitaryBaseChange.baseChangeHom ρ)
      (UnitaryBaseChange.baseChangeHom_form hσ' ρ hρ) g
  exact (UnitaryBaseChange.baseChangeHom_eq_one_iff ρ g).mp hmain

end UnitaryRep

end CFSG.StandardType
