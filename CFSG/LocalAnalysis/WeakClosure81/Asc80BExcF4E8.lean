module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcOuterR
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSL
import CFSG.LieType.SeitzGeneration.OrdinaryOuterLocal
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration


theorem seitzFour_f4_e8 :
    SeitzFour fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ (CFSG.Models.LieModel X .F4 0 p f ∨
      CFSG.Models.LieModel X .E8 0 p f) := by
  intro G _ _ L E hLn hLs hnab hP hC hE h4 _
  obtain ⟨p, f, hp2, hm⟩ := hP
  obtain ⟨τ, hτ, K, _, _, hK2, ⟨φ⟩⟩ : ∃ τ : Tag, (τ = .F4 ∨ τ = .E8) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 2 ∧
        Nonempty (↥L ≃* ↥(adjointGroup τ K)) := by
    have key : ∀ τ : Tag, CFSG.Blueprint.UntwistedChevalleyModel ↥L τ (p ^ f) → p.Prime →
        1 ≤ f → ∃ (K : Type) (_ : Field K) (_ : Finite K), ringChar K ≠ 2 ∧
          Nonempty (↥L ≃* ↥(adjointGroup τ K)) := by
      intro τ hU hp hf
      obtain ⟨K, _, _, hK, he⟩ := nonempty_mulEquiv_adjointGroup τ hU
      have : CharP K p :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
      exact ⟨K, inferInstance, inferInstance, by rw [ringChar.eq K p]; exact hp2, he⟩
    rcases hm with hm | hm
    · obtain ⟨hadm, hU⟩ :=
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
          hm).chevalleyExceptionalModel (by decide)
      exact ⟨.F4, Or.inl rfl, key .F4 hU hadm.1 hadm.2.1⟩
    · obtain ⟨hadm, hU⟩ :=
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
          hm).chevalleyExceptionalModel (by decide)
      exact ⟨.E8, Or.inr rfl, key .E8 hU hadm.1 hadm.2.1⟩
  set A := E.map (MulAut.conjNormal : G →* MulAut ↥L)
  have hA : CFSG.Open.IsElemAbelian 2 A := hE.map _
  have hA4 : Nat.card A = 4 := by
    rw [Subgroup.card_map_of_injective (conjNormal_injective_of_centralizer_eq_bot hC), h4]
  set A' := A.map (MulAut.congr φ).toMonoidHom
  have hA' : CFSG.Open.IsElemAbelian 2 A' := hA.map _
  have hA'4 : Nat.card A' = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr φ).injective, hA4]
  obtain ⟨R, hR, hRr, hER⟩ := exists_normalized_rSubgroup_four_f4_e8 hτ hK2 A' hA' hA'4
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : CharP K (ringChar K) := ringChar.charP K
  have : IsSimpleGroup ↥(adjointGroup τ K) := φ.symm.isSimpleGroup
  have hPA : PlaneGen A := (planeGen_map_congr φ A).1
    (planeGen_of_normalized_rSubgroup_adjointGroup hK2 A' hA' hA'4 R hR hRr hER)
  exact iSup_centralizer_eq_of_seitzHyperGamma hC h4
    ((planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [hA4]; norm_num)).1 hPA)

end CFSG.LocalAnalysis.WeakClosure81
