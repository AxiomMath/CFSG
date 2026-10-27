module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate2022
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.ComponentClassification.CatLeafProof

@[expose] def LangFullFieldAt : Prop :=
  ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    GGCompFieldAt (Nat.card K) (⊤ : Subgroup ↥(adjointGroup τ K))

theorem langFullFieldAt_holds
    : LangFullFieldAt := by
  intro τ hτ K _ _ _
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hk : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hqs : CFSG.IsQuasisimple ↥(adjointGroup τ K) := by
    rcases hτ with rfl | rfl
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K
    · exact isQuasisimple_e8 K
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥(adjointGroup τ K)) := by
    have h := CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K)) hqs
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have key : ∀ t : StatedLieTag, (t = .E7 ∧ τ = .E7 ∨ t = .E8 ∧ τ = .E8) →
      GGCompFieldAt (2 ^ (f : ℕ)) (⊤ : Subgroup ↥(adjointGroup τ K)) := by
    intro t htτ
    obtain ⟨-, hM⟩ := lieModel_of_mulEquiv_adjointGroup_E7_E8 htτ f.pos hk (MulEquiv.refl _)
    have hM' := LieModel.quotient_center_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(adjointGroup τ K)) ≃* ↥(adjointGroup τ K)).symm
      (hM.quotient_center hZ)
    refine ggCompFieldAt_of_lieModel hq hM' ⟨?_, ?_, ?_⟩ <;>
      rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  rw [hk]
  rcases hτ with rfl | rfl
  · exact key .E7 (Or.inl ⟨rfl, rfl⟩)
  · exact key .E8 (Or.inr ⟨rfl, rfl⟩)

end CFSG.StandardType.LangRat
