module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

namespace RootDetectExc

theorem adjFieldForm_E7_E8
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (τ : Tag)
    (hτ : τ = .E7 ∨ τ = .E8) (p : ℕ) : AdjFieldForm τ K p := by
  obtain ⟨hex, Θ, hΘ, -, -, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  intro β hβ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex β
  refine ⟨g, σ, ?_, hgσ⟩
  rw [← hΘ β g σ hgσ, ← map_pow, hβ, map_one]

end RootDetectExc

section Family

theorem ggRootDetect_E8 : GGRootDetect .E8 := by
  intro G _ _ n f ψ hadm _ hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, -⟩ := hadm
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  change γ ∈ (e8Datum (GaloisField 2 f)).roots at hγ
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  exact RootDetectExc.ggPsiInnerDiag_of_isogeny (rootOperatorFamily .E8)
    (e8Datum (GaloisField 2 f)) (isPerfect_e8 (GaloisField 2 f)).commutator_eq_top
    center_adjointGroup_eq_bot (π := MonoidHom.id _) (fun x => ⟨x, rfl⟩)
    (by rw [MonoidHom.ker_id]; exact bot_le) (hp.odd_of_ne_two hp2)
    (RootDetectExc.adjFieldForm_E7_E8 hf _ hK .E8 (Or.inr rfl) p) hker hc hcp
    (α := ⟨γ, hγ'⟩)
    (fun t => ⟨xPar (rootOperatorFamily .E8) γ t, xPar_mem hγ' t, xPar_of_isRoot hγ' t⟩) hT

end Family

end CFSG.StandardType
