module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.Quasithin.H13.NQCatExceptional
import CFSG.LieType.Chevalley.OrdinaryExceptionalOuterTwoPart
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem r891OutCore_holds :
    R891OutCore := by
  intro X _ _ n h
  have hCE : ChevalleyExceptionalModel X .trialityD4 2 n :=
    ((LieModel.chevalleyExceptional_iff (by decide)).1 h).2
  have hn1 : 1 ≤ n := h.admissible.2.1
  refine ⟨CFSG.Quasithin.H13.NQCat.outer_isCyclic_of_even_trialityD4_model hn1 hCE, ?_⟩
  obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hCE
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : σ'.toRingHom = σ := RingHom.ext fun _ => rfl
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := hK
  obtain ⟨-, -, ⟨Θ, -, hsurj, hΘker, -⟩, -, hcard, -, -, ⟨e₀⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn1 K hK3 σ' hσ
  have hout : Nat.card (Outer (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) = 3 * n := by
    rw [card_outer_eq_of_ker_eq_inner Θ hsurj hΘker, hcard]
  rw [hσ'] at e₀ hout
  rw [Nat.card_congr (equivalence (e.trans e₀)).toEquiv]
  exact hout

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
