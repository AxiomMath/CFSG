module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTriPairAutAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgTri_pairAut
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (θ : MulAut ((triD4Universal F σ).K ⧸ Subgroup.center (triD4Universal F σ).K))
    {β' : Fin (triD4Universal F σ).D.rank → ℤ}
    (hβ' : β' ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β')
    (u' : (triD4Universal F σ).K) :
    ∃ β : Fin (triD4Universal F σ).D.rank → ℤ,
      (β ∈ (triD4Universal F σ).D.roots ∧ GGLongRoot (triD4Universal F σ).D β) ∧
      ∃ u : (triD4Universal F σ).K,
        (ggRootSub (triD4Universal F σ).D
          (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) β' u').map θ.toMonoidHom =
          ggRootSub (triD4Universal F σ).D
            (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) β u ∧
        (ggRootSub (triD4Universal F σ).D
          (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) (-β') u').map
            θ.toMonoidHom =
          ggRootSub (triD4Universal F σ).D
            (QuotientGroup.mk' (Subgroup.center (triD4Universal F σ).K)) (-β) u := by
  have hZ : Subgroup.center (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥ :=
    CFSG.ClassicalInvolution.RouteD.center_twistedGroup_eq_bot_of_card σ Nat.prime_two
      hT.1 hT.2.1 hT.2.2
  obtain ⟨α, hα⟩ := irg_exists_aut_of_center_eq_bot hZ θ
  have hβG2 : CFSG.Blueprint.Chevalley.IsRoot .G2 β' := by
    have h := hβ'.1
    change β' ∈ (CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ).roots at h
    rwa [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots] at h
  obtain ⟨t, ht⟩ := irgTA_exists_conj_map_twistedRootGroup hT α
  refine ⟨β', hβ', α u' * t, ?_, ?_⟩
  · change (((CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup σ β').map
          (MulAut.conj u').toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center
          (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)))).map θ.toMonoidHom =
      ((CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup σ β').map
        (MulAut.conj (α u' * t)).toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center
          (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)))
    exact irg_map_conj_subgroup_mulAut _ θ α hα (ht β' hβG2)
  · change (((CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup σ (-β')).map
          (MulAut.conj u').toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center
          (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)))).map θ.toMonoidHom =
      ((CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup σ (-β')).map
        (MulAut.conj (α u' * t)).toMonoidHom).map
        (QuotientGroup.mk' (Subgroup.center
          (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)))
    exact irg_map_conj_subgroup_mulAut _ θ α hα
      (ht (-β') (CFSG.LieType.Steinberg.TagRoots.isRoot_neg hβG2))

end CFSG.StandardType.RCKRP
