module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestOverP
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFStarSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRestAsch86J4Eleven_holds :
    SporKRestAsch86J4Eleven := by
  intro S Y hY hNY
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  let θ : (TauCeti.CFSGIndex.sporadic .J4).Group ≃* ↥CFSG.Sporadic.J4.J :=
    f.symm.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have : Finite (TauCeti.CFSGIndex.sporadic .J4).Group :=
    CFSG.Sporadic.Presentation.J4.finite_card_le.1
  have hfinJ : Finite ↥CFSG.Sporadic.J4.J := Finite.of_equiv _ θ.toEquiv
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h0 : CFSG.AGLEmbeddingD2.HeisLocal 11
      ((CFSG.Sporadic.J4Schreier.Q11Sylow : Sylow 11 ↥CFSG.Sporadic.J4.J) :
        Subgroup ↥CFSG.Sporadic.J4.J) :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.heisLocal_of_normMax_of_eq
      CFSG.AGLEmbeddingD2.Wilson.Coordinator.normMax_Q11
      CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.heisLocalEq_Q11Sylow
  have hsyl := @Sylow.card_eq_multiplicity ↥CFSG.Sporadic.J4.J (Subgroup.toGroup _) hfinJ 11 _
    CFSG.Sporadic.J4Schreier.Q11Sylow
  obtain ⟨-, hmax, hcent, -, -, -, hsolv, -⟩ :=
    @CFSG.AGLEmbeddingD2.heisLocal_sylow _ ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) _ hfinJ 11 _
      θ _ h0 hsyl S
  rcases hmax Y hNY with rfl | rfl
  · refine sporKRest_fstar_isPGroup_of_normal_sylow hsolv (S.subtype Subgroup.le_normalizer)
      (by rw [Sylow.coe_subtype]; exact Subgroup.normal_in_normalizer) fun x hx => ?_
    rw [Sylow.coe_subtype] at hx ⊢
    rw [Subgroup.mem_subgroupOf]
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hx) ⟨h, Subgroup.le_normalizer hh⟩
      (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hh))
  · exact absurd rfl hY

theorem sporKRest_coverOrUnmarked_J4_11 :
    SporKRestCoverOrUnmarked 11 (TauCeti.CFSGIndex.sporadic .J4).Group :=
  ggSporKRest_coverOrUnmarked_J4_11_of_asch86 sporKRestAsch86J4Eleven_holds

end CFSG.StandardType.SporadicShape

end
