module

import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E7Model
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.S2MathAs51642Interfaces

theorem q1E7_of_adjointMarking
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup .E7 F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ (b : G) (hb : b ∈ Bs), ggBeta L θ hN ⟨b, hb⟩ ∈
      Set.range (MulAut.conj : adjointGroup .E7 F →* MulAut (adjointGroup .E7 F))) :
    GGInnerDiagOn Bs J := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have : Finite (MulAut ↥L) := Finite.of_injective _ DFunLike.coe_injective
  refine ggInnerDiagOn_stdSub_of_quotient_components (r := 0) hp hcfg θ hN hI
    (by rw [pow_zero]; exact Nat.card_pos) ?_
  intro A hA hAI _ u hu hu1 C hC
  exact Q1E7Model.q1E7Model_holds hp hp2 hA hAI hu hu1 hC

theorem q1E7_selectedTransfer :
    Q1SelectedTransfer (fun _ lab => lab.tag = .E7) (fun _ _ _ => True) := by
  intro G _ _ p B Bs x L D J hcfg P hmark
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hmark
  refine ⟨hperf, lab, hΛ, ?_⟩
  obtain ⟨t, l, n⟩ := lab
  by_cases ht : t = .E7
  · subst ht
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw ⊢
    obtain ⟨K, iK, fK, hK, hs, hna, θK, hP⟩ := hraw
    refine ⟨K, iK, fK, hK, hs, hna, θK, hP, ?_⟩
    intro _ hN hactors
    have : CharP K 2 := charP_two_of_card hK
    let e := TableBExc.recipeEquiv .E7 K
    have hI : ∀ (b : G) (hb : b ∈ Bs), ggBeta L (θK.trans e) hN ⟨b, hb⟩ ∈
        Set.range (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) := by
      intro b hb
      obtain ⟨φ, hφ, hind⟩ := hactors b⁻¹ (Bs.inv_mem hb)
      have heq : φ = ggLAut L θK ⟨b, hN hb⟩ := by
        ext r
        obtain ⟨q, rfl⟩ := θK.surjective r
        induction q using QuotientGroup.induction_on with
        | H z =>
          rw [ggLAut_apply]
          apply hind z (L.normalizerMonoidHom ⟨b, hN hb⟩ z)
          change b * (z : G) * b⁻¹ = (b⁻¹)⁻¹ * (z : G) * b⁻¹
          rw [inv_inv]
      change ggLAut L (θK.trans e) ⟨b, hN hb⟩ ∈ _
      rw [NbrLangTypeA.ggLAut_trans (K := L) θK e ⟨b, hN hb⟩, ← heq]
      obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_E7 K hφ
      refine ⟨e r, ?_⟩
      rw [← hr]
      refine MulEquiv.ext fun z => ?_
      change e r * z * (e r)⁻¹ = e (r * e.symm z * r⁻¹)
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩)
      (q1E7_of_adjointMarking hcfg (θK.trans e) hN hI)
  · exact largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, hP, fun hS => absurd hS ht⟩) hraw

theorem q1E7InnerDiag_holds :
    GGBstarInnerDiagJInputOn (fun _ lab => lab.tag = .E7) :=
  q1On_of_selectedTransfer q1E7_selectedTransfer

end CFSG.StandardType
