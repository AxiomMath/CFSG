module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycMLayer
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLieLayerLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

@[expose] def GGLieLayerInputOn (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → S lab →
      LargeEvenLabelAll lab fun R _ I _ => ∀ φ ∈ I, LayerCycM.GGLayerLieTwo p φ

theorem GGLieLayerInputOn.mono {S S' : LargeEvenLabel → Prop} (h : GGLieLayerInputOn S)
    (hS : ∀ lab, S' lab → S lab) : GGLieLayerInputOn S' :=
  fun p lab hp hp2 hlab hs hS' => h p lab hp hp2 hlab hs (hS lab hS')

theorem ggLieLayerInputOn_six_of_input (h : GGLieLayerInputOn GGLieLayerLabel) :
    GGLieLayerInputOn fun lab => lab.tag = .E6 ∨ lab.tag = .twE6 :=
  h.mono fun _ hlab => by
    rcases hlab with h | h <;> simp [GGLieLayerLabel, h]

theorem conj_mem_largeEvenChevIDImage {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type)
    [Field K] (H : Subgroup (LargeEvenChevGL A K)) (x : LargeEvenCenterQuot H) :
    MulAut.conj x ∈ LargeEvenChevIDImage A K H :=
  Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)

theorem ggLayerCenterCyclicExcSixRestInput_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) :
    GGLayerCenterCyclicExcSixRestInput := by
  intro p lab hp hp2 hlab hs hsix
  have hS : lab.tag = .E6 ∨ lab.tag = .twE6 := hsix.imp (fun h => h.1) id
  intro Q hQ
  exact largeEvenRawDatum_mono (fun R _ I F hh =>
    ⟨hh.1, fun _ _ => LayerCycM.ggLayerCenterCyclic_of_layerLieTwo hG hp hp2 hh.2⟩)
    (h p lab hp hp2 hlab hs hS Q hQ)

section Twisted


theorem ggLayerInnerModelOn_triD4_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .triD4) :
    GGLayerInnerModelOn fun lab => lab.tag = .triD4 := by
  intro p lab hp hp2 hlab hs ht Q hQ
  have hQ' := h p lab hp hp2 hlab hs ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht hn
  subst ht
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hP⟩ := hQ'
  refine ⟨K, i1, i2, hK, hq, fun _ _ r => ?_⟩
  haveI := (finite_ggPSections_recipe_triD4 hn K hK hp hp2).1
  exact LayerCycM.ggModelLayerCyclic_of_layerLieTwo hG hp hp2
    (hP _ (conj_mem_largeEvenChevIDImage _ _ _ r))

end Twisted

section TwF4


theorem ggLayerInnerModelOn_twF4_of_lieLayer (hG : CFSG.Open.GriessAllModelsStatement)
    (h : GGLieLayerInputOn fun lab => lab.tag = .twF4) :
    GGLayerInnerModelOn fun lab => lab.tag = .twF4 := by
  intro p lab hp hp2 hlab hs ht Q hQ
  have hQ' := h p lab hp hp2 hlab hs ht Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  dsimp only [LargeEvenRawDatum] at hQ' ⊢
  obtain ⟨K, i1, i2, hK, hq, hP⟩ := hQ'
  refine ⟨K, i1, i2, hK, hq, fun _ _ r => ?_⟩
  haveI := (finite_ggPSections_recipe_twF4 ha K hK hp hp2).1
  exact LayerCycM.ggModelLayerCyclic_of_layerLieTwo hG hp hp2
    (hP _ (conj_mem_largeEvenChevIDImage _ _ _ r))

end TwF4

end CFSG.StandardType

end
