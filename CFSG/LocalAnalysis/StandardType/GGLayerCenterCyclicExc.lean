module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcTw
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import CFSG.LocalAnalysis.StandardType.GGLayerTitsCent

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGLayerCenterCyclicExcSixRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ lab.tag = .twE6

@[expose] def GGLayerCenterCyclicExcSixRestInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab → GGLayerCenterCyclicExcSixRestLabel p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)

@[expose] def GGLayerCenterCyclicExcRest : Prop :=
  GGExcAdjLayerCycInput .G2 2 ∧ GGExcAdjLayerCycInput .F4 1 ∧ GGExcAdjLayerCycInput .E7 1 ∧
    GGExcAdjLayerCycInput .E8 1 ∧ GGE6AdjLayerCycInput ∧
    GGLayerInnerModelOn (fun lab => lab.tag = .triD4 ∨ lab.tag = .twF4) ∧
    GGLayerCenterCyclicExcSixRestInput

theorem GGLayerInnerModelOn.mono {S S' : LargeEvenLabel → Prop} (h : GGLayerInnerModelOn S)
    (hS : ∀ lab, S' lab → S lab) : GGLayerInnerModelOn S' :=
  fun p lab hp hp2 hlab hs hS' => h p lab hp hp2 hlab hs (hS lab hS')

section Reduction


theorem ggLayerCenterCyclicExcInput_of_rest (h : GGLayerCenterCyclicExcRest) :
    GGLayerCenterCyclicExcInput := by
  obtain ⟨hG2, hF4, hE7, hE8, hE6, hTw, hSix⟩ := h
  intro p lab hp hp2 hlab hs hexc
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | A => exact (hexc.1 (Or.inl rfl)).elim
  | twA => exact (hexc.1 (Or.inr (Or.inl rfl))).elim
  | B => exact (hexc.1 (Or.inr (Or.inr (Or.inl rfl)))).elim
  | C => exact (hexc.1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
  | D => exact (hexc.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).elim
  | twD => exact (hexc.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).elim
  | B2der => exact (hexc.2 (Or.inl rfl)).elim
  | G2der => exact (hexc.2 (Or.inr (Or.inl rfl))).elim
  | twF4der => exact (hexc.2 (Or.inr (Or.inr rfl))).elim
  | G2 =>
    exact largeEvenLabelAll_layerCenterCyclic_adj hG2 hF4 hE7 hE8 hp hp2 hlab (Or.inl rfl) hs
  | F4 =>
    exact largeEvenLabelAll_layerCenterCyclic_adj hG2 hF4 hE7 hE8 hp hp2 hlab
      (Or.inr (Or.inl rfl)) hs
  | E7 =>
    exact largeEvenLabelAll_layerCenterCyclic_adj hG2 hF4 hE7 hE8 hp hp2 hlab
      (Or.inr (Or.inr (Or.inl rfl))) hs
  | E8 =>
    exact largeEvenLabelAll_layerCenterCyclic_adj hG2 hF4 hE7 hE8 hp hp2 hlab
      (Or.inr (Or.inr (Or.inr rfl))) hs
  | twB2 => exact largeEvenLabelAll_layerCenterCyclic_twB2 hp hlab rfl hs
  | triD4 =>
    exact largeEvenLabelAll_layerCenterCyclic_triD4 (hTw.mono fun _ h => Or.inl h) hp hp2 hlab
      rfl hs
  | twF4 =>
    exact largeEvenLabelAll_layerCenterCyclic_twF4 (hTw.mono fun _ h => Or.inr h) hp hp2 hlab
      rfl hs
  | E6 =>
    by_cases h3 : p = 3 ∧ 3 ∣ 2 ^ n - 1
    · exact hSix p _ hp hp2 hlab hs (Or.inl ⟨rfl, h3⟩)
    · refine largeEvenLabelAll_layerCenterCyclic_E6 hE6 hp hp2 hlab rfl hs ?_
      by_cases hp3 : p = 3
      · exact Or.inr fun h => h3 ⟨hp3, h⟩
      · exact Or.inl hp3
  | twE6 => exact hSix p _ hp hp2 hlab hs (Or.inr rfl)

theorem ggLayerCenterCyclicInput_of_excRest
    (h : GGLayerCenterCyclicExcRest) : GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_exc (ggLayerCenterCyclicExcInput_of_rest h)

theorem ggLayerCenterCyclicExcSixRestInput_of_input (h : GGLayerCenterCyclicExcInput) :
    GGLayerCenterCyclicExcSixRestInput := by
  intro p lab hp hp2 hlab hs hsix
  have ht : lab.tag = .E6 ∨ lab.tag = .twE6 := hsix.imp (fun h => h.1) id
  refine h p lab hp hp2 hlab hs ⟨fun hcl => ?_, fun hder => ?_⟩
  · obtain ⟨t, l, n⟩ := lab
    rcases ht with h6 | h6 <;> (dsimp only at h6; subst h6) <;>
      rcases hcl with h | h | h | h | h | h <;> cases h
  · obtain ⟨t, l, n⟩ := lab
    rcases ht with h6 | h6 <;> (dsimp only at h6; subst h6) <;>
      rcases hder with h | h | h <;> cases h

end Reduction

end CFSG.StandardType

end
