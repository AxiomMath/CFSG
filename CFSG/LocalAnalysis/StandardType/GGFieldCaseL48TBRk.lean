module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkConfig
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkHigh

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise

@[expose] def GGL48TableBKnownFormsRk : Prop :=
  (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGD4Three p lab → ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableBRk p R I (GGL48TB0Rank lab)) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGD4Three p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk p R I (GGL48TB0Rank lab)) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGD4Three p lab → ¬ GGL48F4TwoThreeLabel p lab →
        ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGL48F4TwoThreeLabel p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableBRk p R I 5) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ =>
          GGIrredModTableBRk p R I (GGL48TB0Rank lab) ∨ GGWPlusTableBRk p R I (GGL48TB0Rank lab))

theorem ggL48TorusWeylCentInput_of_knownRk (hF : GGL48NbrFieldInput)
    (hsub : GGNbrSubcomponentInput) (hUK : GGL48InnerKInput)
    (hID : GGBstarInnerDiagLInputOn fun _ _ => True) (h : GGL48TableBKnownFormsRk)
    (hb : GGL48TB0TwConfigInputInn) : GGL48TorusWeylCentInput := by
  obtain ⟨-, -, -, hTor, hTorRk, -, -, -⟩ := h
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hJD c hc hcp
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hJK : J ≤ K := hsub G p B x L D J hS.1.1.1 hS.1.1.2.2 y K hS.2.2.2.2.2.1.2.2.1
  obtain ⟨hL, lab, hlab, hraw⟩ := hID G p B Bs x L D J hS.1.1
    (ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hS.1.1.1)
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := largeEvenRawDatum_exists hraw
  by_cases hrow : GGL48TB0TwRow p lab
  · have hraw' := hTorRk p lab hp hlab hsplit hrow _ hraw
    obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
    have hmark : GGInnerDiagOnLab
        (fun p lab' => GGL48TB0TwRow p lab' ∧ GGL48TB0Rank lab' = GGL48TB0Rank lab) p Bs L :=
      ⟨hL, lab, hlab, largeEvenRawDatum_mono
        (fun _ _ _ _ ⟨hs, hna, θ', _, hrest⟩ => ⟨hs, hna, θ', ⟨hrow, rfl⟩, hrest⟩) hraw⟩
    have hr := ggL48TB0Rk_pow_le_card_of_inn hb hS hJD hmark
    exact torusWeylCent_at_of_tableBRk hF hS hJK (hUK G p B Bs x L D J X B₂ d y K U U₁ hS) θ hL
      hBsN h3 hKG hr |>.2 c hc hcp
  · have hraw' := hTor p lab hp hlab hsplit hrow _ hraw
    obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
    exact torusWeylCent_at_of_tableB hF hS hJK (hUK G p B Bs x L D J X B₂ d y K U U₁ hS) θ hL
      hBsN h3 hKG |>.2 c hc hcp

theorem ggL48HomocyclicOrMetaInput_of_knownRk (hF : GGL48NbrFieldInput)
    (hsub : GGNbrSubcomponentInput) (hinn : GGRawInnSubgroupInput) (ha₀ : GGLNoncyclicInput)
    (hID : GGBstarInnerDiagLInputOn fun _ _ => True) (h : GGL48TableBKnownFormsRk)
    (hb1 : GGL48F4TwoThreeConfigInput) (hb2 : GGL48TB0TwConfigInputInn) :
    GGL48HomocyclicOrMetaInput := by
  obtain ⟨hTBp, hTBpRk, hD43, hTor, hTorRk, hHM, hF4, hHMRk⟩ := h
  have hN := ggL48NormalInputS_of_nonCyclic (ggL48NonCyclicInput_of_lNoncyclic ha₀)
  have hUK := ggL48InnerKInput_of_rawInnSubgroup hinn
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hJD h46
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hNc := hN G p B Bs x L D J X B₂ d y K U U₁ hS
  have hJK : J ≤ K := hsub G p B x L D J hS.1.1.1 hS.1.1.2.2 y K hS.2.2.2.2.2.1.2.2.1
  have hUK' := hUK G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨hL, lab, hlab, hraw⟩ := hID G p B Bs x L D J hS.1.1
    (ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hS.1.1.1)
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := largeEvenRawDatum_exists hraw
  by_cases hD : GGD4Three p lab
  · have hraw' := hD43 p lab hp hlab hsplit hD _ hraw
    obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
    exact Or.inl (homocyclic_of_irredModTableB hF hS h46 θ hL hBsN h3
      fun M _ _ L' E θ' hE hpos => (hKG M L' E θ' hE hpos).2)
  · by_cases hF4l : GGL48F4TwoThreeLabel p lab
    · have hraw' := hF4 p lab hp hlab hsplit hF4l _ hraw
      obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
      have hmark : LargeEvenMarking L fun lab' _ _ _ _ _ => lab'.tag = .F4 ∧ lab'.n = 1 :=
        ⟨hL, lab, hlab, largeEvenRawDatum_mono
          (fun _ _ _ _ ⟨hs, hna, θ', _, _⟩ => ⟨hs, hna, θ', hF4l.1, hF4l.2.1⟩) hraw⟩
      have h5 : p ^ 5 ≤ Nat.card Bs := by
        obtain ⟨-, -, rfl⟩ := hF4l
        exact ggL48F4TwoThree_pow_five_le_card hb1 hS.1.1.1 hS.1.1.2.1
          (tableBPosition_of_setup hS θ hL hBsN h3).2.2.1 hmark
      exact Or.inl (homocyclic_of_irredModTableBRk hF hS h46 θ hL hBsN h3 hKG h5)
    · by_cases hrow : GGL48TB0TwRow p lab
      · have hraw' := largeEvenLabelAll_and (hTBpRk p lab hp hlab hsplit hrow)
          (largeEvenLabelAll_and (hHMRk p lab hp hlab hsplit hrow)
            (hTorRk p lab hp hlab hsplit hrow)) _ hraw
        obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKGp, hKGq, hKGt⟩ :=
          largeEvenRawDatum_exists hraw'
        have hmark : GGInnerDiagOnLab
            (fun p lab' => GGL48TB0TwRow p lab' ∧ GGL48TB0Rank lab' = GGL48TB0Rank lab) p Bs L :=
          ⟨hL, lab, hlab, largeEvenRawDatum_mono
            (fun _ _ _ _ ⟨hs, hna, θ', _, hrest⟩ => ⟨hs, hna, θ', ⟨hrow, rfl⟩, hrest⟩) hraw⟩
        have hr := ggL48TB0Rk_pow_le_card_of_inn hb2 hS hJD hmark
        rcases hKGq with hirr | hW
        · exact Or.inl (homocyclic_of_irredModTableBRk hF hS h46 θ hL hBsN h3 hirr hr)
        · have hZ := (torusWeylCent_at_of_tableBRk hF hS hJK hUK' θ hL hBsN h3 hKGt hr).1
          exact Or.inr (automizerMeta_at_of_tableBRk hS hNc θ hL hBsN h3 hZ hKGp hW hr)
      · have hraw' := largeEvenLabelAll_and (hTBp p lab hp hlab hsplit hD hrow)
          (largeEvenLabelAll_and (hHM p lab hp hlab hsplit hD hF4l hrow)
            (hTor p lab hp hlab hsplit hrow)) _ hraw
        obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKGp, hKGq, hKGt⟩ :=
          largeEvenRawDatum_exists hraw'
        rcases hKGq with hirr | hW
        · exact Or.inl (homocyclic_of_irredModTableB hF hS h46 θ hL hBsN h3 hirr)
        · have hZ := (torusWeylCent_at_of_tableB hF hS hJK hUK' θ hL hBsN h3 hKGt).1
          exact Or.inr (automizerMeta_at_of_tableB hS hNc θ hL hBsN h3 hZ hKGp hW)

theorem ggL48QuotIOneInput_of_knownRk (hF : GGL48NbrFieldInput)
    (hT : GGL48TorusWeylCentInput) (hsub : GGNbrSubcomponentInput) (hinn : GGRawInnSubgroupInput)
    (ha₀ : GGLNoncyclicInput) (hcyc : GGL46CyclicIOneInput) (hW : GGL48HomocyclicOrMetaInput)
    (hID : GGBstarInnerDiagLInputOn fun _ _ => True) (h : GGL48TableBKnownFormsRk)
    (hb : GGL48TB0TwConfigInputInn) : GGL48QuotIOneInput := by
  obtain ⟨hTBp, hTBpRk, hD43, -, -, -, -, -⟩ := h
  have hN := ggL48NormalInputS_of_nonCyclic (ggL48NonCyclicInput_of_lNoncyclic ha₀)
  have hLF := ggL48LFieldIOneInput_of_torusWeyl hF hT hsub (ggL48InnerKInput_of_rawInnSubgroup hinn)
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hI1 h46 R hRp hRmax hUR hA
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  have hNc := hN G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨hL, lab, hlab, hraw⟩ := hID G p B Bs x L D J hS.1.1
    (ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hS.1.1.1)
  obtain ⟨-, -, -, -, -, -, -, -, hsplit, -⟩ := largeEvenRawDatum_exists hraw
  by_cases hD : GGD4Three p lab
  · have hraw' := hD43 p lab hp hlab hsplit hD _ hraw
    obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
    obtain ⟨-, -, rfl⟩ := hD
    exact exists_monoidHom_of_irredTableB hF hS h46 θ hL hBsN h3 hKG (by norm_num)
  · by_cases hrow : GGL48TB0TwRow p lab
    · have hraw' := hTBpRk p lab hp hlab hsplit hrow _ hraw
      obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
      have hmark : GGInnerDiagOnLab
          (fun p lab' => GGL48TB0TwRow p lab' ∧ GGL48TB0Rank lab' = GGL48TB0Rank lab) p Bs L :=
        ⟨hL, lab, hlab, largeEvenRawDatum_mono
          (fun _ _ _ _ ⟨hs, hna, θ', _, hrest⟩ => ⟨hs, hna, θ', ⟨hrow, rfl⟩, hrest⟩) hraw⟩
      have hr := ggL48TB0Rk_pow_le_card_of_inn hb hS hI1 hmark
      obtain ⟨-, -, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
      have hcent := not_mem_commutator_H0_of_coverP hS hxN hNc
        (coverP_at_of_tableBRk hS hNc θ hL hBsN h3 hKG hr)
        (hLF G p B Bs x L D J X B₂ d y K U U₁ hS hI1)
      exact quot_at_of_cent hF hcyc hW hS hI1 h46 R hRp hRmax hUR hA hcent
    · have hraw' := hTBp p lab hp hlab hsplit hD hrow _ hraw
      obtain ⟨R', _, I, F, ⟨-, -, θ, -, -, hBsN, h3⟩, hKG⟩ := largeEvenRawDatum_exists hraw'
      obtain ⟨-, -, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
      have hcent := not_mem_commutator_H0_of_coverP hS hxN hNc
        (coverP_at_of_tableB hS hNc θ hL hBsN h3 hKG)
        (hLF G p B Bs x L D J X B₂ d y K U U₁ hS hI1)
      exact quot_at_of_cent hF hcyc hW hS hI1 h46 R hRp hRmax hUR hA hcent

theorem ggL48QuotIOneInput_of_knownFormsRk (hF : GGL48NbrFieldInput)
    (hsub : GGNbrSubcomponentInput) (hinn : GGRawInnSubgroupInput) (ha₀ : GGLNoncyclicInput)
    (hcyc : GGL46CyclicIOneInput) (hID : GGBstarInnerDiagLInputOn fun _ _ => True)
    (h : GGL48TableBKnownFormsRk) (hb1 : GGL48F4TwoThreeConfigInput)
    (hb2 : GGL48TB0TwConfigInputInn) : GGL48QuotIOneInput :=
  ggL48QuotIOneInput_of_knownRk hF
    (ggL48TorusWeylCentInput_of_knownRk hF hsub (ggL48InnerKInput_of_rawInnSubgroup hinn) hID h
      hb2)
    hsub hinn ha₀ hcyc (ggL48HomocyclicOrMetaInput_of_knownRk hF hsub hinn ha₀ hID h hb1 hb2) hID
    h hb2

end CFSG.StandardType

end
