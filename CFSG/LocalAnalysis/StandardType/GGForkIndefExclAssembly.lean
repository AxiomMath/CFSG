module

public import CFSG.LocalAnalysis.StandardType.GGP3CellDispatch
public import CFSG.LocalAnalysis.StandardType.GGP5CellDispatch
public import CFSG.LocalAnalysis.StandardType.GGR4Pump
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkSplit
public import CFSG.LocalAnalysis.StandardType.GGForkCellsDefs
public import CFSG.LocalAnalysis.StandardType.GGForkRestTrichotomy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem gfie_extDatum_zero {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) (hF : GGForkPairing C b c h α ha αa) {φ : Λ → MulAut ↥Bs}
    {φa : MulAut ↥Bs} (hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs) (hφa : φa ∈ ggInduced ⊤ Bs)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h)) (hu : αa (h b) = 0) :
    GGExtDatum ι (ggAttachCartan C c) (ggOptFam φa φ) (ggOptFam ha h) (ggOptFam αa α) := by
  have hv : α b ha = 0 := (ggFork_cross_iff hp2 hNT ι hF hφ hφa hlin hlina).1.mp hu
  have hdiag : ∀ j : Option Λ, ggAttachCartan C c j j = 2 := by
    rintro (_ | j)
    · rfl
    · rw [ggAttachCartan_some_some, hF.diag j]
  have hP : ∀ i j : Option Λ,
      ggOptFam αa α i (ggOptFam ha h j) = (ggAttachCartan C c i j : ZMod p) := by
    rintro (_ | i) (_ | j)
    · simp [hF.aa]
    · by_cases hjb : j = b
      · subst hjb
        simp [hu, hF.ne]
      · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_none_some, hF.aL j hjb]
        split_ifs <;> simp
    · by_cases hib : i = b
      · subst hib
        simp [hv, hF.ne]
      · simp only [ggOptFam_none, ggOptFam_some, ggAttachCartan_some_none, hF.aR i hib]
        split_ifs <;> simp
    · simp only [ggOptFam_some, ggAttachCartan_some_some, hF.pair]
  refine ⟨?_, ?_, hP, hind, hdiag⟩
  · rintro (_ | i)
    · exact hφa
    · exact hφ i
  · rintro (_ | i) w
    · exact hlina w
    · exact hlin i w

private theorem gfie_card_one {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b : Λ}
    (h : GGIndefCellOne C b) : 5 ≤ Fintype.card Λ := by
  unfold GGIndefCellOne at h
  rcases h with ⟨n, hn, e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩
  · rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · rw [← Fintype.card_congr e, Fintype.card_fin]
    omega

private theorem gfie_zero_small {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b : Λ}
    (h : GGIndefCellZero C b) (hc : ¬ 5 ≤ Fintype.card Λ) :
    ∃ e : Fin 4 ≃ Λ, ((∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) ∧ (b = e 0 ∨ b = e 3) := by
  unfold GGIndefCellZero at h
  rcases h with ⟨n, hn, e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, -, -⟩ | ⟨e, hC, hb⟩
  · exfalso
    apply hc
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · exfalso
    apply hc
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · exfalso
    apply hc
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · exfalso
    apply hc
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  · exact ⟨e, hC, hb⟩

private theorem gfie_F4_pos {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (hF : GGForkMatrix C b c) (e : Fin 4 ≃ Λ)
    (hC : (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) :
    (b = e 0 ∧ c = e 1) ∨ (b = e 3 ∧ c = e 2) := by
  rcases hC with hC | hC
  · rcases ggLeafPos_F4 (hF.leafPos e hC) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← h1, e.apply_symm_apply], by rw [← h2, e.apply_symm_apply]⟩
    · exact Or.inr ⟨by rw [← h1, e.apply_symm_apply], by rw [← h2, e.apply_symm_apply]⟩
  · have hC' : ∀ i j, C (e i) (e j) = (Matrix.transpose CartanMatrix.F₄) i j := by
      intro i j
      rw [Matrix.transpose_apply]
      exact hC i j
    rcases ggLeafPos_F4T (hF.leafPos e hC') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [← h1, e.apply_symm_apply], by rw [← h2, e.apply_symm_apply]⟩
    · exact Or.inr ⟨by rw [← h1, e.apply_symm_apply], by rw [← h2, e.apply_symm_apply]⟩

theorem ggForkIndefExclRest_of_five (ha₀ : GGLNoncyclicInput) (hPU : GGPumpupInput)
    (hSpan : GGTBSpanInput) (hNF : GGR4NotFiveAtLine) (hZ : GGCentreTwoKnown)
    (hZtw : GGCentreTrivialTwKnown) (hJleaf : GGR4JInput) :
    GGForkIndefExclRest := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hOW _ Λ _ _ M C V _ _ ι φ φa h α ha αa b
    c hM hCM hF hlin hlina hind hAL hAK hshA hshBCD
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hcon
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  have hφ : ∀ i, φ i ∈ ggInduced ⊤ Bs := by
    intro i
    have h1 : φ i ∈ ggAutomizer L Bs := by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact mem_ggAutomizer_iff.mp (ggAutomizer_mono Bs (le_top : L ≤ ⊤) h1)
  have hφa : φa ∈ ggInduced ⊤ Bs := by
    have h1 : φa ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Or.inr rfl)
    exact mem_ggAutomizer_iff.mp (ggAutomizer_mono Bs (le_top : K ≤ ⊤) h1)
  obtain ⟨htri0, htri1⟩ := ggForkRest_trichotomy hM hCM hF.toMatrix hshBCD
  refine ⟨fun hu0 => ?_, fun hu1 => ?_⟩
  · rcases htri0 with hW | hcell
    · exact Or.inl hW
    · exfalso
      rcases hp35 with hp3 | h5
      · by_cases hcard : 5 ≤ Fintype.card Λ
        · exact ggFork_false_of_indefCell_three ha₀ hp3 hcfg hNT hM hCM hF hlin hlina hind hAL hAK
            hcard (Or.inl ⟨hu0, hcell⟩)
        · obtain ⟨e, hC, hbe⟩ := gfie_zero_small hcell hcard
          have hpos := gfie_F4_pos hF.toMatrix e hC
          have hD0 := gfie_extDatum_zero hp2 hNT ι hF hφ hφa hlin hlina hind hu0
          have hSc : GGScalarsPmOne Bs := ggScalarsPmOne_of_prime_three hcfg hp3
          have hspan : Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤ :=
            hSpan G p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hOW Λ M C V ι φ φa h α ha αa b c
              hM hCM hF hlin hlina hind hAL hAK
          exact ggFork_R4_false_of_five hp3 hPU hNF hZ hZtw hJleaf hcfg hOp hInn hNT hnbr hRG hSc
            hD0 hspan ⟨e, hC, hpos⟩ hAL hAK
      · exact ggFork_false_of_indefCell_five_line ha₀ h5 hcfg hNT hM hCM hF hlin hlina hind hAL hAK
          (Or.inl ⟨hu0, hcell⟩)
  · rcases htri1 with hW | hN | hcell
    · exact Or.inl hW
    · exact Or.inr hN
    · exfalso
      rcases hp35 with hp3 | h5
      · exact ggFork_false_of_indefCell_three ha₀ hp3 hcfg hNT hM hCM hF hlin hlina hind hAL hAK
          (gfie_card_one hcell) (Or.inr ⟨hu1, hcell⟩)
      · exact ggFork_false_of_indefCell_five_line ha₀ h5 hcfg hNT hM hCM hF hlin hlina hind hAL hAK
          (Or.inr ⟨hu1, hcell⟩)

theorem ggForkIndefExclRest_of_inputs (ha₀ : GGLNoncyclicInput) (hPU : GGPumpupInput)
    (hSpan : GGTBSpanInput) (hPump : GGPumpCInput) (hPumpTw : GGPumpTwInput)
    (hZ : GGCentreTwoKnown) (hZtw : GGCentreTrivialTwKnown) (hJleaf : GGR4JInput) :
    GGForkIndefExclRest :=
  ggForkIndefExclRest_of_five ha₀ hPU hSpan (ggR4NotFiveAtLine_of_pump hPump hPumpTw) hZ hZtw hJleaf

theorem ggForkIndefExclRest_of_notFive (ha₀ : GGLNoncyclicInput) (hPU : GGPumpupInput)
    (hSpan : GGTBSpanInput) (hPump : GGPumpCInput) (hPumpTw : GGPumpTwNotFive)
    (hZ : GGCentreTwoKnown) (hZtw : GGCentreTrivialTwKnown) (hJleaf : GGR4JInput) :
    GGForkIndefExclRest :=
  ggForkIndefExclRest_of_five ha₀ hPU hSpan (ggR4NotFiveAtLine_of_notFive hPump hPumpTw) hZ hZtw
    hJleaf

end CFSG.StandardType
