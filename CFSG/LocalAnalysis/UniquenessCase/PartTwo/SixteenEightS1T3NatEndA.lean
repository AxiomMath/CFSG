module

public import CFSG.Quasithin.Background.FFC5T2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U Z : Subgroup W}

theorem s16t3_sumOfNat_summand {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ} (h : SumOfNat N H U Z k) (i : Fin k) :
    ∃ I : Subgroup W, Z ≤ I ∧ I ≤ U ∧ SumOfNat N H I Z 1 := by
  obtain ⟨J, hZJ, -, hsup, hNJ⟩ := h
  refine ⟨J i, hZJ i, ?_, ?_⟩
  · rw [← hsup]
    exact (le_iSup J i).trans le_sup_right
  · refine ⟨fun _ => J i, fun _ => hZJ i, ?_, ?_, fun _ => hNJ i⟩
    · intro j
      have hempty : (⨆ (j' : Fin 1) (_ : j' ≠ j), J i) = ⊥ := by
        apply iSup_eq_bot.2
        intro j'
        apply iSup_eq_bot.2
        intro hj
        exact (hj (Subsingleton.elim j' j)).elim
      rw [hempty, sup_bot_eq]
      exact inf_le_right
    · have hone : (⨆ _ : Fin 1, J i) = J i :=
        le_antisymm (iSup_le fun _ => le_rfl) (le_iSup (fun _ : Fin 1 => J i) 0)
      rw [hone, sup_eq_right.2 (hZJ i)]

theorem s16t3_sumOfNat_one {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : SumOfNat N H U Z 1) :
    N H U Z := by
  obtain ⟨I, hZI, -, hsup, hN⟩ := h
  have h0 : (⨆ i : Fin 1, I i) = I 0 := by
    refine le_antisymm (iSup_le fun i => ?_) (le_iSup I 0)
    rw [Subsingleton.elim i 0]
  have hU : I 0 = U := by
    rw [h0, sup_eq_right.2 (hZI 0)] at hsup
    exact hsup
  rw [← hU]
  exact hN 0

theorem s16t3_sumOfNat_singleton {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {I Z : Subgroup W} (hZI : Z ≤ I) (hN : N H I Z) :
    SumOfNat N H I Z 1 := by
  refine ⟨fun _ => I, fun _ => hZI, ?_, ?_, fun _ => hN⟩
  · intro j
    have hempty : (⨆ (j' : Fin 1) (_ : j' ≠ j), I) = ⊥ := by
      apply iSup_eq_bot.2
      intro j'
      apply iSup_eq_bot.2
      intro hj
      exact (hj (Subsingleton.elim j' j)).elim
    rw [hempty, sup_bot_eq]
    exact inf_le_right
  · have hone : (⨆ _ : Fin 1, I) = I :=
      le_antisymm (iSup_le fun _ => le_rfl) (le_iSup (fun _ : Fin 1 => I) 0)
    rw [hone, sup_eq_right.2 hZI]

theorem s16t3_realizes_restrict {D : FFModel} {H : Subgroup (MulAut W)} {U Z I : Subgroup W}
    (h : D.Realizes H U Z) (hIU : I ≤ U) (hI : StableUnder H I) (hIZ : I ⊔ Z = U) :
    D.Realizes H I (I ⊓ Z) := by
  obtain ⟨π, hπ⟩ := h
  have hI' : ∀ g : ↥H, ∀ u ∈ I, (g : MulAut W) u ∈ I := fun g u hu => hI g g.2 u hu
  have hres := FFC.realizesVia_restrict hπ (U' := I) hIZ hI'
  refine ⟨π, ?_⟩
  rw [inf_comm] at hres
  exact hres

theorem s16t3_restrict_binaryNaturalSL {n a : ℕ} {I : Subgroup W}
    (h : BinaryNaturalSL L U Z n a) (hIU : I ≤ U) (hI : StableUnder L I) (hIZ : I ⊔ Z = U) :
    BinaryNaturalSL L I (I ⊓ Z) n a := by
  obtain ⟨K, hK, hKf, hK2, hR⟩ := h
  exact ⟨K, hK, hKf, hK2, s16t3_realizes_restrict hR hIU hI hIZ⟩

theorem s16t3_restrict_natSpn {n a : ℕ} {I : Subgroup W}
    (h : NatSpn L U Z n a) (hIU : I ≤ U) (hI : StableUnder L I) (hIZ : I ⊔ Z = U) :
    NatSpn L I (I ⊓ Z) n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_realizes_restrict hR hIU hI hIZ⟩

theorem s16t3_restrict_natOmegaPlus {n a : ℕ} {I : Subgroup W}
    (h : NatOmegaPlus L U Z n a) (hIU : I ≤ U) (hI : StableUnder L I) (hIZ : I ⊔ Z = U) :
    NatOmegaPlus L I (I ⊓ Z) n a := by
  obtain ⟨he, K, hK, hKf, hK2, hR⟩ := h
  exact ⟨he, K, hK, hKf, hK2, s16t3_realizes_restrict hR hIU hI hIZ⟩

theorem s16t3_restrict_natOmegaMinus {n a : ℕ} {I : Subgroup W}
    (h : NatOmegaMinus L U Z n a) (hIU : I ≤ U) (hI : StableUnder L I) (hIZ : I ⊔ Z = U) :
    NatOmegaMinus L I (I ⊓ Z) n a := by
  obtain ⟨he, K, hK, hKf, b, c, hK2, hirr, hR⟩ := h
  exact ⟨he, K, hK, hKf, b, c, hK2, hirr, s16t3_realizes_restrict hR hIU hI hIZ⟩

theorem s16t3_restrict_alternatingNatural {n : ℕ} {I : Subgroup W}
    (h : AlternatingNatural L U Z n) (hIU : I ≤ U) (hI : StableUnder L I) (hIZ : I ⊔ Z = U) :
    AlternatingNatural L I (I ⊓ Z) n :=
  s16t3_realizes_restrict h hIU hI hIZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
