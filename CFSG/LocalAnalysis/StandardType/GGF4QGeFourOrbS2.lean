module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

section Inputs

theorem ggF4QGeFourOrbInput_S2_of_kgPos (hKG : GGF4QGeFourKGPosInput .S2) :
    GGF4QGeFourOrbInput .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow i j
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨hL, hK⟩ : GGTableBPosImage p Bs .POmegaMinus 4 f L ∧
      (GGTableBPosImage p Bs .PSU 6 f K ∨ GGTableBPosImage p Bs .POmegaMinus 4 f K) :=
    hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  have hML : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
      ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
    intro k l
    rw [coxeterMatrix_POmegaMinus_four]
    rfl
  obtain ⟨-, -, -, εL, hεL, -⟩ := hL
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _) hML
  rcases hK with hK | hK
  · obtain ⟨-, -, -, εK, hεK, -⟩ := hK
    obtain ⟨σK, -, hMK⟩ := exists_coxeterMatrix_PSU_six (f := f) (by omega)
    obtain ⟨b, hb, hb01, hb12, hb02, hbK⟩ :=
      exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK σK hMK
    exact ggF4QGeFourOrb_of_triples ha hb ha01 ha12 ha02 hb01 hb12 hb02 haL hbK i j
  · obtain ⟨-, -, -, εK, hεK, -⟩ := hK
    obtain ⟨b, hb, hb01, hb12, hb02, hbK⟩ :=
      exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_right εK hεK (Equiv.refl _) hML
    exact ggF4QGeFourOrb_of_triples ha hb ha01 ha12 ha02 hb01 hb12 hb02 haL hbK i j

end Inputs

end CFSG.StandardType

end
