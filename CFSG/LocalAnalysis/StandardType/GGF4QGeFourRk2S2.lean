module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2OmegaBond
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2OmegaComm
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourA2PSU
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2OmegaLinear
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2PSU

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem ggF4QGeFourRk2_of_tableBPos_POmegaMinus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hpp : p.Prime) (hp2 : p ≠ 2) (hEl : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ A) {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .POmegaMinus 4 f X) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4)
    (hi : ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs)
    (hj : ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggAutomizer X Bs) :
    (CoxeterMatrix.F₄ i j = 2 →
      ∀ a ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs),
      ∀ b ∈ ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs),
        a * b = b * a) ∧
    (CoxeterMatrix.F₄ i j = 3 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
        LinearBlockStandardPair F W
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))) ∧
    (CoxeterMatrix.F₄ i j = 4 →
      GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs)) ∨
        GGF4QGeFourBond .S2 f (by omega)
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple j * w⁻¹) : ↥A) : MulAut ↥Bs))
          (ggRankOneIn X Bs ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥A) : MulAut ↥Bs))) :=
  ⟨ggF4QGeFourRk2_commute_of_tableBPosImage_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA hf hpos
      w i j hi hj,
    ggF4QGeFourRk2_linear_of_tableBPosImage_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA hf hpos
      w i j hi hj,
    ggF4QGeFourRk2_bond_of_tableBPosImage_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA hf hpos
      w i j hi hj⟩

theorem ggF4QGeFourRk2Input_S2_of_kgPos (hKG : GGF4QGeFourKGPosInput .S2) :
    GGF4QGeFourRk2Input .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow X hX w i j hi hj
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
  have hXA : ggAutomizer X Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rcases hX with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  obtain ⟨hposL, hposK⟩ := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  have hΩ : GGTableBPosImage p Bs .POmegaMinus 4 f X → _ := fun hO =>
    ggF4QGeFourRk2_of_tableBPos_POmegaMinus hpp hp2 hEl hNT hAind hpres hXA hf hO w i j hi hj
  rcases hX with rfl | rfl
  · exact hΩ hposL
  · rcases hposK with hU' | hO
    · exact ⟨ggF4QGeFourRk2_commute_of_tableBPosImage_PSU hpp hp2 hEl hNT hAind hpres hXA hf hU'
          w i j hi hj,
        fun hl => ggF4QGeFourPSUPairInput_holds G p Bs hpp hp2 hEl hNT _ hAind e hpres X hXA f hf
          hU' w i j hl hi hj,
        ggF4QGeFourRk2_bond_of_tableBPosImage_PSU hpp hp2 hEl hNT hAind hpres hXA hf hU'
          w i j hi hj⟩
    · exact hΩ hO

end CFSG.StandardType

end
