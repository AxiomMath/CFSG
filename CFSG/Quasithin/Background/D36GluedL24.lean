module

public import CFSG.Quasithin.Background.D36GluedLift

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def L24NaturalSection : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (U Z : Subgroup V), BinaryNaturalSL H U Z 2 2 →
      rk ↥U = rk ↥Z + 4 ∧
      (∀ R : Subgroup (MulAut V), R ≤ H → IsElemAbelian2 R → rk ↥R ≤ 2) ∧
      ∀ R : Subgroup (MulAut V), R ≤ H → IsElemAbelian2 R → R ≠ ⊥ →
        rk ↥(commModSub U R Z) + 2 ≤ rk ↥U ∧
        ∀ x ∈ commModSub U R Z, ∀ r ∈ R, r ≠ 1 → ∃ z ∈ U, (r z * z⁻¹) * x⁻¹ ∈ Z

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace GluedSwap

theorem false_of_L24 (h : GluedSwap X A U U') (hY : ∀ y : Y, y ^ 2 = 1) (hL₀X : L₀ ≤ X)
    (hL₀ : ∀ l ∈ L₀, ∀ u ∈ U', l u = u)
    (hdiag : ∀ b ∈ A ⊓ stabSub U, ∃ l ∈ L₀, ∀ u ∈ U, b u = l u)
    (hnat : BinaryNaturalSL L₀ U (U ⊓ fixV L₀) 2 2) (hmod : L24NaturalSection) : False := by
  obtain ⟨h0, h2R, h2⟩ := hmod Y hY L₀ U (U ⊓ fixV L₀) hnat
  have hRel := h.diag_isElemAbelian2 hL₀ hdiag
  have hRne := h.diag_ne_bot hdiag
  have hkR := h.rk_le_diagSub hdiag hRel
  have hR2 := h2R _ glueDiagSub_le hRel
  obtain ⟨hs1, hsk, hB⟩ := h.shape_B hY
  have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ :=
    le_inf inf_le_left (fun d hd l hl => hL₀ l hl d hd.2)
  have hdz : rk ↥(U ⊓ U') ≤ rk ↥(U ⊓ fixV L₀) := rk_mono hDZ
  have hUh : rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) ≤ rk ↥U := rk_mono (commModSub_le _ _ _)
  have hDU : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
  obtain ⟨h2a, h2b⟩ := h2 _ glueDiagSub_le hRel hRne
  have hle : commModSub U (A ⊓ stabSub U) (U ⊓ U') ≤
      commModSub U (glueDiagSub L₀ A U) (U ⊓ fixV L₀) := by
    intro x hx
    refine ⟨hx.1, fun ρ hρ => ?_⟩
    obtain ⟨-, b, hb, e⟩ := hρ
    rw [← e x hx.1]
    exact hDZ (hx.2 b hb)
  have hrk := rk_mono hle
  have hZD : U ⊓ U' = U ⊓ fixV L₀ := by
    refine eq_of_le_of_rk_le hY hDZ ?_
    omega
  refine h.false_of_commutators hY hL₀X hL₀ hdiag fun x hx r hr hr1 => ?_
  obtain ⟨z, hz, hzD⟩ := h2b x (hle hx) r hr hr1
  exact ⟨z, hz, hZD ▸ hzD⟩

end GluedSwap

end Glued

end CFSG.Quasithin
