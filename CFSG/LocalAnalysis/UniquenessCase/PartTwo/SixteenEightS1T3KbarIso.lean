module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIsoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Set

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem ThreeNat.exists_iso_of_mem_irrSet (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    {J J' : Subgroup W} (hJ : J ∈ irrSet L) (hJ' : J' ∈ irrSet L) :
    ∃ φ : ↥J ≃* ↥J', (∀ u : ↥J, ((φ u : ↥J') : W) ∈ fixV L ↔ (u : W) ∈ fixV L) ∧
      ∀ l ∈ L, ∀ u : ↥J, ∀ hu : l (u : W) ∈ J,
        ((φ ⟨l (u : W), hu⟩ : ↥J') : W) * (l ((φ u : ↥J') : W))⁻¹ ∈ fixV L := by
  have hq : CFSG.Open.IsQuasisimple ↥L := h.quasi
  have htrans : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ Subgroup.normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
    intro I₁ h₁ I₂ h₂
    obtain ⟨g, hg, hI⟩ := h.trans I₁ h₁ I₂ h₂
    exact ⟨g, hg.2, hI⟩
  have h7quot : Nat.card {Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)) //
      XMod.IsIrr ↥L Y} = 7 := by
    rw [← s16t3_card_irrSet_eq_quot hq]
    exact h7
  have hiso : XMod.Iso ↥L (tilde L (⊤ : Subgroup W) J) (tilde L (⊤ : Subgroup W) J') :=
    s16t3_iso_all_irr_of_seven h.elem hq h.sum htrans h7quot _ _
      (s16t3_isIrr_tilde_of_mem_irrSet hq hJ)
      (s16t3_isIrr_tilde_of_mem_irrSet hq hJ')
  have hcard : Nat.card ↥(J ⊓ fixV L) = Nat.card ↥(J' ⊓ fixV L) := by
    obtain ⟨a, ha, hJ'eq⟩ := h.trans J hJ J' hJ'
    have han : a ∈ Subgroup.normalizer (L : Set (MulAut W)) := ha.2
    have hfix_mem : ∀ w : W, a w ∈ fixV L ↔ w ∈ fixV L := by
      intro w
      constructor
      · intro hw x hx
        have h1 := hw (a * x * a⁻¹) (conj_mem_of_mem_normalizer han hx)
        have h3 : a (x w) = a w := by
          calc a (x w) = (a * x * a⁻¹) (a w) := by simp [MulAut.mul_apply]
            _ = a w := h1
        exact a.injective h3
      · intro hw x hx
        have h1 := hw (a⁻¹ * x * a) (inv_conj_mem_of_mem_normalizer han hx)
        calc x (a w) = a ((a⁻¹ * x * a) w) := by simp [MulAut.mul_apply]
          _ = a w := by rw [h1]
    have hfix : (fixV L).map a.toMonoidHom = fixV L := by
      ext w
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hfix_mem z).2 hz
      · intro hw
        exact ⟨a⁻¹ w, (hfix_mem (a⁻¹ w)).1 (by simpa using hw), by simp⟩
    have hJ'inf : J' ⊓ fixV L = (J ⊓ fixV L).map a.toMonoidHom := by
      conv_lhs => rw [hJ'eq, ← hfix]
      rw [Subgroup.map_inf J (fixV L) a.toMonoidHom a.injective]
    rw [hJ'inf]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective (J ⊓ fixV L) a.toMonoidHom a.injective)
  exact s16t3_exists_mulEquiv_of_tilde_iso h.elem hcard hiso

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
