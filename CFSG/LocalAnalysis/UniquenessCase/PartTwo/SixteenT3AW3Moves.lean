module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Cycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

theorem s16t_w3_S_moves (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) (i : ι) : ∃ s ∈ S, ∃ y ∈ Y i, s y ≠ y := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ j, (∀ s ∈ S, ∀ y ∈ Y j, s y = y) →
      ∀ s ∈ S, ∀ y ∈ (Y j).map f.toMonoidHom, s y = y := by
    intro j hj s hs
    have h1 := s16t_w3_conj_fix (f := f) (hj _ (s16t_w3_conj_mem h hS (X.inv_mem hfX) hs))
    rwa [inv_inv, show f * (f⁻¹ * s * f) * f⁻¹ = s by group] at h1
  obtain ⟨i₁, i₂, h1, h2, -, -, -, -, hall⟩ := s16t_w3_cycle h hfX hf3 hfm i
  have hfix1 : ∀ s ∈ S, ∀ y ∈ Y i₁, s y = y := by
    rw [← h1]
    exact hstep i hcon
  have hfix2 : ∀ s ∈ S, ∀ y ∈ Y i₂, s y = y := by
    rw [← h2]
    exact hstep i₁ hfix1
  have hS1 : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 fun s hs =>
    s16t_w3_ext h.iSup_eq_top fun j y hy => by
      rcases hall j with rfl | rfl | rfl
      · exact hcon s hs y hy
      · exact hfix1 s hs y hy
      · exact hfix2 s hs y hy
  have h9 := s16t_w3_card_S h hS hSc
  rw [hS1, Subgroup.card_bot] at h9
  norm_num at h9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
