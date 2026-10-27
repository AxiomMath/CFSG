module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentySwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineSwap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineCap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_nine (D : Data G) (h14 : R16_14 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : Choice1613 D ⊥ V hV L A)
    (hAg : A ≤ conjSubgroup V g) (hΔ : Concl1617 D ⊥ V hV L A g Δ)
    (h9 : Case168_9 D ⊥ V hV L) : False := by
  classical
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  obtain ⟨I₀, I₁, a, hS₀, hN3⟩ := s16c167_twenty_nine_swap D hC hA hAel hΔ h9
  obtain ⟨B₀, hB₀, hhyp⟩ := s16c167_twenty_hyper hS₀ hAel hV
  have hc2 : ¬ Case168_2 D ⊥ V hV L := by
    intro h2
    have h3 : D.sig = {3} := h2.2.2
    have h7 : D.sig = {7} := h9.2.2.2.2
    rw [h3] at h7
    exact absurd h7 (by norm_num)
  have hI := s16c167_insp18_case9 D hC.setting hΔ hc2 h9
  have hcap :=
    s16c167_twenty_nine_cap D hC (h14 ⊥ V L hV hC) hA hAg hΔ hI h9 hhyp
  obtain ⟨-, hle⟩ := s16c167_twenty_chain hS₀ hAel hV hB₀ rfl hcap
  have hB₀A : B₀ ≤ A := fun x hx => ((hB₀ x).1 hx).1
  have hge := hN3 B₀ hB₀A (fun b hb => ((hB₀ b).1 hb).2)
  have hle4 : Nat.card ↥(I₀ ⊓ centralizer (B₀ : Set G)) ≤ 4 := by
    simpa using hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
