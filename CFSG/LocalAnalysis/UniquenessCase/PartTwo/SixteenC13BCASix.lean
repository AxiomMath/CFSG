module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixNon
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCASixSw

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c13bcA_case168_6 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D ⊥ V L hV) (h6 : Case168_6 D ⊥ V hV L) : Insp1613U D V := by
  have hmods := s16c13bc_six_modules D h6
  obtain ⟨⟨e⟩, -, hs, hσ⟩ := h6
  obtain ⟨hLp, hLc, J₀, J₁, hJ₀, hJ₁, hinf, hsup, hfix₀, hE₀, hE₁, hψ₃⟩ := hmods
  have hp3 : (3 : ℕ) ∈ D.sig := by
    rw [hσ]
    exact Set.mem_singleton 3
  have hQ : Subgroup.center (↥(lBar ⊥ V hV L) × ↥(lBar ⊥ V hV L)) = ⊥ := by
    rw [Subgroup.center_prod, hLc, Subgroup.bot_prod_bot]
  obtain ⟨Z, -, hZM, hZc, hZn, -⟩ :=
    s16c1610_center_fstar (Mb := Mbar D.M ⊥ V hV) (p := 3) hQ e
  obtain ⟨z, hz3, hzL, hzW, hzne⟩ := s16c13bcA_six_z D hc hs hZM hZc hZn hLp hsup
  by_cases hall : ∀ w ∈ barSub ⊥ V hV (E3.wClos V D.k D.T),
      (lBar ⊥ V hV L).map (MulAut.conj w).toMonoidHom = lBar ⊥ V hV L
  · exact s16c13bcA_six_nonswap D hc hs hp3 hLc hJ₀ hJ₁ hinf hsup hE₀ hE₁ hψ₃ hz3 hzL hzW hzne
      hall
  · obtain ⟨t, ht⟩ := not_forall.1 hall
    obtain ⟨htW, htne⟩ := Classical.not_imp.1 ht
    exact s16c13bcA_six_swap D hc hs hp3 hLc hJ₀ hJ₁ hinf hsup hfix₀ hE₀ hE₁ hψ₃ hz3 hzL hzW
      hzne htW htne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
