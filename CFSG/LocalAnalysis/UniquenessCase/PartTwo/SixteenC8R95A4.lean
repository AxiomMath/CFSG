module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93k
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A3
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem r95_isL2_of_lbar_le (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (h92 : R92 D) (hnot : ¬ IsPGroup 3 (Lbar9 Y H))
    (hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    ∃ p f : ℕ, LieModel (Lbar9 Y H) .PSL 2 p f := by
  by_contra hL2
  obtain ⟨K, hK, ⟨e⟩⟩ :=
    r95_exists_core hyp hH (r95_isSimple_lbar hyp hH h92 hnot) hLM
  have hIM : I9 H ≤ D.M :=
    I9_le_M_of_not_isL2 hK461 hK462 hSch hK hH
      (fun h3 => hnot (h3.of_equiv e))
      (fun ⟨p, f, h⟩ => hL2 ⟨p, f, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩)
  exact hyp.2.1.2.1
    ((r95_prod_of_lbar_le hyp hH h92 hLM).le.trans (sup_le inf_le_right hIM))

theorem r95_caseA (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {D : Data G} {Y H D₃ : Subgroup G}
    (hyp : Hyp91 D Y H D₃) (hH : H ≠ ⊤) (h92 : R92 D)
    (hX : LieModel (BarO3 (Opp 3 Y)) .PSL 3 2 1)
    (hLM : img9 H (L9 Y H) ≤ img9 H (H ⊓ D.M)) :
    ∃ e : ℕ, 1 ≤ e ∧ LieModel (Lbar9 Y H) .PSL 2 7 e ∧ H = (H ⊓ D.M) ⊔ I9 H := by
  obtain ⟨E, π, hπ⟩ := r95_section_lbar hyp
  have hnot : ¬ IsPGroup 3 (Lbar9 Y H) := fun h3 => by
    obtain ⟨n, hn⟩ := ((h3.to_subgroup E).of_surjective π hπ).exists_card_dvd_pow
    rw [CFSG.Blueprint.LieModel.card_psl_three_two hX] at hn
    exact absurd
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) ((by omega : (7 : ℕ) ∣ 168).trans hn))
      (by omega)
  obtain ⟨p, f, hQ⟩ := r95_isL2_of_lbar_le hK461 hK462 hSch hyp hH h92 hnot hLM
  obtain rfl : p = 7 := r95_char_seven_of_section hQ π hπ hX
  exact ⟨f, hQ.admissible.2.1, hQ, r95_prod_of_lbar_le hyp hH h92 hLM⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
