module

public import CFSG.Quasithin.MS93.S4A442R
public import CFSG.Quasithin.MS93.S4A442P1
public import CFSG.Quasithin.MS93.S4A442P2
public import CFSG.Quasithin.MS93.S4A431G

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s442Disj_of (h32 : S32) (h43 : S43) (h441 : S441) (hcomm : S442Comm)
    (hffd : S442FFD) : S442Disj := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_S32 h32 h
  have hV := h43 G M T L h hH.1 hH.2.1 hfull
  have h441' := h441 G M T L h F inferInstance inferInstance φ hH hb
  by_contra hD
  rw [Disj442, not_or, not_not] at hD
  obtain ⟨hA, hB'⟩ := hD
  have hB : ∀ g ∈ stab (puAmalgam h.le) α,
      conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2)) (ZM (puAmalgam h.le) α) ≤
        Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4) := by
    intro g hg
    by_contra hle
    exact hB' ⟨g, hg, hle⟩
  have hN := P442.stab_le_normalizer h hφ hC hb hV h441' hc hA hB
  obtain ⟨δ, hconf⟩ := P442.exists_conf442 _ h.hyp20 hb hV hc hA hB
  exact P442.false_of_conf h hC hb hV h441' hcomm hffd hH hconf hN

theorem s442_of (h32 : S32) (h43 : S43) (h441 : S441) (hcomm : S442Comm) (hffd : S442FFD) :
    S442 :=
  s442_of_disj (s442Disj_of h32 h43 h441 hcomm hffd)

end CFSG.Quasithin.MS93.S4A
