module

public import CFSG.RankThree.GF2n.Tim78S48AffPts
public import CFSG.RankThree.GF2n.Tim78S48PairModel

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem exists_endgameData (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hphase1 : ∀ g' : G, Hyp48 M B T g' → ¬ conjSubgroup g' B ≤ P → Phase1 B T g')
    {g : G} (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (h1 : Phase1 B T g) :
    ∃ C L : Subgroup G, EndgameData M B Q P T g C L := by
  have hBgQ := H.Bg_inf_Q hCen hU hP
  have hTgW := H.Tg_inf_W hCen hU h48 hP
  have hTgnc := H.Tg_not_cent hCen hU hP
  have hcent := H.aC_cent h48 hP h1
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (H.conj_B_ne_bot g)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  exact ⟨H.aC g, H.aC g ⊔ conjSubgroup g B,
    { hC := fun c => H.mem_aC
      hL := rfl
      B_le_C := H.B_le_aC h48
      C_elem := H.aC_elem h48 h1 hcent
      C_cent := hcent
      C_inf := H.aC_inf_Bg hBgQ
      card_C := (H.card_aC h48 hP hBgQ h1 hcent hy hy1').1
      L_elem := H.aL_elem h48 h1 hcent
      relIndex_L := H.relIndex_aL hBgQ hcent
      Q_norm := H.Q_le_normalizer_aL h48 hP hBgQ h1.part_W hcent
      Q_comm := fun x hx l hl => H.Q_comm_aL h48 hP hBgQ h1.part_W hcent hx hl
      T_comm := fun t ht l hl => H.T_comm_aL h48 ht hcent hl
      T_rel := by rw [H.T_inf_centralizer_aL h48 hcent]; exact h1.relIndex_T
      part := H.part_aL h48 hP hBgQ h1 hTgW hTgnc hcent hphase1
      trans := H.trans_aL h48 hP hBgQ h1 hTgW hTgnc hcent hphase1
      Bg_inf := hBgQ }⟩

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
