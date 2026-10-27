module

public import CFSG.Quasithin.Background.C31SporL
public import CFSG.Quasithin.Background.C31Steps

public section

namespace CFSG.Quasithin.C31Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C48Spor

variable {G : Type} [Group G] [Finite G]

theorem c31SporStep_of
    (hA3 : A3Orbits G)
    (h22 : ASC22One G) (hInsp : InspC31Sporadic) (hM23 : SchurMult2M23) (hM24 : SchurMult2M24)
    (hJ4 : SchurMult2J4) (hHe : SchurMult2He) : C31SporStep G := by
  intro H R M L V K h hK h31 s hsn hsK
  have hKX := K_le_sporX (H := H) hK.1
  have hM0ne : img (sporN H K) (conjClosure L M) ≠ ⊥ := fun hb =>
    img_V_ne_bot h h31 (le_bot_iff.mp (hb ▸ img_mono h.V_le))
  have hsK' : IsSporadic s ↥(img (sporN H K) K) := IsSporadic.of_mulEquiv (kStarEquiv hKX) hsK
  have hJ : s = .J4 → C31SporJ.J4Cond (img (sporN H K) R) (img (sporN H K) M) := by
    rintro rfl
    exact C31SporJ.normalizer_img_le_of_j4 h22 h hK h31
      (IsSporadic.of_mulEquiv (kEquivKStar hK (center_eq_bot_of_img hK h31 hJ4 hsK')).symm hsK')
  obtain ⟨hC31, -, -⟩ := hInsp s hsn (↥(sporX H K) ⧸ sporN H K) (img (sporN H K) K)
    (img (sporN H K) (conjClosure L M)) (img (sporN H K) R) (img (sporN H K) M)
    (img (sporN H K) V) (img_K_normal H K) hsK'
    (centralizer_kStar_eq_bot (commutator_eq_of_isComponentOf hK) hKX) (img_mono h31.1)
    (img_M0_perfect h h31) hM0ne (exists_cComp_img h h31) (isPGroup_img h.pgroup)
    (img_mono h.le_M) (img_le_normalizer (le_normalizer_conjClosure L M))
    (img_le_normalizer (c2_9_two h).1) (img_isSylowTwoOf h h31) (img_mono h.V_le)
    (img_V_ne_bot h h31) (isElemAbelian_img h.V_elem) (img_V_comm h h31) (img_V_le_center h h31)
    (normalizer_inf_le_img_M h h31) (normalizer_img_R_le h h31) (not_img_K_le h hK h31) hJ
  rcases hC31 with c3 | c4 | c5 | c6 | c7 | c8 | c9
  · have c := c31Case3_of_img h hK h31 c3
    exact ⟨eq_of_c31Case3 hA3 h h31 c, Or.inl c⟩
  · have c := c31Case4_of_img h hK h31 hM23 c4
    exact ⟨eq_of_c31Case4 hA3 h c, Or.inr (Or.inl c)⟩
  · have c := c31Case5_of_img h hK h31 hM24 c5
    exact ⟨eq_of_c31Case5 hA3 h c, Or.inr (Or.inr (Or.inl c))⟩
  · have c := c31Case6_of_img h hK h31 hJ4 c6
    exact ⟨eq_of_c31Case6 hA3 h c, Or.inr (Or.inr (Or.inr (Or.inl c)))⟩
  · have c := c31Case7_of_img h hK h31 c7
    exact ⟨eq_of_c31Case7 hA3 h h31 c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c))))⟩
  · have c := c31Case8_of_img h hK h31 hHe c8
    exact ⟨eq_of_c31Case8 hA3 h c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl c)))))⟩
  · have c := c31Case9_of_img h hK h31 c9
    exact ⟨eq_of_c31Case9 hA3 h h31 c, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr c)))))⟩

end CFSG.Quasithin.C31Spor
