module

public import CFSG.Quasithin.Background.HSU3Beta
public import CFSG.Quasithin.Background.HSz
public import CFSG.Quasithin.Vol2.Ch7Elim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

theorem stmt7_2_1_SU3 : Stmt7_2_1_SU3 := by
  intro G _ _ T L I hyp hV hNM hc n hn2 hrow
  have hL : BinaryNaturalSU3 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hrow
  have hLM : autI hV (fsuL0 T L) ≤ autI hV ⊤ := autI_fsuL0_le hV
  have hMN := autI_top_le_normalizer (T := T) (L := L) (I := I) hV hNM
  obtain ⟨h1, h2, h3, -, h5⟩ := H2_SU3 hn2 hL hLM hMN
  exact ⟨h3, h1, h2, H2_SU3_beta hn2 hL hLM hMN (hypBang_autI hyp.fsu hV), h5⟩

theorem stmt7_2_1_Sz : Stmt7_2_1_Sz := by
  intro G _ _ T L I hyp hV hNM hc n hrow
  have hL : BinaryNaturalSz (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hrow
  have hLM : autI hV (fsuL0 T L) ≤ autI hV ⊤ := autI_fsuL0_le hV
  have hMN := autI_top_le_normalizer (T := T) (L := L) (I := I) hV hNM
  obtain ⟨h1, -, h3, h4⟩ := H3_Sz hL hLM hMN
  exact ⟨h1, h4, h3⟩

theorem stmt7_5_2_of_rows
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711 : Stmt7_1_1_normal) (h734 : Stmt7_3_4) (h741 : Stmt7_4_1)
    (hM22 : Stmt7_2_1_M22Hat) (hSL3 : Stmt7_2_1_SL3Pair) : Stmt7_5_2 :=
  stmt7_5_2_of h37 h38 h39 hmod h711 h734 h741 stmt7_2_1_SU3 stmt7_2_1_Sz hM22 hSL3

end CFSG.Quasithin.H13
