module

public import CFSG.Quasithin.H13.A6S13821zf
public import CFSG.Quasithin.H13.A6S13821za

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem case13820L24_of
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h1337 : Stmt13_3_7) (h13 : Lem13813)
    (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) : Case13820L24 := by
  intro G _ _ T L V S H K n hCtx hb hL24
  obtain ⟨hS, hH, hK, hKn, hHK, hn, hLie⟩ := hCtx
  obtain ⟨e₁⟩ := S.kst_equiv hS hH hK
  have hLieQ : LieF2n (↥K ⧸ CFSG.pCore 2 ↥K) n := lieF2n_congr e₁.symm hLie
  obtain ⟨e⟩ := S.exists_equiv_alt_of_l24 hS hH hK hL24
  obtain ⟨-, t, ⟨htT, htL⟩, -, hout⟩ := hb
  by_cases hhat : IsHatA6 L
  · exact S.false_of_hat_l24 h139 h37 h38 h1334 hS hH hK hKn hn hLieQ e hhat htT htL hout
  · have hL1K := S.L1_le_of_l24 h1337 h13 h1334 hS hH hK hKn hn hLieQ e hhat
    rcases S.exists_transv_or_quad_VH h36 h139 h1334 h13 h13314 h13315 h1356two hS hH hK hKn
        hHK with ⟨x, hxR, htr⟩ | ⟨Y, hYR, hYq, hY4⟩
    · exact S.false_of_transv_l24 h1334 hS hH hK hKn hHK hn hLieQ e hhat hL1K hxR htr
    · exact S.false_of_quad_l24 h13 h1334 h13314 h13315 h1356two hS hH hK hKn hHK hn hLieQ e
        hhat hL1K hYR hYq hY4

end CFSG.Quasithin.H13.A6
