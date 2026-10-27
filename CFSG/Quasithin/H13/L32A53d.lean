module

public import CFSG.Quasithin.H13.L32A512
public import CFSG.Quasithin.H13.L32A511Pf
public import CFSG.Quasithin.H13.L32A512c
public import CFSG.Quasithin.H13.L32A513c
public import CFSG.Quasithin.H13.L32A59S
public import CFSG.Quasithin.H13.L32A511Qi

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem contra14_5_3Solv_of (h4 : Lemma14_7_4_two_three) : Contra14_5_3Solv := by
  intro G _ _ T L V V₂ Y C hQ hsolv
  have hJ := C.thompsonJ_le_centralizer h4 hQ hsolv
  have hX := C.xL_eq_commutator h4 hQ hsolv
  have hO3 := lemma14_5_11_of_core lemma14_5_11Core_holds G T L V V₂ Y C (C.quot_xT h4).1 (C.inf_eq h4) hQ hsolv
    hJ hX
  obtain ⟨hne, hcase⟩ := C.lemma14_5_12 h4 hQ hsolv hO3 lemma14_5_12CaseOne_holds
  exact lemma14_5_13Fin_holds G T L V V₂ Y C (C.quot_xT h4).1 (C.inf_eq h4) hQ hsolv hJ hX hO3
    hne hcase

theorem thm14_5_3_of_inputs (h4 : Lemma14_7_4_two_three) (h55 : Lemma14_5_5Q)
    (h36 : A36ForSQTK) (h1434 : Lemma1434One) (hSym : Lemma14_5_8Sym) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : Thm14_5_3 :=
  thm14_5_3_of_solv (contra14_5_3Solv_of h4) h4 h55 h36 h1434 hSym h1222 h1332 h1334

end CFSG.Quasithin.H13.L32A.T53
