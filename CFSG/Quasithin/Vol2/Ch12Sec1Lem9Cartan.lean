module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9Geom

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem lem1219Cartan_of (h331 : Stmt3_3_1) (hB : Lem12211Borel) (hE : E2.E22StatementC) :
    Lem1219Cartan := by
  intro G _ _ T L V V₁ V₂ n hyp hTL H hH hlt
  have hqs := Sec121Thm.isQuasisimple_of_hyp121 hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, -⟩, -, -, hNT, -⟩ :=
    (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal hqs
  rw [hLT] at hMmax hNT
  obtain ⟨⟨C, hCM, hCo, hCi⟩, hall⟩ := hB G T (Subgroup.normalizer (L : Set G)) H hyp.simple
    hyp.nonabelian hyp.qtke hyp.sylow hMmax hTL hNT hH hlt.le
  obtain ⟨-, hstep⟩ := hall C hCM hCo hCi
  obtain ⟨p, A, hp, hp3, hAC, hA1, hAe, hAT⟩ := hstep (Or.inl hlt)
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq hyp.sylow
  have huniq : IsUniqueMaxOver H T (H ⊓ Subgroup.normalizer (L : Set G)) := by
    subst hS
    exact IsHStar.isUniqueMaxOver S hH hTL
  have hnot := Ch4.lemma4413NAPGt3_of hE G H T (H ⊓ Subgroup.normalizer (L : Set G)) hyp.simple
    hyp.nonabelian hyp.qtke hH.1.2 (lt_trans (by norm_num) hlt)
    (isSylowTwoOf_of_isSylowTwo hyp.sylow hH.1.1) huniq C hCM hCo hCi p A hp hp3 hAC hAe hAT
  refine ⟨p, A, hp, hp3, fun x => ⟨1, Subtype.ext ?_⟩, hA1, hAC.trans hCM, hAT, fun hN => ?_⟩
  · simpa using hAe.2 x x.2
  · exact hnot fun x hx => ⟨hx.1, hN hx.2⟩

theorem lem1219_of_steps (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hB : Lem12211Borel) (hE : E2.E22StatementC) (hPerm : Lem1219Perm)
    (hOdd : Lem1219OddLocal) : Lem1219 :=
  lem1219_of h1001 h331 h443 h1211 hH91 h1217 h1218 (lem1219Cartan_of h331 hB hE) hPerm hOdd
    lem1219Geom_holds

theorem stmt12_1_11_of_steps (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit')
    (h1211 : Lem1211) (hH91 : LemH91) (h1217 : Lem1217) (h1218 : Lem1218)
    (hB : Lem12211Borel) (hE : E2.E22StatementC) (hPerm : Lem1219Perm)
    (hOdd : Lem1219OddLocal) (h12110 : Lem12110) : Stmt12_1_11 :=
  stmt12_1_11_of_lemmas h1001 h331 h1217 h1218
    (lem1219_of_steps h1001 h331 h443 h1211 hH91 h1217 h1218 hB hE hPerm hOdd) h12110

end CFSG.Quasithin.H13
