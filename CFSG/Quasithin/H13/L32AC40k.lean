module

public import CFSG.Quasithin.H13.L32AC40j
public import CFSG.Quasithin.H13.L32ACSk6

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem thm14_7_40_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (h38 : Lemma14_7_38)
    (h45 : Lemma14_7_45_A5) (h46 : Lemma14_7_46) : Thm14_7_40 := by
  intro G _ _ T L V H S K hK hHeq n hn hLie
  obtain ⟨-, -, -, hF⟩ := h30 G T L V H S K hK
  have hTK := h32 G T L V H S K hK
  have hK₀ : conjClosure K T = K :=
    le_antisymm
      (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk)
      (le_conjClosure K T)
  rw [hK₀, ← hHeq] at hF
  have hA5 := h45 G T L V H S K hK hHeq n hn hLie
  have hl1K := h46 G T L V H S K hK hHeq n hn hLie
  have hHKT : H = K ⊔ T := by
    rw [hHeq, ← sup_assoc, sup_eq_left.mpr hl1K]
  have := factElem hF (le_conjClosure V H)
  exact ⟨(s5_of h1222 h1332 h1334 S hF hK₀ hHKT hA5 hl1K).1,
    isL24Section_of h1222 h1332 h1334 h38 S hF hK₀ hHKT hA5 hl1K⟩

end CFSG.Quasithin.H13.L32A.C
