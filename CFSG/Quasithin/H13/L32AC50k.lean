module

public import CFSG.Quasithin.H13.L32AC50j
public import CFSG.Quasithin.H13.L32AC50g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

theorem lemma14_7_50_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h2 : Lemma14_7_2) (h4 : Lemma14_7_4_two_three)
    (h28 : Lemma14_7_28) (h29 : Thm14_7_29) (h32 : Lemma14_7_32) (h47 : Lemma14_7_47)
    (h48 : Lemma14_7_48) (hMod : Lemma14_7_50_Mod) : Lemma14_7_50 := by
  intro G _ _ T L V H S K hK hA
  obtain ⟨π, hker, hA7⟩ := exists_pi_a7 h37 h38 h28 h32 h47 h48 S hK hA
  obtain ⟨π', hker', hA7', hT⟩ := exists_pi_a7_ts S π hker hA7
  obtain ⟨K', hcK', hHKT, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  obtain ⟨I, hV1I, hIU, hIn, hcase⟩ := hMod G T L V H S K hK hHKT hL1K hA π' hker' hA7'
  rcases hcase with ⟨hr, Δ, hΔ, hst⟩ | ⟨β, -, hβker, hβ⟩
  · have hPT : (T.subgroupOf H).map π' = Alt7.taSub := by
      rcases hT with ⟨htop, -⟩ | ⟨-, hPT⟩
      · exfalso
        have h1 := Alt7.card_alt7
        rw [← hr, htop, Subgroup.card_top, Alt7.card_perm7] at h1
        omega
      · exact hPT
    exact false_of_four h1222 h1332 h1334 h29 S hker' hr hPT hIn hΔ hst
  · exact false_of_six h1222 h1332 h1334 h2 h4 S hker' hT hV1I hIU hIn hβker hβ

end CFSG.Quasithin.H13.L32A.C
