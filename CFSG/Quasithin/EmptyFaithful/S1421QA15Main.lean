module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Odd
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Dich
public import CFSG.Quasithin.EmptyFaithful.S1421QA15YNot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem lemma14215Core3_of_branches (hQ : Core3Quasi) (hE : Core3He) : Lemma14215Core3 := by
  intro G _ _ T M H K1 st hlt h13 hne M₁ hM₁ hT hS L hL hlt' hLn hGeq hLc
  have ctx : S1421.Core3Ctx T M H K1 L M₁ :=
    ⟨st, hlt, h13, hne, hM₁, hT, hS, hL, hlt', hLn, hGeq, hLc⟩
  by_cases hq : CFSG.IsQuasisimple ↥L
  · exact hQ G T M H K1 L M₁ ctx hq
  · obtain ⟨z, hz, hz1, hz2, hzc, hZ⟩ := S1421.exists_generator st
    have h115 := S1421.lemma115Hyp_g0 st hne hM₁ hS hz hz1 hz2 hzc hZ
    have hYG0 : yOfL22 T M ≤ S1421.g0Of T M H K1 :=
      (le_sup_left : yOfL22 T M ≤ S1421.l2Of T H (yOfL22 T M)).trans
        (le_sup_right.trans le_sup_left)
    have hodd : oddCoreIn (S1421.g0Of T M H K1) = ⊥ :=
      S1421.oddCoreIn_g0_eq_bot st hYG0 hz hz1 h115.inverts_oddCoreIn
    have hsolv := S1421.isSolvable_quotient_g0 st hLn hGeq
    rcases S1421.isQuasisimple_or_charTwo hL hLn hsolv hodd with h | h
    · exact absurd h hq
    · exact hE G T M H K1 L M₁ ctx hq h

theorem lemma14215Core3_of_inputs (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129StatementUsed G)
    (hl : Core3QuasiList) (hb : Core3QuasiBig) (h1 : Core3QuasiSmallLe) (h2 : Core3QuasiSmallU)
    (ho : Core3HeOdd) (hs : Core3HeSyl) : Lemma14215Core3 :=
  lemma14215Core3_of_branches (core3Quasi_of_list hl hb h1 h2)
    (core3He_of_cases ho (core3HeYnot_of_h129 h129) (core3HeYin_of_syl h129 hs))

end CFSG.Quasithin
