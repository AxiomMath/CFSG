module

public import CFSG.Quasithin.Vol2.KGFactInsp4316Out
public import CFSG.Quasithin.Vol2.Ch4Sec3InspInner
public import CFSG.Quasithin.Vol2.Ch4Sec3L43Steps

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem insp4316_of
    (hOD : Insp4316OutDer) (hEm : Insp4316E16m) (hEL : Insp4316E16L) (hL3 : Insp4316L3eps)
    (hOL : Insp4316OutLie) : Ch4.Insp4316 := by
  intro X _ _ S hSn hS hnc hlist hC n F _ _ hn hF R K hR1 hR2 hKS hKp hKR hRK hχ hprime hcore
    x hxn hxR hxK hgen
  have cfg : Cfg4316 S R K n x := ⟨hSn, hS, hnc, hlist, hC, hn, hR1, hR2, hKS, hKp, hKR, hRK,
    ⟨F, inferInstance, inferInstance, hF, hχ⟩, hprime, hcore, hxn, hxR, hxK, hgen⟩
  have hQS : pCoreOf 2 K ≤ S := (Subgroup.map_subtype_le _).trans hKS
  by_cases hx1 : x = 1
  · subst hx1
    have hR : R = pCoreOf 2 K := by
      refine le_antisymm ?_ hcore
      rwa [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right, bot_sup_eq] at hgen
    by_cases hn2 : n = 2
    · subst hn2
      by_cases hE : IsElemAbelian 2 R ∧ Nat.card ↥R = 2 ^ 4 ∧ ∀ R' : Subgroup X, R' ≤ R →
          K ≤ Subgroup.normalizer (R' : Set X) → R' = ⊥ ∨ R' = R
      · obtain ⟨hEa, hEc, hEi⟩ := hE
        refine Or.inl ⟨rfl, ?_⟩
        rcases hprime 3 Nat.prime_three (by norm_num) (by norm_num) with h3 | ⟨-, h3⟩
        · exact hEm X S R K hSn hS hnc hlist hC F hF hKS hKp hKR hRK hχ h3 hR hEa hEc hEi
        · exact hEL X S R K hSn hS hnc hlist hC F hF hKS hKp hKR hRK hχ h3 hR hEa hEc hEi
      · exact Or.inr ⟨rfl, fun _ => hE⟩
    · exact Or.inr ⟨rfl, fun h => absurd h hn2⟩
  · left
    obtain ⟨p, hp, hp2, hpn, x', hx'z, hx'o, hx'K⟩ :=
      Ch4.InspInner.exists_prime_pow (by omega) hx1 hxn (hRK hxR) hxK
    by_cases hx'S : x' ∈ S
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP F 2 := charP_of_card_eq_prime_pow hF
      obtain ⟨χ, hχs, hχk⟩ := hχ
      obtain ⟨rfl, hL⟩ := Ch4.InspInner.eq_three hKS hF hχs hχk hprime hp hp2 hpn hx'S hx'o hx'K
      have ⟨s, q, _, hsq⟩ := hL
      have hRS : R ≤ S :=
        le_of_odd_commutator hC (hOD ↥S hS hnc (Or.inr ⟨s, q, hsq⟩)) hR2 hQS hgen
      exact hL3 X S R K n x cfg hRS x' hx'z hx'o hx'S hL
    · rcases outTwoFam_or_oddOutLie hlist with hT | hLie
      · exact absurd (dvd_card_outer_of_not_mem hC hx'S hp hx'o)
          (not_dvd_outer_of_outTwoFam hT hp hp2)
      · have hRS : R ≤ S := le_of_odd_commutator hC (hOD ↥S hS hnc (Or.inl hLie)) hR2 hQS hgen
        exact hOL X S R K n x cfg hRS hLie x' hx'z p hp hp2 hpn hx'o hx'S

end CFSG.Quasithin.H13.KGInsp4316
