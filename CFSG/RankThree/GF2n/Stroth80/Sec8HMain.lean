module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HCases

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec8_normR_of_inter_large (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {m : ℕ}
    (hmSp : SpMNat hc t m) {g : G} (hg : g ∈ M)
    (hlarge : Nat.card Z ^ (m + 1) <
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t))) :
    g ∈ Subgroup.normalizer (Rt M (LB M Q B) t : Set G) := by
  obtain ⟨C, D, hC, hD, hCV, hDV, hnp⟩ := sec8_exists_pair h34 hRoot hs hr hmSp hg hlarge
  exact sec8_normR_of_pair h34 hRoot h51 hs hg hC hD hCV hDV hnp

theorem sec8LemmaH_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) :
    Sec8LemmaHStatement := by
  intro G _ _ M Q Z B hc n t hs r hr m hmSp g hgM hgL hVW hcard
  classical
  by_cases hAc : ∀ x ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      x ∈ (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r
  · have hlarge := sec8_caseA_large h34 hRoot h53 h310chi hs hr hmSp hgM hgL hAc
    rw [← card_inf_conjSubgroup_inv g] at hlarge
    exact sec8_normR_of_inter_large h34 hRoot h51 hs hr hmSp hgM hlarge
  · exact (sec8_caseB h34 hRoot h53 h310chi hs hr hmSp hgM hgL hVW hcard hAc).elim

end

end CFSG.RankThree.GF2n.Stroth80
