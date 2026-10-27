module

public import CFSG.Quasithin.Background.RonanE114Pair
public import CFSG.Quasithin.Background.RonanE114A7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11
open CFSG.QuasithinUnique.Setup.X6

section Tits


theorem hasSolvInvPair_tits {X : Type} [Group X] [Finite X] (hX : IsTits X) :
    HasSolvInvPair X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 X))
  have hT := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  generalize (P₀ : Subgroup X) = U at hT
  obtain ⟨H, N, hUc, hUH, hUN, hHc, hNc, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice X hX U hT
  obtain ⟨hHtop, hNtop⟩ := ne_top_of_card hHc hNc
  have hcardne : ∀ {A B : Subgroup X}, A ≤ B → Nat.card A ∣ Nat.card B := fun h =>
    Subgroup.card_dvd_of_le h
  refine hasSolvInvPair_of_unique_orders hT hUH hUN hHs hNs ?_ ?_ ?_
  ·
    rcases hlat (H ⊔ N) (hUH.trans le_sup_left) with h | h | h | h
    · exfalso
      have := hcardne (le_sup_left : H ≤ H ⊔ N)
      rw [h, hUc, hHc] at this
      exact absurd this (by norm_num)
    · exfalso
      have := hcardne (le_sup_right : N ≤ H ⊔ N)
      rw [h, hHc, hNc] at this
      exact absurd this (by norm_num)
    · exfalso
      have := hcardne (le_sup_left : H ≤ H ⊔ N)
      rw [h, hHc, hNc] at this
      exact absurd this (by norm_num)
    · exact h
  · intro Y hY hYc
    rcases hlat Y hY with rfl | rfl | rfl | rfl
    · rw [hUc, hHc] at hYc
      exact absurd hYc (by norm_num)
    · rfl
    · rw [hNc, hHc] at hYc
      exact absurd hYc (by norm_num)
    · exact absurd (Subgroup.eq_top_of_card_eq H (by simpa using hYc.symm)) hHtop
  · intro Y hY hYc
    rcases hlat Y hY with rfl | rfl | rfl | rfl
    · rw [hUc, hNc] at hYc
      exact absurd hYc (by norm_num)
    · rw [hHc, hNc] at hYc
      exact absurd hYc (by norm_num)
    · rfl
    · exact absurd (Subgroup.eq_top_of_card_eq N (by simpa using hYc.symm)) hNtop

theorem nParam_eq_one_of_isTits {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hTits : IsTits (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  refine le_antisymm (nParam_le_one_of_hasSolvInvPair (hasSolvInvPair_tits hTits) hLn
    (MulEquiv.refl _) hTs hFT) ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥(CFSG.generalizedFitting G)))
  obtain ⟨H, N, hUc, -⟩ := titsSylowOvergroupLattice _ hTits _
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀)
  have hev : 2 ∣ Nat.card (CFSG.generalizedFitting G) := by
    have := Subgroup.card_subgroup_dvd_card (P₀ : Subgroup ↥(CFSG.generalizedFitting G))
    rw [hUc] at this
    exact dvd_trans (by norm_num) this
  exact Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) hev)

end Tits

end CFSG.Quasithin.RonanE114
