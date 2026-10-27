module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem not_thompsonJ_le_q1_inf_q2 (hF : Hyp111 L1 L2 S) :
    ¬ thompsonJ S ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  intro hJ
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF
  have hJ2 : IsPGroup 2 (thompsonJ S) := hF.h1.pgroup.to_le (thompsonJ_le_self S)
  have hPN : ∀ {P : Subgroup G}, IsSylowTwoOf S P → thompsonJ S ≤ pCoreOf 2 P →
      P ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    intro P hSP hJQ
    have hQS : pCoreOf 2 P ≤ S := F7.isSylowTwoOf_pCoreOf_le hSP
    have hJeq : thompsonJ S = thompsonJ (pCoreOf 2 P) := thompsonJ_eq_of_le hJQ hQS
    have hchar : ((thompsonJ (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P)).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (pCoreOf 2 P)
    have hmap : ((thompsonJ (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P)).map
        (pCoreOf 2 P).subtype = thompsonJ S := by
      rw [Subgroup.map_subgroupOf_eq_of_le (thompsonJ_le_self (pCoreOf 2 P))]
      exact hJeq.symm
    have h := (le_normalizer_pCoreOf 2 P).trans
      (normalizer_le_normalizer_map_of_characteristic
        ((thompsonJ (pCoreOf 2 P)).subgroupOf (pCoreOf 2 P)))
    rwa [hmap] at h
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le (hPN (F112W.isSylowTwoOf_parabolic hR) (hJ.trans inf_le_left))
      (hPN (F112W.isSylowTwoOf_parabolic' hR) (hJ.trans inf_le_right))
  have hJleO : thompsonJ S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 ((thompsonJ_le_self S).trans le_sup_right) hG0N hJ2
  rw [hF.o2] at hJleO
  have hSne : S ≠ ⊥ := by
    intro hS
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF
      (le_bot_iff.mp (by simpa [hS] using A4.omegaOneCenterOf_le S))
  exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hF.h1.pgroup hSne (le_bot_iff.mp hJleO)

end CFSG.Quasithin.Stroth

end
