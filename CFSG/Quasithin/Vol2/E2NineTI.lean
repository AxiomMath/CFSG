module

public import CFSG.Quasithin.Vol2.E2NinePullback
public import CFSG.Quasithin.Vol2.E2SevenStatement

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AS_E_2_9_nStarTI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V →
    IsTISetIn V M → E1.nParam (⊤ : Subgroup (E2.StarQuot M H)) = E1.nParam H

@[expose] def AS_E_2_9CTI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V : Subgroup G), E2.Hyp28 H T M V →
    IsTISetIn V M →
    (¬ IsL33Exception (⊤ : Subgroup (E2.StarQuot M H)) (E2.star M H V) →
      ∃ I : Subgroup G, IsInIHTVC H T M V I) ∧
    ∀ I : Subgroup G, IsInIHTVC H T M V I →
      (⁅kerIn M H, I⁆ ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ Subgroup.normalizer (I : Set G) ∧
        kerIn M H ≤ Subgroup.normalizer (oTwoUpper I : Set G)) ∧
      (CharTwo H → CharTwo I)

end CFSG.Quasithin.ASInputs

namespace CFSG.Quasithin

theorem ASInputs.as_E_2_9CTI_of (h27 : ASInputs.AS_E_2_7C) (hsq : ASInputs.AS_E_2_9_starSQTK)
    (hn : ASInputs.AS_E_2_9_nStarTI) : ASInputs.AS_E_2_9CTI := by
  intro G _ _ H T M V h hTI
  refine ⟨fun hL => ?_, fun I hI => ASInputs.e2_9C_members h hI⟩
  have := E2P.finite_starQuot M H
  obtain ⟨I₀, hI₀⟩ := h27 (E2.StarQuot M H) ⊤ (E2.star M H T) (E2.star M H M) (E2.star M H V)
    (h.star (hsq G H T M V h)) (E2P.kerIn_star M H) hL
  exact E2.exists_isInIHTVC_of_star h (hn G H T M V h hTI) hI₀

end CFSG.Quasithin
