module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocZSNR1
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Bang
public import CFSG.Quasithin.EmptyFaithful.S1421STC3Defs

public section

namespace CFSG.Quasithin.SzSurvLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem hZS_of_nonab_setting1427 (h209 : Lemma14209Used)
    (h311 : Theorem311) {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}
    (st : Setting1427 T M H K1) (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1)
    (hf : CharTwo (S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 ⊔
      borelOf K1 (S1421.sOf T K1)))
    (h15 : pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) = ⊥)
    (hna : ⁅vBeta K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) (quasithinOmegaOneCenter T),
      vBeta K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)
        (quasithinOmegaOneCenter T)⁆ ≠ ⊥) :
    ∀ u ∈ S1421.sOf T K1, u * u = 1 → (∀ s ∈ S1421.sOf T K1, u * s = s * u) →
      u ∈ quasithinOmegaOneCenter T := by
  by_cases hS : S1421.sOf T K1 = T
  · exact S1421.hZS_of_eq hS
  · have hlt : S1421.sOf T K1 < T := lt_of_le_of_ne S1421.sOf_le_T hS
    have hset := S1421.r1Setting_of_setting1427_legacyBare h311 st h13 hf h15
      (fun _ _ h => isL2Quot_one_iff_perm3.mpr h)
    obtain ⟨Kc, hKc, -, hKT, -⟩ := h209 G T M H K1 st hlt
    have hKZ : K1 ≤ Subgroup.centralizer (omegaOneCenterOf (S1421.sOf T K1) : Set G) :=
      fun x hx => S1421.oTwoUpper_le_centralizer_omegaOneCenter_sOf st hlt hKc hKT
        (st.notation_.le_K hx)
    exact hZS_of_nonab hset st.notation_.bender hKZ hna

end CFSG.Quasithin.SzSurvLoc
