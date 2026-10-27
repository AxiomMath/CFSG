module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIb
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwo3
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLe

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str86_caseII_false
    {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hU3 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) : False := by
  classical
  obtain ⟨m, hL2⟩ := h2
  have hm : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  by_cases hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ = ⊥
  swap
  · exact str86_caseIIb_false hF.toW hSB (Or.inr hU3) hB2 ⟨m, hL2⟩ hII hJZ
  have hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    (caseII_split hF.toW hSB (Or.inr hU3) hL2 hm hII).1 hJZ
  by_cases hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S
  swap
  · exact str86_caseIIa_notLe_false hF hSB hU3 hB2 ⟨m, hL2⟩ hII hIIa hZ
  obtain ⟨k, hk, F, hFld, hFin, hFc, hU3'⟩ := hU3
  letI : Field F := hFld
  letI : Finite F := hFin
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) := str86_isSzU3Quot_of_statedSU hk hFc hU3'
  have hN : IsNormalIn (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (le_normalizer_conjClosure (Z1 L1 L2 S) (L2 ⊔ S))
  obtain ⟨c, hc⟩ := D15Proof.exists_isChiefSeriesFrom (H := L2 ⊔ S) (U := str86U L1 L2 S)
    (str86U L1 L2 S) hN
  have hc2 : c ≤ 2 := str86_caseIIa_chief_le_two hF hSB hq hm hL2 hII hZ hc
  rcases Nat.lt_or_ge c 2 with hlt | hge
  · exact str86_caseIIa_chief_le_one_false hF hSB hq hm hL2 hII hIIa hZ hc (by omega)
  · obtain rfl : c = 2 := le_antisymm hc2 hge
    exact str86_caseIIa_two_false hF hSB hk hFc hU3' hB2 hL2 hII hIIa hZ hc

theorem str86CaseI_holds :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
      VU3Big L1 → VBig L2 → VL2 L2 →
        L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  intro G _ _ L1 L2 S hF hSB hU3 hB2 h2
  by_contra hII
  exact str86_caseII_false hF hSB hU3 hB2 h2 hII

end CFSG.Quasithin.Stroth

end
