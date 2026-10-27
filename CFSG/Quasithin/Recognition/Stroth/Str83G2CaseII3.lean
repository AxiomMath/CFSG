module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIb

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83_caseII2_false
    {L1 L2 S : Subgroup G} {a : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a)) (hB2 : VBig L2) (h2 : VL2 L2)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hII2 : ¬ L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G)) : False := by
  obtain ⟨m, hL2⟩ := h2
  have hm : 2 ≤ m :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ ≠ ⊥ := by
    intro hcomm
    apply hII2
    rw [hsup2]
    exact (caseII_split hF hB hB1 hL2 hm hII).mp hcomm
  exact str86_caseIIb_false hF hB hB1 hB2 ⟨m, hL2⟩ hII hJZ

end CFSG.Quasithin.Stroth

end
