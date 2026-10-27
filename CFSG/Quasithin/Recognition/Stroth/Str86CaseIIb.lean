module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIbOffender
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIbGen
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIbBaum
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIPushUp3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIb_false
    {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ ≠ ⊥) : False := by
  classical
  obtain ⟨m, hL2⟩ := h2
  have hm : 2 ≤ m :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hCZ : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S :=
    str86_inf_centralizer_z2_of_caseIIb hF hSB hm hL2 hII hJZ
  obtain ⟨A, hA, -, hAr, hZA, heq⟩ :=
    str86_caseIIb_offender hF hSB hm hL2 hII hJZ
  obtain ⟨g, hg, hK⟩ :=
    str86_caseIIb_generation hF hSB hm hL2 hA.1 hA.2.1 hAr
  have hZK : (2 ^ m) ^ 2 ≤ (Z2 L1 L2 S ⊓ Subgroup.centralizer
      ((A ⊔ conjSubgroup A g : Subgroup G) : Set G)).relIndex (Z2 L1 L2 S) :=
    str86_caseIIb_sq_le_relIndex hF hSB hm hL2 hII hJZ hK
  have hR : P2 L1 L2 S ≤
      Subgroup.normalizer ((baum S ⊓ Q2 L1 L2 S : Subgroup G) : Set G) :=
    str86_caseIIb_baum_inf_normal hF hSB hCZ hA (le_of_eq hZA) heq hg hK hZK
  refine str86_false_of_pushUp hF hSB hB1 hB2 ⟨m, hL2⟩
    (hF.1.h1.pgroup.to_le (show baum S ≤ S from inf_le_left)) ?_ ?_ ?_ hR
  · calc baum S ≤ S := inf_le_left
      _ ≤ bigB L1 L2 S := le_sup_right
      _ ≤ P1 L1 L2 S := le_sup_right
  · exact P1_le_normalizer_baum_of_caseII hF hSB hB1 hII
  · intro hbQ
    exact not_thompsonJ_le_Q2_of_caseII hF hSB hB1 hII
      ((CFSG.Quasithin.B6.thompsonJ_le_baum S).trans hbQ)

end CFSG.Quasithin.Stroth

end
