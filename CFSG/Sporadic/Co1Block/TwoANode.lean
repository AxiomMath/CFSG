module

public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.Classes
public import CFSG.Sporadic.Co1Block.CompQuot

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier

theorem isConj_aC_of_ncard_fix
    {t : GA} (ht : orderOf t = 2)
    (hfix : (xFix (t : GL24)).ncard = 2280) : IsConj t aC := by
  rcases involution_classes.1 t ht with h | h | h
  · exact h
  · rw [← ncard_fix_isConj h, ncard_fix_cC] at hfix
    norm_num at hfix
  · rw [← ncard_fix_isConj h, ncard_fix_a₁] at hfix
    norm_num at hfix

theorem selfCentralizing_aC :
    ∃ Q : Subgroup (Subgroup.centralizer ({aC} : Set GA)), Q.Normal ∧ Nat.card Q = 512 ∧
      Subgroup.centralizer (Q : Set (Subgroup.centralizer ({aC} : Set GA))) ≤ Q ∧
      ∀ B : Subgroup (Subgroup.centralizer ({aC} : Set GA)), ¬ CFSG.IsComponent B := by
  obtain ⟨Q, h1, h2, h3, h4⟩ := selfCentralizing_of_GL (t := aC) (Q := twoAQ) (n := 9)
    (by rw [coe_aC]; exact twoAQ_le) (by rw [coe_aC]; exact twoAQ_normal)
    (by rw [coe_aC]; exact twoA_selfCentralizing) (by rw [card_twoAQ]; norm_num)
  exact ⟨Q, h1, by rw [h2]; norm_num, h3, h4⟩

theorem cti_co1_2280_fixed_point_centralizer_has_no_components
    {t : GA} (ht : orderOf t = 2)
    (hfix : (xFix (t : GL24)).ncard = 2280) :
    ∃ Q : Subgroup (Subgroup.centralizer ({t} : Set GA)), Q.Normal ∧ Nat.card Q = 512 ∧
      Subgroup.centralizer (Q : Set (Subgroup.centralizer ({t} : Set GA))) ≤ Q ∧
      ∀ B : Subgroup (Subgroup.centralizer ({t} : Set GA)), ¬ CFSG.IsComponent B :=
  selfCentralizing_of_isConj (isConj_aC_of_ncard_fix ht hfix).symm selfCentralizing_aC

end CFSG.Sporadic.Co1Block
