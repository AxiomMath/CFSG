module

public import CFSG.Quasithin.Recognition.F112IdentW
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalGlue
import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalGlue
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalIdent

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Stroth

@[expose] def St84LLLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (m n : ℕ),
    F112HypW L1 L2 S → 2 ≤ m → 2 ≤ n → ¬ (m = 2 ∧ n = 2) →
      IsL2Quot m (oTwoQuot ↥L1) → IsL2Quot n (oTwoQuot ↥L2) →
        (m = n ∧ (L3qLocalData L1 L2 S n ∨ Sp4qLocalData L1 L2 S n ∨
            G2qLocalData L1 L2 S n ∨ G2qLocalData L2 L1 S n)) ∨
          (m = 3 * n ∧ D4qLocalData L1 L2 S n) ∨ (n = 3 * m ∧ D4qLocalData L2 L1 S m) ∨
          (n = 2 * m ∧ U4qLocalData L1 L2 S m) ∨ (m = 2 * n ∧ U4qLocalData L2 L1 S n)

@[expose] def G2qIdent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112HypW L1 L2 S → 3 ≤ f → IsL2Quot f (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      G2qLocalData L1 L2 S f → IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over f)

@[expose] def D4qIdent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (f : ℕ),
    F112HypW L1 L2 S → 2 ≤ f → IsL2Quot (3 * f) (oTwoQuot ↥L1) → IsL2Quot f (oTwoQuot ↥L2) →
      D4qLocalData L1 L2 S f →
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f)

theorem idL2L2GenW_of_parts (hV : St84LLLocal) (hG2 : G2qIdent) (hD4 : D4qIdent) :
    IdL2L2GenW := by
  intro G _ _ L1 L2 S m n hF hm hn hmn h1 h2
  rcases hV G L1 L2 S m n hF hm hn hmn h1 h2 with
    ⟨rfl, hD | hD | hD | hD⟩ | ⟨he, hD⟩ | ⟨he, hD⟩ | ⟨he, hD⟩ | ⟨he, hD⟩
  · exact Or.inl ⟨rfl, Or.inl (isAmalgamOfGroup_psl3_of_l3qLocalData (by omega) hF.1 hD)⟩
  · exact Or.inl ⟨rfl, Or.inr (Or.inl (isAmalgamOfGroup_sp4_of_sp4qLocalData (by omega) hF.1 hD))⟩
  · exact Or.inl ⟨rfl, Or.inr (Or.inr (hG2 G L1 L2 S m hF (by omega) h1 h2 hD))⟩
  · exact Or.inl ⟨rfl, Or.inr (Or.inr
      (isAmalgamOfGroup_f112Amalgam_swap (hG2 G L2 L1 S m hF.symm (by omega) h2 h1 hD)))⟩
  · exact Or.inr (Or.inl ⟨he, hD4 G L1 L2 S n hF hn (he ▸ h1) h2 hD⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨he, hD4 G L2 L1 S m hF.symm hm (he ▸ h2) h1 hD⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨he, isAmalgamOfGroup_psu4_or_isU4ExtTwo hm hF.1 hD⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨he, isAmalgamOfGroup_psu4_or_isU4ExtTwo hn hF.1.symm hD⟩)))

end CFSG.Quasithin.F112R.St84

end
