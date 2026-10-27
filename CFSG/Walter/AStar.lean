module

public import CFSG.Walter.AStar.Components
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Walter

@[expose] def SimpleCaseHyp : Prop := ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
  (∃ a b : L, a * b ≠ b * a) → HasAbelianSylowTwo L →
  (∀ H : Subgroup L, H ≠ ⊤ → IsAStar H) → IsTypeL2 L ∨ IsTypeJR L

theorem isAStar_of_hasAbelianSylowTwo (hSC : SimpleCaseHyp) {X : Type} [Group X] [Finite X]
    (hX : HasAbelianSylowTwo X) : IsAStar X := by
  suffices h : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X], Nat.card X = n →
      HasAbelianSylowTwo X → IsAStar X from h _ X rfl hX
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hY : HasAbelianSylowTwo (X ⧸ pPrimeCore 2 X) := hX.quotient _
  refine ⟨hX, odd_index_generalizedFittingSubgroupOf hO hY, ?_⟩
  intro K hK
  refine ⟨center_eq_bot_of_isComponentOf hO hY hK, ?_⟩
  have hKs := isSimpleGroup_of_isComponentOf hO hY hK
  refine hSC K hKs (nonabelian_of_isComponentOf hK) (hY.subgroup K) ?_
  intro H hH
  have hlt : Nat.card H < n := by
    calc Nat.card H < Nat.card (⊤ : Subgroup K) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
      _ = Nat.card K := Subgroup.card_top
      _ ≤ Nat.card (X ⧸ pPrimeCore 2 X) := Subgroup.card_le_card_group K
      _ ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      _ = n := hn
  exact ih _ hlt H rfl ((hY.subgroup K).subgroup H)

end CFSG.Walter
