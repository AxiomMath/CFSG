module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelAssembly
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem charTwo_titsHD : CharTwo titsHD := by
  obtain ⟨-, -, -, -, -, -, hJn, -, -, -, hCJ, -⟩ := AT_Tits_intrinsic_local_pair
  refine charTwo_of_index_le_two (X := titsHD) (J := titsJD) le_rfl
    (by rw [Subgroup.relIndex_self]; norm_num) ?_ (fun _ hx => titsJ_le_titsH hx)
    (titsD_le_normalizer_of_normal titsJ_le_titsH hJn)
    (inf_centralizer_subgroupOf_le titsJ_le_titsD hCJ)
  exact IsPGroup.of_card (n := 9) (by rw [card_titsJD]; norm_num)

theorem charTwo_titsND : CharTwo titsND := by
  obtain ⟨-, -, -, -, -, -, -, hKn, -, -, -, hCK⟩ := AT_Tits_intrinsic_local_pair
  refine charTwo_of_index_le_two (X := titsND) (J := titsKD) le_rfl
    (by rw [Subgroup.relIndex_self]; norm_num) ?_ (fun _ hx => titsK_le_titsN hx)
    (titsD_le_normalizer_of_normal titsK_le_titsN hKn)
    (inf_centralizer_subgroupOf_le titsK_le_titsD hCK)
  exact IsPGroup.of_card (n := 10) (by rw [card_titsKD]; norm_num)

theorem card_pCoreOf_titsHD : Nat.card (pCoreOf 2 titsHD) = 2 ^ 9 := by
  rw [card_pCoreOf_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe titsH_le_titsD), card_pCoreOf_titsH]
  norm_num

theorem modelFacts_tits :
    ∃ (Y : Type) (_ : Group Y) (T M₁ M₂ : Subgroup Y), Nonempty (Y ≃* quasithinTits) ∧
      IsYAmalgamPair T M₁ M₂ ∧ Hyp53 (GoldAmalgam.ofSubgroupPair M₁ M₂) ∧
      Nat.card ↥(M₁ ⊓ M₂) = 2 ^ 11 ∧ Nat.card ↥(pCoreOf 2 M₁) = 2 ^ 9 ∧
      Nat.card ↥(pCoreOf 2 M₂) = 2 ^ 10 := by
  have hS : Nat.card titsTwoLocalLattice.S = 2 ^ 11 := by
    change Nat.card titsSD = 2 ^ 11
    rw [card_titsSD]
    norm_num
  have h₁ : Nat.card titsTwoLocalLattice.P₁ = 5 * 2 ^ 11 := by
    change Nat.card titsHD = 5 * 2 ^ 11
    rw [card_titsHD]
    norm_num
  have h₂ : Nat.card titsTwoLocalLattice.P₂ = 3 * 2 ^ 11 := by
    change Nat.card titsND = 3 * 2 ^ 11
    rw [card_titsND]
    norm_num
  have hO₁ : 4 * Nat.card (pCoreOf 2 titsTwoLocalLattice.P₁) = 2 ^ 11 := by
    change 4 * Nat.card (pCoreOf 2 titsHD) = 2 ^ 11
    rw [card_pCoreOf_titsHD]
    norm_num
  obtain ⟨h53, hinf, hO₂⟩ := hyp53_of_lattice titsTwoLocalLattice hS h₁ h₂ charTwo_titsHD
    charTwo_titsND hO₁
  refine ⟨↥titsD, inferInstance, titsTwoLocalLattice.S, titsTwoLocalLattice.P₁,
    titsTwoLocalLattice.P₂, ⟨quasithinTitsEquivD.symm⟩, isYAmalgamPair_lattice _, h53, hinf, ?_,
    ?_⟩
  · change Nat.card (pCoreOf 2 titsHD) = 2 ^ 9
    exact card_pCoreOf_titsHD
  · omega

end CFSG.Quasithin.Fan86.Model
