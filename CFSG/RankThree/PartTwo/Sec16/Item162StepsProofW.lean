module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire16
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162WO2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₁ Y₂ S : Subgroup G),
    Sec15R G A c L → Conf162 A (lB A) c L Y₁ Y₂ S →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ →
        CFSG.Open.pCoreOf 2 Y₂ ≤ (L ⊓ Y₂) ⊔ S

namespace Proof162

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem not_transOmegaThree_of_le {c : G}
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ¬ TransOmegaThree A c := by
  rintro ⟨h3, hall⟩
  have hsub : omegaA A ⊆ {Subgroup.zpowers c} := by
    intro F hF
    obtain ⟨w, hw, rfl⟩ := hall F hF
    rw [Set.mem_singleton_iff]
    exact Late.map_conj_eq_of_mem_normalizer (hWH hw)
  have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [h3, Set.ncard_singleton] at hle
  omega

theorem not_normalizer_le_of_conf162 {c : G} {L Y₁ Y₂ S : Subgroup G}
    (h1514 : Item1514 A (lB A) c L) (hconf : Conf162 A (lB A) c L Y₁ Y₂ S)
    (hO2 : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ → CFSG.Open.pCoreOf 2 Y₂ ≤ (L ⊓ Y₂) ⊔ S) :
    ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro hWH
  have hcov : Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
    rcases h1514 Y₂ hconf.maxCE.1.mem₂ hconf.meets₂ with
      ⟨hY, -⟩ | ⟨-, -, hT, -⟩ | ⟨-, -, hY, -⟩
    · exact hY
    · exact absurd hT (not_transOmegaThree_of_le hWH)
    · exact hY
  have hO := hO2 hWH hcov
  have hSY₁ : S ≤ Subgroup.normalizer (Y₁ : Set G) := hconf.maxCE.1.s₁.prop.1.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hconf.maxCE.1.s₁.prop
  have hLY : L ≤ S ⊔ Y₁ := hconf.le_y.trans le_sup_right
  have hle : Y₂ ≤ S ⊔ Y₁ := by
    calc Y₂ = (Y₂ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₂ := hcov
      _ ≤ S ⊔ Y₁ :=
        sup_le (inf_le_right.trans hLY) (hO.trans (sup_le (inf_le_left.trans hLY) le_sup_left))
  have hY₂Y₁ : Y₂ ≤ Y₁ :=
    le_of_le_sup_of_isPGroup_two hSY₁ hS2 hle hconf.maxCE.1.mem₂.prop.1.2.1
  have heq : Y₂ = Y₁ := hconf.maxCE.1.mem₂.eq_of_le hconf.maxCE.1.mem₁.prop hY₂Y₁
  exact hconf.maxCE.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one, heq]⟩

end Proof162

theorem step162WR_of (h1514 : Item1514R) (hO2 : Step162WO2) : Step162WR := by
  intro G _ _ A c₀ L₀ _ c L Y₁ Y₂ S hR hconf
  exact Proof162.not_normalizer_le_of_conf162 (h1514 G A c L hR) hconf
    (hO2 G A c L Y₁ Y₂ S hR hconf)

end CFSG.RankThree.PartTwo.Sec16
