module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightU3
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightG2

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

@[expose] def K424Inner46EightRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)) →
    IsQuasisimple X → Subgroup.center X = ⊥ → Census424 X

namespace Item424Res2

open Res423Two Item434CharThree

theorem census424_of_l39 {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 3 (GaloisField 3 2)) : Census424 X := by
  have hK9 : Nat.card (GaloisField 3 2) = 9 := by rw [GaloisField.card 3 2 two_ne_zero]; norm_num
  intro D c d K h
  exfalso
  set θ : X ≃* SL(3, GaloisField 3 2) := e.trans (slEquivProjSL (GaloisField 3 2)).symm
  obtain ⟨g, a₀, b₀, hab, hle⟩ := exists_map_le_lineSub two_ne_zero θ h.maximal.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  refine false_of_le_card_eighty_one h.maximal h.card_eq
    (E := (lineSub a₀ b₀).map e'.symm.toMonoidHom)
    (isElemAbelian_map' _ (isElemAbelian_lineSub a₀ b₀)) ?_ ?_
  · intro x hx
    exact ⟨e' x, hle ⟨x, hx, rfl⟩, e'.symm_apply_apply x⟩
  · rw [Subgroup.card_map_of_injective e'.symm.injective, card_lineSub hab, hK9]
    norm_num

theorem census424_of_u39 {X : Type} [Group X] [Finite X] (e : X ≃* projSU 3 3 2) :
    Census424 X := by
  have hF := card_galois_two_mul (e := 2) two_ne_zero
  intro D c d K h
  exfalso
  set θ : X ≃* SU (unitaryInvolution (GaloisField 3 (2 * 2)) 3 2) 3 :=
    e.trans (suEquivProjSU two_ne_zero).symm
  obtain ⟨g, a₀, ha₀, hle⟩ := exists_map_le_lineU two_ne_zero θ h.maximal.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  refine false_of_le_card_eighty_one h.maximal h.card_eq
    (E := (lineU (unitaryInvolution_involutive hF) a₀).map e'.symm.toMonoidHom)
    (isElemAbelian_map' _ (isElemAbelian_lineU a₀)) ?_ ?_
  · intro x hx
    exact ⟨e' x, hle ⟨x, hx, rfl⟩, e'.symm_apply_apply x⟩
  · rw [Subgroup.card_map_of_injective e'.symm.injective]
    have h81 := card_lineU_ge hF ha₀
    norm_num at h81
    exact h81

end Item424Res2

open Item424Res2

theorem k424Inner46Eight_of
    (h : K424Inner46EightRest) : K424Inner46Eight := by
  rintro X _ _ hX hq hZ -
  rcases hX with ⟨e, he1, he2, hl | hu⟩ | hX | ⟨-, hG | hU⟩
  · interval_cases e
    · obtain ⟨φ⟩ := hl
      exact census424_of_l33 φ
    · obtain ⟨φ⟩ := hl
      exact census424_of_l39 φ
  · interval_cases e
    · obtain ⟨φ⟩ := hu
      exact census424_of_u33 φ
    · obtain ⟨φ⟩ := hu
      exact census424_of_u39 φ
  · exact h X (Or.inl hX) hq hZ
  · exact census424_of_g2_three hZ hG
  · exact h X (Or.inr hU) hq hZ

end CFSG.RankThree.PartTwo.Sec4
