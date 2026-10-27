module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU33Tools
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

namespace Res423Two

open Item434CharThree

theorem exists_map_le_lineSub {e : ℕ} (he : e ≠ 0) {X : Type} [Group X] [Finite X]
    (θ : X ≃* SL(3, GaloisField 3 e)) {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) :
    ∃ (g : SL(3, GaloisField 3 e)) (a₀ b₀ : GaloisField 3 e), (a₀ ≠ 0 ∨ b₀ ≠ 0) ∧
      D.map (θ.trans (MulAut.conj g⁻¹)).toMonoidHom ≤ lineSub a₀ b₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite SL(3, GaloisField 3 e) := Finite.of_injective _ Subtype.val_injective
  have hD' : CFSG.Assembly.IsElemAbelian 3 (D.map θ.toMonoidHom) := isElemAbelian_map' _ hD
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := heis (GaloisField 3 e))
    (by rw [card_heis, GaloisField.card 3 e he, factorization_card_SL_three he, ← pow_mul,
      mul_comm])
    (Sec5.isPGroup_of_isElemAbelian hD')
  have hle : (D.map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom ≤ heis (GaloisField 3 e) :=
    Item434AltPerm.map_conj_inv_le hg
  have hmap : D.map (θ.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (D.map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  obtain ⟨a₀, b₀, hab, hR⟩ := exists_le_lineSub hle
    (comm_of_isElemAbelian (isElemAbelian_map' _ hD'))
  exact ⟨g, a₀, b₀, hab, hmap ▸ hR⟩

theorem census423_of_l33 {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projSL 3 (GaloisField 3 1)) : Census423 X := by
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by rw [GaloisField.card 3 1 one_ne_zero, pow_one]
  refine census423_of_alphaVanishes fun D hD hD9 => ?_
  set θ : X ≃* SL(3, GaloisField 3 1) := e.trans (slEquivProjSL (GaloisField 3 1)).symm
  obtain ⟨g, a₀, b₀, hab, hle⟩ := exists_map_le_lineSub one_ne_zero θ hD.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  have heq : D.map e'.toMonoidHom = lineSub a₀ b₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_lineSub hab, hK3, Subgroup.card_map_of_injective e'.injective, hD9]
    norm_num
  refine alphaVanishes_of_noSignalizer_mulEquiv hZ e' (comm_of_isElemAbelian hD.prop)
    (ne_bot_of_card_nine hD9) fun Q hQ hN => ?_
  rw [heq] at hN
  exact eq_bot_of_le_normalizer_three hab hQ hN

theorem false_of_le_card_eighty_one {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) {E : Subgroup X} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hDE : D ≤ E)
    (hE81 : 81 ≤ Nat.card E) : False := by
  have h1 := Subgroup.card_le_of_le (hD.2 hE hDE)
  omega

theorem census423_of_l39 {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 3 (GaloisField 3 2)) : Census423 X := by
  have hK9 : Nat.card (GaloisField 3 2) = 9 := by rw [GaloisField.card 3 2 two_ne_zero]; norm_num
  intro D hD hD9
  exfalso
  set θ : X ≃* SL(3, GaloisField 3 2) := e.trans (slEquivProjSL (GaloisField 3 2)).symm
  obtain ⟨g, a₀, b₀, hab, hle⟩ := exists_map_le_lineSub two_ne_zero θ hD.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  refine false_of_le_card_eighty_one hD hD9 (E := (lineSub a₀ b₀).map e'.symm.toMonoidHom)
    (isElemAbelian_map' _ (isElemAbelian_lineSub a₀ b₀)) ?_ ?_
  · intro x hx
    exact ⟨e' x, hle ⟨x, hx, rfl⟩, e'.symm_apply_apply x⟩
  · rw [Subgroup.card_map_of_injective e'.symm.injective, card_lineSub hab, hK9]
    norm_num

theorem exists_map_le_lineU {e : ℕ} (he : e ≠ 0) {X : Type} [Group X] [Finite X]
    (θ : X ≃* SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) {D : Subgroup X}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) :
    ∃ (g : SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) (a₀ : GaloisField 3 (2 * e)),
      a₀ ≠ 0 ∧ D.map (θ.trans (MulAut.conj g⁻¹)).toMonoidHom ≤
        lineU (unitaryInvolution_involutive (card_galois_two_mul he)) a₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) :=
    Finite.of_injective _ Subtype.val_injective
  have hD' : CFSG.Assembly.IsElemAbelian 3 (D.map θ.toMonoidHom) := isElemAbelian_map' _ hD
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := heisU (unitaryInvolution_involutive (card_galois_two_mul he)))
    (by rw [card_heisU (card_galois_two_mul he), factorization_card_SU_three he, ← pow_mul,
      mul_comm])
    (Sec5.isPGroup_of_isElemAbelian hD')
  have hle : (D.map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom ≤
      heisU (unitaryInvolution_involutive (card_galois_two_mul he)) :=
    Item434AltPerm.map_conj_inv_le hg
  have hmap : D.map (θ.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (D.map θ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  obtain ⟨a₀, ha₀, hR⟩ := exists_le_lineU hle (comm_of_isElemAbelian (isElemAbelian_map' _ hD'))
  exact ⟨g, a₀, ha₀, hmap ▸ hR⟩

theorem census423_of_u33 {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projSU 3 3 1) : Census423 X := by
  have hF := card_galois_two_mul (e := 1) one_ne_zero
  refine census423_of_alphaVanishes fun D hD hD9 => ?_
  set θ : X ≃* SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3 :=
    e.trans (suEquivProjSU one_ne_zero).symm
  obtain ⟨g, a₀, ha₀, hle⟩ := exists_map_le_lineU one_ne_zero θ hD.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  have heq : D.map e'.toMonoidHom = lineU (unitaryInvolution_involutive hF) a₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h9 := card_lineU_le hF ha₀
    rw [Subgroup.card_map_of_injective e'.injective, hD9]
    norm_num at h9
    exact h9
  have hinj := Item434Kit.conj_injective_of_center_eq_bot (center_eq_bot_of_mulEquiv hZ θ)
  refine alphaVanishes_of_noSignalizer_mulEquiv hZ e' (comm_of_isElemAbelian hD.prop)
    (ne_bot_of_card_nine hD9) fun Q hQ hN => ?_
  rw [heq] at hN
  exact eq_bot_of_le_normalizer_unitary_three hF hinj ha₀ hQ hN

theorem census423_of_u39 {X : Type} [Group X] [Finite X] (e : X ≃* projSU 3 3 2) :
    Census423 X := by
  have hF := card_galois_two_mul (e := 2) two_ne_zero
  intro D hD hD9
  exfalso
  set θ : X ≃* SU (unitaryInvolution (GaloisField 3 (2 * 2)) 3 2) 3 :=
    e.trans (suEquivProjSU two_ne_zero).symm
  obtain ⟨g, a₀, ha₀, hle⟩ := exists_map_le_lineU two_ne_zero θ hD.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  refine false_of_le_card_eighty_one hD hD9
    (E := (lineU (unitaryInvolution_involutive hF) a₀).map e'.symm.toMonoidHom)
    (isElemAbelian_map' _ (isElemAbelian_lineU a₀)) ?_ ?_
  · intro x hx
    exact ⟨e' x, hle ⟨x, hx, rfl⟩, e'.symm_apply_apply x⟩
  · rw [Subgroup.card_map_of_injective e'.symm.injective]
    have h81 := card_lineU_ge hF ha₀
    norm_num at h81
    exact h81

end Res423Two

open Res423Two

@[expose] def K423Inner46EightRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))) → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

theorem k423Inner46Eight_of (h : K423Inner46EightRest) : K423Inner46Eight := by
  rintro X _ _ hX hq hZ hSL
  rcases hX with ⟨e, he1, he2, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | hX | hX
  · interval_cases e
    · exact census423_of_l33 hZ φ
    · exact census423_of_l39 φ
  · interval_cases e
    · exact census423_of_u33 hZ φ
    · exact census423_of_u39 φ
  · exact h X (Or.inl hX) hq hZ hSL
  · exact h X (Or.inr hX) hq hZ hSL

end CFSG.RankThree.PartTwo.Sec4
