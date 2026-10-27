module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofU54
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Matrix
open scoped MatrixGroups

@[expose] def K424Inner46SevenSp62 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSp 3 (GaloisField 2 1)) → Census424 X

namespace Item424Res2

@[expose] noncomputable def slCongr {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    SpecialLinearGroup n R ≃* SpecialLinearGroup n S where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' A B := map_mul _ A B

@[expose] def tvZ {i j : Fin 5} (h : i ≠ j) : SL(5, ZMod 2) := SpecialLinearGroup.transvection h 1

@[expose] def swZ {i j : Fin 5} (h : i ≠ j) : SL(5, ZMod 2) := tvZ h * tvZ h.symm * tvZ h

@[expose] def l52T1 : SL(5, ZMod 2) :=
  tvZ (show (0 : Fin 5) ≠ 1 by decide) * tvZ (show (1 : Fin 5) ≠ 0 by decide)

@[expose] def l52T2 : SL(5, ZMod 2) :=
  tvZ (show (2 : Fin 5) ≠ 3 by decide) * tvZ (show (3 : Fin 5) ≠ 2 by decide)

@[expose] def l52R : SL(5, ZMod 2) :=
  swZ (show (0 : Fin 5) ≠ 2 by decide) * swZ (show (1 : Fin 5) ≠ 3 by decide) *
    swZ (show (0 : Fin 5) ≠ 1 by decide)

theorem l52_facts : l52T1 ^ 3 = 1 ∧ l52T1 ≠ 1 ∧ l52T2 ^ 3 = 1 ∧ l52T1 * l52T2 = l52T2 * l52T1 ∧
    (l52T2 ≠ 1 ∧ l52T2 ≠ l52T1 ∧ l52T2 ≠ l52T1 ^ 2) ∧
    l52R * l52T1 * l52R⁻¹ = l52T2 ^ 2 ∧ l52R * l52T2 * l52R⁻¹ = l52T1 ∧ l52R ^ 4 = 1 ∧
    l52R ^ 2 * l52T1 * (l52R ^ 2)⁻¹ ≠ l52T1 := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem eq_of_mem_zpowers_of_pow_three {H : Type*} [Group H] {p x : H} (hp : p ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers p) : x = 1 ∨ x = p ∨ x = p ^ 2 := by
  obtain ⟨k, rfl⟩ := hx
  change p ^ k = 1 ∨ p ^ k = p ∨ p ^ k = p ^ 2
  rw [zpow_eq_zpow_emod' k hp]
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · exact Or.inl (zpow_zero p)
  · exact Or.inr (Or.inl (zpow_one p))
  · exact Or.inr (Or.inr (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]))

@[expose] def l52F : Subgroup SL(5, ZMod 2) := Subgroup.zpowers l52T1 ⊔ Subgroup.zpowers l52T2

theorem l52F_card : Nat.card l52F = 9 := by
  obtain ⟨h1, h2, h3, h4, ⟨h5, h6, h7⟩, -⟩ := l52_facts
  refine (Item434SmallTwoOther.isElemAbelian_zpowers_sup h1 h2 h3 (fun hm => ?_) h4).2
  rcases eq_of_mem_zpowers_of_pow_three h1 hm with h | h | h
  · exact h5 h
  · exact h6 h
  · exact h7 h

theorem l52R_mem_normalizer : l52R ∈ Subgroup.normalizer (l52F : Set SL(5, ZMod 2)) := by
  obtain ⟨-, -, -, -, -, h8, h9, -⟩ := l52_facts
  have hle : l52F.map (MulAut.conj l52R).toMonoidHom ≤ l52F := by
    rw [l52F, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h8]
      exact (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) 2))
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h9]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  exact hle ⟨x, hx, rfl⟩

theorem factorization_card_SL5Z : (Nat.card SL(5, ZMod 2)).factorization 3 = 2 := by
  rw [← Nat.card_congr (slCongr (GaloisField.equivZmodP 2).toRingEquiv).toEquiv]
  exact Item434SmallTwoOther.L52.factorization_card_SL5

theorem exists_pow_four_l52 {X : Type} [Group X] (e : X ≃* projSL 5 (GaloisField 2 1))
    {D : Subgroup X} (hD9 : Nat.card D = 9) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, h10, h11⟩ := l52_facts
  have : Finite SL(5, ZMod 2) := inferInstance
  set φ : X ≃* SL(5, ZMod 2) := e.trans
    ((Item434SmallTwoOther.slEquivProjSL (by norm_num)).symm.trans
      (slCongr (GaloisField.equivZmodP 2).toRingEquiv))
  have ht1 : l52T1 ∈ l52F := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  obtain ⟨hm, h4, h2⟩ := normalizerMonoidHom_pow_four l52R_mem_normalizer h10 ht1 h11
  exact exists_pow_four_of_conj φ factorization_card_SL5Z l52F_card hm h4 h2 hD9

theorem census424_of_l52 {X : Type} [Group X] [Finite X] (e : X ≃* projSL 5 (GaloisField 2 1)) :
    Census424 X := by
  intro D c d K h
  exact (false_of_pow_four h (exists_pow_four_l52 e h.card_eq)).elim

end Item424Res2

open Item424Res2

theorem k424Inner46Seven_of (hS : K424Inner46SevenSp62) : K424Inner46Seven := by
  rintro X _ _ hX - - -
  rcases hX with h | h | h
  · obtain ⟨e⟩ := h
    exact census424_of_l52 e
  · exact hS X h
  · obtain ⟨e⟩ := h
    exact census424_of_u54 e

end CFSG.RankThree.PartTwo.Sec4
