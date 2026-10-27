module

public import CFSG.RankThree.PartOne.BRANCH.RankFinal
public import CFSG.RankThree.PartOne.BRANCH.RankSylow
public import CFSG.RankThree.PartOne.BRANCH.RankArith

public section

namespace CFSG.RankThree.PartOne.BRANCH

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.N143X

theorem g2ThreeRank :
    G2ThreeRank := by
  intro X _ _ f hmod E hE hcard
  obtain ⟨hadm, K, _, _, hK, ⟨e₀⟩⟩ := hmod
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : X ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv X e.toEquiv
  have hf : 1 ≤ f := hadm.2.1
  have hQ : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hE3 : ∀ x ∈ E.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 3) y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  have hmain : ∃ (T : Subgroup (adjointGroup .G2 K)) (L : Type) (_ : Field L)
      (ψ : T →* (Fin Tag.G2.rank → Lˣ)), Function.Injective ψ ∧ ¬ 3 ^ (1 + 1) ∣ T.index := by
    have hGcard : Nat.card (adjointGroup .G2 K) = Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 2 - 1) := card_adjointGroup_G2
    rcases two_pow_mod_three f with ⟨h3, -⟩ | ⟨h3, -⟩
    ·
      have hQ3 : Nat.card K % 3 = 1 := by rw [hK]; exact h3
      have hle : torusGroup .G2 K ≤ adjointGroup .G2 K := torusGroup_le_adjointGroup_G2
      obtain ⟨et, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
      let eT : (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) ≃* torusGroup .G2 K :=
        Subgroup.subgroupOfEquivOfLe hle
      have hTcard : Nat.card ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)) =
          (Nat.card K - 1) ^ 2 := by
        rw [Nat.card_congr eT.toEquiv]
        exact card_torusGroup_G2
      refine ⟨(torusGroup .G2 K).subgroupOf (adjointGroup .G2 K), K, inferInstance,
        et.symm.toMonoidHom.comp eT.toMonoidHom, et.symm.injective.comp eT.injective, ?_⟩
      have hmul := ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)).index_mul_card
      rw [hTcard, hGcard] at hmul
      have := not_nine_dvd_g2_split hQ hQ3 (by rw [mul_comm]; exact hmul)
      simpa using this
    ·
      have hQ3 : Nat.card K % 3 = 2 := by rw [hK]; exact h3
      obtain ⟨T, ψ, hψ, hTcard⟩ := exists_torus_negOne_G2 K
      refine ⟨T, AlgebraicClosure K, inferInstance, ψ, hψ, ?_⟩
      have hmul := T.index_mul_card
      rw [hTcard, hGcard] at hmul
      have := not_nine_dvd_g2_twisted hQ hQ3 (by rw [mul_comm]; exact hmul)
      simpa using this
  obtain ⟨T, L, _, ψ, hψ, hidx⟩ := hmain
  have hb := card_le_of_torus Nat.prime_three ψ hψ hidx hE3
  rw [hcard'] at hb
  have : Tag.G2.rank = 2 := rfl
  rw [this] at hb
  norm_num at hb

end CFSG.RankThree.PartOne.BRANCH
