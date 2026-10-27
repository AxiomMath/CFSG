module

public import CFSG.RankThree.PartOne.N143.Statements
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
import CFSG.RankThree.PartOne.BRANCH.RankArith
import CFSG.RankThree.PartOne.BRANCH.RankSylow

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.BRANCH

theorem exists_sub_card_pow_three_five {X : Type} [Group X] {q : ℕ} (hq : q.Prime) {D : Subgroup X}
    (hD : CFSG.IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 5) :
    ∃ E : Subgroup X, (∀ x ∈ E, x ^ q = 1) ∧ Nat.card E = q ^ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 5 hq.ne_zero)
  have hdvd : q ^ 3 ∣ Nat.card D := by
    rw [hcard]
    exact pow_dvd_pow q (by norm_num)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime q hdvd
  refine ⟨H.map D.subtype, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩
    exact elemPow_eq_one_of_isElementaryAbelian (p := q) (d : X) d.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hH]

theorem false_G2_prime
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E : Subgroup X} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hmod
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : X ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  refine Q1327C.false_of_pow_three_G2_five K hp hp5 hpq
    (E := E.map (e : X →* adjointGroup .G2 K)) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    change (e x) ^ p = 1
    rw [← map_pow, hE x hx, map_one]
  · rw [← Nat.card_congr (e.subgroupMap E).toEquiv]
    exact hcard

theorem card_le_G2_three
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 ^ 3 := by
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
    rw [← map_pow, hE y hy, map_one]
  have hcard' : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective e.injective
  have hmain : ∃ (T : Subgroup (adjointGroup .G2 K)) (L : Type) (_ : Field L)
      (ψ : T →* (Fin Tag.G2.rank → Lˣ)), Function.Injective ψ ∧ ¬ 3 ^ (1 + 1) ∣ T.index := by
    have hGcard : Nat.card (adjointGroup .G2 K) = Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) *
        (Nat.card K ^ 2 - 1) := card_adjointGroup_G2
    rcases BRANCH.two_pow_mod_three f with ⟨h3, -⟩ | ⟨h3, -⟩
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
  simpa using hb

theorem false_G2_three_five
    {X : Type} [Group X] [Finite X] {f : ℕ} (hmod : ChevalleyExceptionalModel X .G2 2 f)
    {E : Subgroup X} (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 5) : False := by
  have hb := card_le_G2_three hmod
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian (p := 3) (A := E) x hx)
  rw [hcard] at hb
  norm_num at hb

end CFSG.RankThree.PartOne.F106
