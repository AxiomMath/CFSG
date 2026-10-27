module

public import CFSG.RankThree.PartOne.KF.ClsExcRank
public import CFSG.RankThree.PartOne.KF.ClsRankOneLevi
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import CFSG.Timmesfeld.Orders.ExceptionalTorus

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ExceptionalOrders
open CFSG.Assembly.RankThreeEven (localRank)

section Main

theorem no_plane_G2 {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1) {U E : Subgroup (adjointGroup .G2 K)}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup .G2 K)))
    (hEp : ∀ g ∈ E, g ^ p = 1) (hEc : Nat.card E = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨J, φ, hJ, hφ, hmem⟩ := exists_hom_into_parabolic_of_normalizes .G2 hU hU2 hE
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hex : ∀ i : Fin Tag.G2.rank, ∃ j : Fin Tag.G2.rank, ∀ k, k ≠ i → k = j := by
    decide
  obtain ⟨j, hj⟩ := hex i
  have hsub : J ⊆ ({j} : Set (Fin Tag.G2.rank)) := fun k hk => hj k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup .G2 K J ≤ parabolicSubgroup .G2 K {j} :=
    ((standard_parabolic_cells .G2 K).2.2.2.1 J _).2 hsub
  have hrT : ¬ p ∣ Nat.card (torusGroup .G2 K) := by
    rw [card_torusGroup_G2]
    exact fun h => hpq (hp.dvd_of_dvd_pow h)
  have hrange : IsPGroup p φ.range :=
    (IsPGroup.of_card hEc).of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcyc : IsCyclic φ.range := isCyclic_of_le_parabolic_singleton j hp2 hrT
    (by rintro _ ⟨e, rfl⟩; exact hle (hmem e)) hrange
  have hEcyc : IsCyclic E :=
    isCyclic_of_surjective (MonoidHom.ofInjective hφ).symm.toMonoidHom
      (MonoidHom.ofInjective hφ).symm.surjective
  exact not_isCyclic_of_pow_eq_one hp hEc (fun g => Subtype.ext (hEp g g.2)) hEcyc

end Main

end CFSG.RankThree.PartOne.KFU

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint (AdjointQuotient)
open CFSG.Assembly.RankThreeEven (localRank)

theorem kf123ExcG2NoRankTwo : KF123ExcG2NoRankTwo := by
  intro X _ _ f hch p hp hp5 hpq
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hch.2
  have : CharP K 2 := KFU.charP_two_of_card_eq_two_pow hK
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  let e : X ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  by_contra hrank
  push Not at hrank
  obtain ⟨U, hU2, hU0, E, hEU, hEel, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) (by omega : 2 ≤ localRank p X)
  have : IsElementaryAbelian p E := hEel
  refine KFU.no_plane_G2 hp (by omega) (by rwa [hK]) (U := U.map e.toMonoidHom)
    (E := E.map e.toMonoidHom) ?_ (hU2.map e.toMonoidHom) ?_ ?_ ?_
  · intro hbot
    exact hU0 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hEU
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian g hg, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hEc

end CFSG.RankThree.PartOne
