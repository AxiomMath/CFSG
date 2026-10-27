module

public import CFSG.RankThree.PartOne.KF.F4ParabolicSums
public import CFSG.RankThree.PartOne.KF.ClsExcE
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizes
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ExceptionalOrders
open CFSG.Assembly.RankThreeEven (localRank)

section Coatoms

@[expose] def coatomMask : Fin Tag.F4.rank → ℕ := ![14, 13, 11, 7]

theorem coatomMask_cases : ∀ i, coatomMask i = 7 ∨ coatomMask i = 11 ∨ coatomMask i = 13 ∨
    coatomMask i = 14 := by
  decide

theorem coatomMask_cover : ∀ i k : Fin Tag.F4.rank, k ≠ i → k ∈ maskSet .F4 (coatomMask i) := by
  decide

end Coatoms

section Main

theorem finsum_parabolicWeylGroup_eq_parabolicSum {τ : Tag} [Fintype (WeylGroup τ)]
    (J : Set (Fin τ.rank)) (q : ℕ) :
    ∑ᶠ w : parabolicWeylGroup τ J, q ^ (coxeterSystem τ).length w.1 = parabolicSum τ J q := by
  classical
  rw [parabolicSum, finsum_eq_sum_of_fintype]
  simp only [parabolic_eq_parabolicWeylGroup]
  exact (Finset.sum_subtype (Finset.univ.filter (· ∈ parabolicWeylGroup τ J))
    (fun x => by simp) (fun w => q ^ (coxeterSystem τ).length w)).symm

theorem no_plane_F4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {U E : Subgroup (adjointGroup .F4 K)} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K)))
    (hEc : Nat.card E = p ^ 2) : False := by
  classical
  have hc : ringChar K = 2 := by
    have : Fintype K := Fintype.ofFinite K
    have h : (2 : ℕ) • (1 : K) = 0 := by
      have := card_nsmul_eq_zero (G := K) (x := 1)
      rwa [← Nat.card_eq_fintype_card, hK] at this
    refine CharP.ringChar_of_prime_eq_zero Nat.prime_two ?_
    rwa [nsmul_one] at h
  have : CharP K 2 := ringChar.of_eq hc
  obtain ⟨J, hJ, hdvd⟩ := card_dvd_parabolic_of_normalizes .F4 hU hU2 hE
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  set M : Finset (Fin Tag.F4.rank) := maskSet .F4 (coatomMask i) with hM
  have hsub : J ⊆ (M : Set (Fin Tag.F4.rank)) := fun k hk => by
    exact_mod_cast coatomMask_cover i k (fun h => hi (h ▸ hk))
  have hle : parabolicSubgroup .F4 K J ≤ parabolicSubgroup .F4 K (M : Set (Fin Tag.F4.rank)) :=
    ((standard_parabolic_cells .F4 K).2.2.2.1 J _).2 hsub
  have hdvd' : p ^ 2 ∣ Nat.card (parabolicSubgroup .F4 K (M : Set (Fin Tag.F4.rank))) := by
    rw [← hEc]
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨-, -, -, -, -, -, hcell⟩ := standard_parabolic_cells .F4 K
  rw [hcell (M : Set (Fin Tag.F4.rank))] at hdvd'
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  rw [card_torusGroup_F4, ncard_posRoots_F4, hK,
    finsum_parabolicWeylGroup_eq_parabolicSum] at hdvd'
  have hcop : Nat.Coprime (p ^ 2) (2 ^ 24) :=
    Nat.Coprime.pow 2 24 ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
  have h1 : p ^ 2 ∣ parabolicSum .F4 M 2 := by
    have h2 : (2 - 1) ^ 4 = 1 := by norm_num
    rw [h2, one_mul] at hdvd'
    exact hcop.dvd_of_dvd_mul_left hdvd'
  exact not_sq_dvd_parabolicSum_F4_two hp hp5 (coatomMask_cases i) h1

end Main

end CFSG.RankThree.PartOne.KFU

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Blueprint (AdjointQuotient)

theorem kf123ExcF4TwoNoRankTwo : KF123ExcF4TwoNoRankTwo := by
  intro K _ _ _ hK p hp hp5 hrank
  have hC : Subgroup.center (adjointGroup .F4 K) = ⊥ := center_adjointGroup_eq_bot
  let e : AdjointQuotient .F4 K ≃* adjointGroup .F4 K :=
    (QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot
  obtain ⟨U, hU2, hU0, E, hEU, -, hEc⟩ :=
    exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hrank.ge
  refine KFU.no_plane_F4_two hK hp hp5 (U := U.map e.toMonoidHom) (E := E.map e.toMonoidHom) ?_
    (hU2.map e.toMonoidHom) ?_ ?_
  · intro hbot
    exact hU0 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).1 hbot)
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hEU
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hEc

end CFSG.RankThree.PartOne
