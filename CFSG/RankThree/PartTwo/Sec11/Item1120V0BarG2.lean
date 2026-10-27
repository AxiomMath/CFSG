module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarFam
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCount
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.Open (ordG2)

namespace Item1120V0Bar

section Arith

theorem g2_three_dvd_sq_sub_one {q : ℕ} (hq3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h <;> simp [h]
  omega

theorem factorization_ordG2 {q : ℕ} (hq : 0 < q) (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    (ordG2 q).factorization 3 = 2 * (q ^ 2 - 1).factorization 3 + 1 := by
  have hq2sq : 4 ≤ q ^ 2 := by nlinarith
  have hq6le : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
  have hdvd : 3 ∣ q ^ 2 - 1 := g2_three_dvd_sq_sub_one hq3
  have hndvd2 : ¬ 3 ∣ q ^ 2 := fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hndvd6 : ¬ 3 ∣ q ^ 6 := fun h => hq3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hodd3 : Odd (3 : ℕ) := ⟨1, by norm_num⟩
  have h6 : (q ^ 2) ^ 3 = q ^ 6 := by ring
  have hL : padicValNat 3 ((q ^ 2) ^ 3 - 1 ^ 3) = padicValNat 3 (q ^ 2 - 1) + padicValNat 3 3 :=
    padicValNat.pow_sub_pow hodd3 (by omega) hdvd hndvd2 (by norm_num)
  have h33 : padicValNat 3 3 = 1 := padicValNat_self
  rw [h6, one_pow, h33] at hL
  have e6 : (q ^ 6).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hndvd6
  have e61 : (q ^ 6 - 1).factorization 3 = (q ^ 2 - 1).factorization 3 + 1 := by
    rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three, hL]
  have hA : q ^ 6 ≠ 0 := pow_ne_zero 6 hq.ne'
  have hB : q ^ 6 - 1 ≠ 0 := by omega
  have hC : q ^ 2 - 1 ≠ 0 := by omega
  unfold ordG2
  rw [Nat.factorization_mul (mul_ne_zero hA hB) hC, Nat.factorization_mul hA hB,
    Finsupp.add_apply, Finsupp.add_apply, e6, e61]
  omega

theorem factorization_card_SL2 {q : ℕ} (hq : 0 < q) (hq2 : 2 ≤ q) (hq3 : ¬ 3 ∣ q) :
    (q * (q ^ 2 - 1)).factorization 3 = (q ^ 2 - 1).factorization 3 := by
  have hq2sq : 4 ≤ q ^ 2 := by nlinarith
  have hC : q ^ 2 - 1 ≠ 0 := by omega
  rw [Nat.factorization_mul hq.ne' hC, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hq3, zero_add]

end Arith

section Main


noncomputable def G2eComapMulEquiv {Z G : Type} [Group Z] [Group G] (e : Z ≃* G)
    (L : Subgroup G) : (L.comap e.toMonoidHom : Subgroup Z) ≃* L :=
  (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))

theorem nonempty_mulEquiv_long_short {Z : Type} [Group Z] {K : Type} [Field K] [Finite K]
    (e : Z ≃* adjointGroup .G2 K) :
    Nonempty (((KS11Lie4Proof.g2LongSL2 K).comap e.toMonoidHom : Subgroup Z) ≃*
      ((KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom : Subgroup Z)) := by
  obtain ⟨f⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2LongSL2 (K := K)
  obtain ⟨g⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  exact ⟨(G2eComapMulEquiv e (KS11Lie4Proof.g2LongSL2 K)).trans
    (f.symm.trans (g.trans (G2eComapMulEquiv e (KS11Lie4Proof.g2ShortSL2 K)).symm))⟩

theorem v0FamG2 : V0FamG2 := by
  intro Z _ _ hZq α σ J ξ γ hα3 hJα hJT hξJ hξsyl hξ9 hσ3 hσα hσJ hσξ hγ3 hP3 hLB
  obtain ⟨q, hq, ⟨e0⟩⟩ := hZq
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.G2 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, ⟨e0⟩⟩, nonempty_mulEquiv_commutator_of_isPerfect hperf⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424G2_holds Z hZ α J hα3 hno hJα hJT
  obtain ⟨z, rfl⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := hα3
  rcases KS11Lie3Proof.splitFamily_g2 Z hZ with hZ' | hno
  swap
  · exact (hno z J hz3 hJα hJT).elim
  have hcen : Subgroup.center Z = ⊥ := KS11Lie3Proof.center_eq_bot_g2 Z hZ
  have hcent : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (MonoidHom.mem_ker.mp hx)
    rw [hcen, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  obtain ⟨K, _, _, hK3, hK4, e, hezM, hB⟩ := KS11Lie4Proof.exists_g2_threeB
    (KS11Lie4Proof.g2ThreeConjSL2_of_minus KS11Lie7Proof.g2ThreeConjSL2Minus_holds)
    (KS11Lie4Proof.g2ThreeACent_of_minus KS11Lie7Proof.g2ThreeACentMinus_holds)
    KS11Lie4Proof.g2ThreeBCent_holds hZ' hz3 hJα hJT
  have hJS : J = (KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom := hB.eq hJα
  have hθc := hB.thetaCentral hJα
  have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJα
  have hσfix : ∀ j ∈ J, σ j = j := fixes_of_mem_theta hJp σ hθc hσJ
  have hout : σ ∈ (MulAut.conj : Z →* MulAut Z).range :=
    (KS11Lie4Proof.centJ119G2Out_of_twisted KS11Lie7Proof.g2ThreeConjSL2Minus_holds
      KS11Lie7Proof.g2ThreeACentMinus_holds) Z hZ' z σ J hz3 hσ3 hσα.symm hJα hJT hσfix
  obtain ⟨b, rfl⟩ := hout
  have hb3 : ∃ k : ℕ, b ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hσ3
    refine ⟨k, hcent ?_⟩
    rw [map_pow, hk, map_one]
  have hbJ : ∀ j ∈ J, b * j = j * b := by
    intro j hj
    have h1 := hσfix j hj
    rw [MulAut.conj_apply] at h1
    calc b * j = (b * j * b⁻¹) * b := by group
      _ = j * b := by rw [h1]
  have hbξ : b * ξ = ξ * b := hcent (by rw [map_mul, map_mul]; exact hσξ)
  have hξ3 : ∃ k : ℕ, ξ ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hξsyl.isPGroup ⟨ξ, Subgroup.mem_zpowers ξ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥ :=
    zpowers_inf_zpowers_eq_bot hJT hξJ hξ3 hbJ hb3
  obtain ⟨e'⟩ := nonempty_mulEquiv_long_short e
  have hz3' : z ^ 3 = 1 := (KS11Lie4Proof.g2_order_three hZ' hz3 hJα hJT).1
  obtain ⟨ζ, hζM, hzζ, hζ3, hζord⟩ := exists_big_elt_of_sylow
    (e'.trans (MulEquiv.subgroupCongr hJS.symm)) hξsyl hezM hz3'
  have hζJ : ∀ j ∈ J, ζ * j = j * ζ := by
    intro j hj
    rw [hJS] at hj
    apply e.injective
    rw [map_mul, map_mul]
    exact (KS11Lie4Proof.g2Short_commute_g2Long hj hζM).symm
  have hle := hLB ζ hζ3
    (by
      rw [MulAut.conj_apply]
      calc z * ζ * z⁻¹ = ζ * z * z⁻¹ := by rw [hzζ]
        _ = ζ := by group)
    (fun j hj => by
      calc ζ * j * ζ⁻¹ = j * ζ * ζ⁻¹ := by rw [hζJ j hj]
        _ = j := by group)
  rw [orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent ζ,
    orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent b] at hle
  have hq3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_of_ringChar_ne hK3
  have hcardZ : Nat.card Z = ordG2 (Nat.card K) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2
  have hcardJ : Nat.card J = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [hJS, Nat.card_congr ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _))).toEquiv]
    obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    rw [← Nat.card_congr e₂.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hξord : orderOf ξ = 3 ^ (Nat.card K ^ 2 - 1).factorization 3 := by
    rw [orderOf_eq_three_pow_of_isSylowOf hξsyl, hcardJ,
      factorization_card_SL2 Nat.card_pos (by omega) hq3]
  have hcardZ3 : (Nat.card Z).factorization 3 = 2 * (Nat.card K ^ 2 - 1).factorization 3 + 1 := by
    rw [hcardZ]
    exact factorization_ordG2 Nat.card_pos (by omega) hq3
  have hcard : 3 ^ (Nat.card Z).factorization 3 ≤ 3 * (orderOf b * orderOf ξ) := by
    rw [hcardZ3]
    have hbge : 3 ^ (Nat.card K ^ 2 - 1).factorization 3 ≤ orderOf b := by
      rw [← hξord, ← hζord]
      exact hle
    calc 3 ^ (2 * (Nat.card K ^ 2 - 1).factorization 3 + 1)
        = 3 * (3 ^ (Nat.card K ^ 2 - 1).factorization 3 *
            3 ^ (Nat.card K ^ 2 - 1).factorization 3) := by
          rw [pow_succ, two_mul, pow_add]
          ring
      _ ≤ 3 * (orderOf b * orderOf ξ) := by
          rw [hξord]
          exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul hbge le_rfl)
  exact v0_conclusion_of_inner hcent hP3 hbξ hdisj hcard

end Main

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
