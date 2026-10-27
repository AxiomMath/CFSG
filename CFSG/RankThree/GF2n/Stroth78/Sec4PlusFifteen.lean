module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEightU33
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec3Three
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.LargeExtraspecial.AS35QCoSevenPlus
import CFSG.GroupTheory.CardLeTwoPowAddMulCardInfCentralizer
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.GH74.SmallRanks.PSL
import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.RankThree.GF2n.Stroth78.Sec2QaAbelian
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem not_seven_dvd_card_Xsub_of_card_ZQ_eq_four
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4)
    (hrank : twoRank ↥(Xsub S a) ≤ 2) (hOut : Nat.card (Outer ↥(Xsub S a)) ≤ 2) :
    ¬ 7 ∣ Nat.card ↥(Xsub S a) := by
  intro h7
  classical
  letI := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  haveI hXn : (Xsub S a).Normal := Xsub_normal S a
  have hZX : Subgroup.center ↥(Xsub S a) = ⊥ := center_Xsub_eq_bot_of_threeFourPlus S h h217 h34
  have hXsub : ∀ E : Subgroup ↥(Xsub S a), (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 2 ^ 2 := by
    intro E hE
    have hEcomm : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e := by
      intro e he f hf
      have h1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE e he)
      have h2 : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hE f hf)
      have h3 : (e * f)⁻¹ = e * f := inv_eq_of_mul_eq_one_right (hE _ (E.mul_mem he hf))
      calc e * f = (e * f)⁻¹ := h3.symm
        _ = f⁻¹ * e⁻¹ := mul_inv_rev e f
        _ = f * e := by rw [h1, h2]
    have hEel : CFSG.Open.IsElemAbelian 2 E :=
      ⟨⟨⟨fun x y => Subtype.ext (hEcomm x x.2 y y.2)⟩⟩, fun x hx => by
        rw [pow_two]
        exact hE x hx⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hEel.2 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have hk2 := CFSG.SectionRank.le_pRank Nat.one_lt_two le_top hEel hk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (hk2.trans hrank)
  have hOutB : ∀ E : Subgroup (Outer ↥(Xsub S a)), (∀ e ∈ E, e * e = 1) →
      Nat.card ↥E ≤ 2 ^ 1 := by
    intro E _
    have hle : Nat.card ↥E ≤ Nat.card (Outer ↥(Xsub S a)) := Subgroup.card_le_card_group E
    omega
  have hA : ∀ e ∈ Lbar S a, e * e = 1 := fun e he => by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj he
  have hLb := CFSG.GroupTheory.card_le_two_pow_add_mul_card_inf_centralizer (Xsub S a) hZX
    hXsub hOutB (Lbar S a) hA
  have hC6 := card_centralizer_Xsub_dvd_six S h h217
  set C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z)) with hCdef
  have hD2 : Nat.card ↥(Lbar S a ⊓ C) ≤ 2 := by
    have hdvd : Nat.card ↥(Lbar S a ⊓ C) ∣ 6 :=
      (Subgroup.card_dvd_of_le (inf_le_right : Lbar S a ⊓ C ≤ C)).trans hC6
    have h3 : ¬ 3 ∣ Nat.card ↥(Lbar S a ⊓ C) := by
      intro h3
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Lbar S a ⊓ C)) 3 h3
      have hx2 : x * x = 1 := Subtype.ext (hA x (Subgroup.mem_inf.mp x.2).1)
      have hdv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
      rw [hx] at hdv
      omega
    have hle6 : Nat.card ↥(Lbar S a ⊓ C) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(Lbar S a ⊓ C) := Nat.card_pos
    generalize Nat.card ↥(Lbar S a ⊓ C) = n at hdvd h3 hle6 hpos ⊢
    interval_cases n <;> omega
  have hR : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  have ha1 : a ≠ 1 := fun ha1 => h.not_mem_ZQ (ha1 ▸ (ZQ z).one_mem)
  have ha2 : a ^ 2 = 1 := by
    have := a_mul_self_eq_one S h.isConj
    rwa [← pow_two] at this
  have hao : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) := by
    rw [ZQ_inf_QaOf_eq_zpowers_of_card_ZQ_eq_four S h hZ,
      centerIn_QaOf_inf_Q_eq_zpowers_of_card_ZQ_eq_four S h hZ, Nat.card_zpowers,
      Nat.card_zpowers, S.hyp.orderOf_z, hao]
  have hid := two_mul_card_Lbar_mul_card_QaInterImage_of_card_inf S h.isConj h.mem_Q
    h.not_mem_ZQ h.mem_Qa hcard
  rw [hR, card_QbarOf_eq_pow S h.card_F] at hid
  have hcommB : ∀ x ∈ QaOf a ⊓ Q z, ∀ y ∈ QaOf a ⊓ Q z, x * y = y * x :=
    fun x hx y hy => commute_of_mem_QaOf_inf_Q S h.isConj h.not_mem_ZQ hx hy
  have hIdim := finrank_QaInterImage_le S hcommB h.card_F
  have hIcard : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) =
      2 ^ finrank (ZMod 2) ↥(QaInterImage S (QaOf a ⊓ Q z)) :=
    CFSG.LargeExtraspecial.AS35QCo.natCard_submodule _
  have hIle : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤ 2 ^ w := by
    rw [hIcard]
    exact Nat.pow_le_pow_right (by norm_num) hIdim
  have hLi : Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 2 ^ (2 * w) := by
    linarith
  have hLb8 : Nat.card ↥(Lbar S a) ≤ 8 * Nat.card ↥(Lbar S a ⊓ C) := by
    simpa using hLb
  have hℓ : Nat.card ↥(Lbar S a) ≤ 16 := by omega
  have hw : w = 4 := by
    have h1 : 2 ^ w * 2 ^ w ≤ 16 * 2 ^ w := by
      calc 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
        _ = Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) := hLi.symm
        _ ≤ 16 * 2 ^ w := Nat.mul_le_mul hℓ hIle
    have h2 : 2 ^ w ≤ 16 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3 : w ≤ 4 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    omega
  subst hw
  have hLi' : Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 256 := by
    rw [hLi]
    norm_num
  have hIle' : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤ 16 := by simpa using hIle
  have hℓ16 : Nat.card ↥(Lbar S a) = 16 := by
    by_contra hne
    have hlt : Nat.card ↥(Lbar S a) ≤ 15 := by omega
    have := Nat.mul_le_mul hlt hIle'
    omega
  have hi16 : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 16 := by
    rw [hℓ16] at hLi'
    omega
  have hD : Nat.card ↥(Lbar S a ⊓ C) = 2 := by omega
  have heven : Even (Nat.card ↥C) := by
    rw [even_iff_two_dvd]
    have := Subgroup.card_dvd_of_le (inf_le_right : Lbar S a ⊓ C ≤ C)
    rwa [hD] at this
  obtain ⟨eC⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217 heven
  have hCcard : Nat.card ↥C = 6 := by
    rw [Nat.card_congr eC.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ρ', hρ'⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 (by rw [hCcard]; norm_num)
  obtain ⟨σ', hσ'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Xsub S a)) 7 h7
  have hρo : orderOf (ρ' : Hbar z) = 3 := by rw [Subgroup.orderOf_coe]; exact hρ'
  have hσo : orderOf (σ' : Hbar z) = 7 := by rw [Subgroup.orderOf_coe]; exact hσ'
  have hρσ : (σ' : Hbar z) * ρ' = ρ' * σ' := Subgroup.mem_centralizer_iff.mp ρ'.2 σ' σ'.2
  have hnd : (qS S).polarBilin.Nondegenerate := by simpa only [qS] using q_nondegenerate S
  have hdim : finrank (ZMod 2) (Additive (QbarOf S)) = 8 := by
    have := finrank_QbarOf_eq_two_mul S h.card_F
    omega
  have hσq : ∀ v, qS S (rhoLin S σ' v) = qS S v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S σ').2 v
  have hρq : ∀ v, qS S (rhoLin S ρ' v) = qS S v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (rhoBar S ρ').2 v
  have hσ7 : rhoLin S σ' ^ 7 = 1 := by
    have := pow_orderOf_eq_one (rhoLin S σ')
    rwa [orderOf_rhoLin, hσo] at this
  have hσ1 : rhoLin S σ' ≠ 1 := by
    intro h1
    have := orderOf_rhoLin S σ'
    rw [h1, orderOf_one, hσo] at this
    omega
  have hρ3 : rhoLin S ρ' ^ 3 = 1 := by
    have := pow_orderOf_eq_one (rhoLin S ρ')
    rwa [orderOf_rhoLin, hρo] at this
  have hρ1 : rhoLin S ρ' ≠ 1 := by
    intro h1
    have := orderOf_rhoLin S ρ'
    rw [h1, orderOf_one, hρo] at this
    omega
  have hcomm : rhoLin S ρ' * rhoLin S σ' = rhoLin S σ' * rhoLin S ρ' := by
    rw [← rhoLin_mul, ← rhoLin_mul, hρσ]
  have hW4 : finrank (ZMod 2) ↥(QaInterImage S (QaOf a ⊓ Q z)) = 4 := by
    have h16 : (2 : ℕ) ^ finrank (ZMod 2) ↥(QaInterImage S (QaOf a ⊓ Q z)) = 2 ^ 4 := by
      rw [← hIcard, hi16]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h16
  have hWs : ∀ v ∈ QaInterImage S (QaOf a ⊓ Q z), qS S v = 0 := by
    intro v hv
    obtain ⟨y, hyB, hyv⟩ := (mem_QaInterImage_iff S).mp hv
    have hv' : v = Additive.ofMul (mkQbar S y) := (congrArg Additive.ofMul hyv).symm
    rw [hv']
    exact (q_eq_zero_iff S y).mpr (sq_eq_one_of_mem_QaOf_inf_Q S h hyB)
  have hHyp : CFSG.LargeExtraspecial.AS35QCo.Seven.Hyp (qS S) (rhoLin S σ') :=
    ⟨hnd, hdim, hσq, hσ7, hσ1⟩
  exact hρ1 (hHyp.eq_one_of_commute_of_totallySingular hW4 hWs hρq hρ3 hcomm)

theorem not_lieModel_psl_three_of_card_ZQ_eq_four
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSL 3 2 1 := by
  intro hX
  have h27 : StatedClassicalModel ↥(Xsub S a) .PSL 2 7 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two
      (hX.statedClassicalModel (by decide))
  have hrank : twoRank ↥(Xsub S a) ≤ 2 :=
    CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd Nat.prime_seven
      (by norm_num) h27
  have hOut : Nat.card (Outer ↥(Xsub S a)) ≤ 2 := by
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h27
    have hdvd := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor
      Nat.prime_seven K hK).2 ↥(Xsub S a)
      ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩
    exact Nat.le_of_dvd (by norm_num) (by simpa using hdvd)
  refine not_seven_dvd_card_Xsub_of_card_ZQ_eq_four S h h217 h34 hw4 hZ hrank hOut ?_
  rw [hX.card_psl_three_two]
  norm_num

end CFSG.RankThree.GF2n.Stroth78
