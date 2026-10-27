module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCentralCoverAtCenterPrimes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem two_le_exponent_of_lieModel_psl_two {Y : Type} [Group Y] {x : ℕ}
    (h : CFSG.Blueprint.LieModel Y .PSL 2 2 x) : 2 ≤ x := by
  obtain ⟨-, h1, -, h2, -⟩ := h.admissible
  by_contra hx
  have hx1 : x = 1 := by omega
  subst hx1
  exact h2 rfl

theorem nonempty_xbarMod_mulEquiv_psl2GF [(Q.subgroupOf M).Normal] {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) :
    Nonempty (XbarMod M Q Z B ≃* CFSG.AGLEmbedding.PSL2GF 2 x) := by
  have hStated := hLm2.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  simp only [CFSG.Open.StatedClassicalModel] at hStated
  obtain ⟨-, K, hKf, hKfin, hKcard, he⟩ := hStated
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨eK⟩ := he
  have hx0 : x ≠ 0 := by
    have h1 : 1 ≤ x := (hLm2.admissible).2.1
    omega
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 x) := Fintype.ofFinite _
  have hcardF : Fintype.card K = Fintype.card (GaloisField 2 x) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKcard,
      GaloisField.card 2 x hx0]
  let iso : K ≃+* GaloisField 2 x := FiniteField.ringEquivOfCardEq hcardF
  exact ⟨eK.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.GorensteinWalter.psl2RingEquiv iso))⟩

theorem isPerfect_xbarMod_of_lieModel [(Q.subgroupOf M).Normal] {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) :
    Group.IsPerfect (XbarMod M Q Z B) := by
  obtain ⟨e⟩ := nonempty_xbarMod_mulEquiv_psl2GF hLm2
  have hx := two_le_exponent_of_lieModel_psl_two hLm2
  have hcard : 3 < Nat.card (GaloisField 2 x) := by
    rw [GaloisField.card 2 x (by omega)]
    calc 3 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
  haveI := CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three (GaloisField 2 x) hcard
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem isCyclic_sylow_xbarMod_of_lieModel [Finite G] [(Q.subgroupOf M).Normal] {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (S : Sylow p (XbarMod M Q Z B)) : IsCyclic S := by
  obtain ⟨e⟩ := nonempty_xbarMod_mulEquiv_psl2GF hLm2
  have hx := two_le_exponent_of_lieModel_psl_two hLm2
  have hcyc := CFSG.Timmesfeld.RankOne.isCyclic_sylow_psl2 hx p hp2
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  haveI : IsCyclic ↥((S : Subgroup (XbarMod M Q Z B)).map e.toMonoidHom) := hcyc
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (S : Subgroup (XbarMod M Q Z B)) e.toMonoidHom
      e.injective).symm.toMonoidHom (MulEquiv.surjective _)

theorem Ctx.odd_card_center_Xbar [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) :
    Odd (Nat.card (Subgroup.center ↥(Xbar M Q Z B))) := by
  haveI : (Xbar M Q Z B).Normal := hc.Xbar_normal
  let C : Subgroup (Mbar M Q) := (Subgroup.center ↥(Xbar M Q Z B)).map (Xbar M Q Z B).subtype
  haveI : C.Normal := ConjAct.normal_of_characteristic_of_normal
  haveI : Group.IsNilpotent ↥C := by
    haveI : IsMulCommutative ↥C := Subgroup.map_isMulCommutative _ _
    exact CommGroup.isNilpotent
  have h := odd_card_of_normal_nilpotent hc.pCore_two_Mbar C
  rwa [Subgroup.card_map_of_injective (Xbar M Q Z B).subtype_injective] at h

theorem commutator_eq_top_of_closure_sq_eq_one {X : Type*} [Group X] [Finite X]
    (hperf : Group.IsPerfect (X ⧸ Subgroup.center X))
    (hodd : Odd (Nat.card (Subgroup.center X))) {S : Set X}
    (hS : Subgroup.closure S = ⊤) (hS2 : ∀ s ∈ S, s ^ 2 = 1) :
    commutator X = ⊤ := by
  have hsup : ∀ g : X, g ∈ commutator X ⊔ Subgroup.center X := by
    intro g
    have hmap : (commutator X).map (QuotientGroup.mk' (Subgroup.center X)) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _), ← commutator_def, hperf.commutator_eq_top]
    have hg : QuotientGroup.mk' (Subgroup.center X) g ∈
        (commutator X).map (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
    have hz : k⁻¹ * g ∈ Subgroup.center X := QuotientGroup.eq.mp hkg
    have h := Subgroup.mul_mem_sup hk hz
    rwa [mul_inv_cancel_left] at h
  rw [eq_top_iff, ← hS, Subgroup.closure_le]
  intro s hs
  obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hsup s)
  have hcomm : Commute c z := Subgroup.mem_center_iff.mp hz c
  have hz2 : z ^ 2 ∈ commutator X := by
    have h1 : c ^ 2 * z ^ 2 = 1 := by
      rw [← hcomm.mul_pow]
      exact hS2 _ hs
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (commutator X).inv_mem ((commutator X).pow_mem hc 2)
  have hzodd : Odd (orderOf z) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz)
  obtain ⟨k, hk⟩ := hzodd
  have hzk : z = (z ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hzc : z ∈ commutator X := by
    rw [hzk]
    exact (commutator X).pow_mem hz2 _
  exact (commutator X).mul_mem hc hzc

theorem Ctx.commutator_Xbar_eq_top_of_lieModel [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) :
    commutator ↥(Xbar M Q Z B) = ⊤ := by
  refine commutator_eq_top_of_closure_sq_eq_one (isPerfect_xbarMod_of_lieModel hLm2)
    hc.odd_card_center_Xbar (S := ((↑) : ↥(Xbar M Q Z B) → Mbar M Q) ⁻¹' Ebar M Q Z B)
    Subgroup.closure_closure_coe_preimage ?_
  intro s hs
  have h2 : orderOf (s : Mbar M Q) = 2 := Ctx.orderOf_eq_two_of_mem_Ebar hs
  rw [Subgroup.orderOf_coe] at h2
  rw [← h2]
  exact pow_orderOf_eq_one s

theorem Ctx.center_Xbar_eq_bot_of_lieModel_psl_two [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  refine CFSG.GorensteinWalter.oddCentralCover_eq_bot_of_cyclic_sylow_at_center_primes
    (hc.commutator_Xbar_eq_top_of_lieModel hLm2) _ rfl hc.odd_card_center_Xbar ?_
  intro p _ _ hp2 S
  exact isCyclic_sylow_xbarMod_of_lieModel hLm2 p hp2 S

end CFSG.RankThree.GF2n.Stroth80
