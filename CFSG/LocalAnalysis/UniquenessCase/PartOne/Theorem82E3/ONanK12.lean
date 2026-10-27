module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LG2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR865G2Center
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2
public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarL3Mat
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.RichardWeiss.Proving.PairRelations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof417

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

open CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec12.Hering129L
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

variable {K : Type} [Field K] [Finite K]

theorem factorization_card_centralizer_threeA
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    (Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))).factorization 3 =
      2 * ((Nat.card K) ^ 2 - 1).factorization 3 + 1 := by
  classical
  have hq2 : 2 ≤ Nat.card K := by omega
  obtain ⟨-, hSL⟩ := g2_centralizer_threeA hK3 hK4 hzS hz3 hz1
  obtain ⟨L, hLfield, hLfin, hcase⟩ := hSL
  rcases hcase with ⟨hLq, hqmod, ⟨e'⟩⟩ | ⟨hLq, hqmod, ⟨e'⟩⟩
  · have hcard : Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) =
        (Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 3 - 1) := by
      rw [Nat.card_congr e'.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hLq]
    have hfac : ((Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) *
        ((Nat.card K) ^ 3 - 1)).factorization 3 =
        2 * (Nat.card K - 1).factorization 3 + 1 := by
      change ((Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) *
        (bif true then (Nat.card K) ^ 3 - 1 else (Nat.card K) ^ 3 + 1)).factorization 3 =
        2 * (bif true then Nat.card K - 1 else Nat.card K + 1).factorization 3 + 1
      exact factorization_card_sl3_order true (Nat.card K) hqmod hq2
    have hsq : ((Nat.card K) ^ 2 - 1).factorization 3 = (Nat.card K - 1).factorization 3 := by
      have hnd : ¬ 3 ∣ Nat.card K + 1 := by
        intro h
        have := Nat.dvd_iff_mod_eq_zero.mp h
        omega
      calc ((Nat.card K) ^ 2 - 1).factorization 3
          = ((Nat.card K + 1) * (Nat.card K - 1)).factorization 3 := by
            rw [show (Nat.card K) ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
              simpa using Nat.sq_sub_sq (Nat.card K) 1]
        _ = (Nat.card K - 1).factorization 3 := factorization_mul_of_not_dvd_left hnd
    rw [hcard, hfac, ← hsq]
  · have hcard : Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) =
        (Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 3 + 1) := by
      rw [Nat.card_congr e'.toEquiv,
        CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hLq]
    have hfac : ((Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) *
        ((Nat.card K) ^ 3 + 1)).factorization 3 =
        2 * (Nat.card K + 1).factorization 3 + 1 := by
      change ((Nat.card K) ^ 3 * ((Nat.card K) ^ 2 - 1) *
        (bif false then (Nat.card K) ^ 3 - 1 else (Nat.card K) ^ 3 + 1)).factorization 3 =
        2 * (bif false then Nat.card K - 1 else Nat.card K + 1).factorization 3 + 1
      exact factorization_card_sl3_order false (Nat.card K) hqmod hq2
    have hsq : ((Nat.card K) ^ 2 - 1).factorization 3 = (Nat.card K + 1).factorization 3 := by
      have hnd : ¬ 3 ∣ Nat.card K - 1 := by omega
      rw [show (Nat.card K) ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) by
        simpa using Nat.sq_sub_sq (Nat.card K) 1]
      exact factorization_mul_of_not_dvd_right hnd
    rw [hcard, hfac, ← hsq]

theorem factorization_card_adjointGroup_g2
    (hq2 : 2 ≤ Nat.card K) (h3 : ¬ 3 ∣ Nat.card K) :
    (Nat.card (adjointGroup .G2 K)).factorization 3 =
      2 * ((Nat.card K) ^ 2 - 1).factorization 3 + 1 := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2,
    factorization_ordG2 (Nat.card_pos) hq2 h3]

private lemma exists_g2ShortSL2_order_three :
    ∃ z ∈ g2ShortSL2 K, orderOf z = 3 ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  have hz3' : (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three K) ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_pow_three K
  have hne : CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three K ≠ 1 := by
    intro h
    refine CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three_ne_smul (k := K) (1 : K) ?_
    rw [h]
    simp
  have hzord' : orderOf (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three K) = 3 :=
    orderOf_eq_prime hz3' hne
  let zSub : ↥(g2ShortSL2 K) := eS (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three K)
  have hzordSub : orderOf zSub = 3 := by
    rw [show zSub = eS (CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof.sl2Three K) from rfl,
      MulEquiv.orderOf_eq, hzord']
  let z : adjointGroup .G2 K := zSub
  have hzS : z ∈ g2ShortSL2 K := zSub.2
  have hzord : orderOf z = 3 := by rw [Subgroup.orderOf_coe, hzordSub]
  have hz3 : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    omega
  exact ⟨z, hzS, hzord, hz3, hz1⟩

private lemma exists_sylow_three_mem_center_of_order_three
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) (hnd3 : ¬ 3 ∣ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzord : orderOf z = 3) :
    ∃ (Q : Sylow 3 (adjointGroup .G2 K))
      (hzQ : z ∈ (Q : Subgroup (adjointGroup .G2 K))),
      IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) (Nat.card K) ∧
        (⟨z, hzQ⟩ : ↥(Q : Subgroup (adjointGroup .G2 K))) ∈
          Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 2 ≤ Nat.card K := by omega
  obtain ⟨-, hSL⟩ := g2_centralizer_threeA hK3 hK4 hzS hz3 hz1
  set C : Subgroup (adjointGroup .G2 K) :=
    Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) with hCdef
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzpowers_le_center : Subgroup.zpowers (⟨z, hzC⟩ : ↥C) ≤ Subgroup.center ↥C := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro c
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcz : Commute c (⟨z, hzC⟩ : ↥C) := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact hcz.zpow_right k
  haveI : (Subgroup.zpowers (⟨z, hzC⟩ : ↥C)).Normal :=
    Subgroup.normal_of_le_center hzpowers_le_center
  have h3z : IsPGroup 3 ↥(Subgroup.zpowers (⟨z, hzC⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers]; simpa using hzord)
  obtain ⟨Qc⟩ : Nonempty (Sylow 3 ↥C) := inferInstance
  have hzQc : (⟨z, hzC⟩ : ↥C) ∈ (Qc : Subgroup ↥C) :=
    IsPGroup.le_sylow_of_normal h3z Qc (Subgroup.mem_zpowers (⟨z, hzC⟩ : ↥C))
  let QH : Subgroup (adjointGroup .G2 K) := (Qc : Subgroup ↥C).map C.subtype
  have hfacC : (Nat.card ↥C).factorization 3 =
      (Nat.card (adjointGroup .G2 K)).factorization 3 := by
    rw [factorization_card_centralizer_threeA hK3 hK4 hzS hz3 hz1,
      factorization_card_adjointGroup_g2 (K := K) hq2 hnd3]
  have hQHcard : Nat.card QH = 3 ^ (Nat.card (adjointGroup .G2 K)).factorization 3 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity, hfacC]
  let Q : Sylow 3 (adjointGroup .G2 K) := Sylow.ofCard QH hQHcard
  have hQcoe : (Q : Subgroup (adjointGroup .G2 K)) = QH := Sylow.coe_ofCard _ _
  have hzQH : z ∈ QH := ⟨⟨z, hzC⟩, hzQc, rfl⟩
  have hzQ : z ∈ (Q : Subgroup (adjointGroup .G2 K)) := hQcoe ▸ hzQH
  refine ⟨Q, hzQ, hSL, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  show (y : adjointGroup .G2 K) * z = z * (y : adjointGroup .G2 K)
  have hy : (y : adjointGroup .G2 K) ∈ QH := by rw [← hQcoe]; exact y.2
  obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy
  rw [← hcy]
  exact Subgroup.mem_centralizer_singleton_iff.mp c.2

theorem exists_short_three_sylow_center
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) (hnd3 : ¬ 3 ∣ Nat.card K) :
    ∃ (z : adjointGroup .G2 K) (Q : Sylow 3 (adjointGroup .G2 K))
      (hzQ : z ∈ (Q : Subgroup (adjointGroup .G2 K))),
      orderOf z = 3 ∧ z ∈ g2ShortSL2 K ∧
        IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) (Nat.card K) ∧
        (⟨z, hzQ⟩ : ↥(Q : Subgroup (adjointGroup .G2 K))) ∈
          Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzS, hzord, hz3, hz1⟩ := exists_g2ShortSL2_order_three (K := K)
  obtain ⟨Q, hzQ, hSL, hzmem⟩ :=
    exists_sylow_three_mem_center_of_order_three hK3 hK4 hnd3 hzS hz3 hz1 hzord
  exact ⟨z, Q, hzQ, hzord, hzS, hSL, hzmem⟩

private lemma zpowers_eq_center_of_card_center_three {G : Type} [Group G] [Finite G]
    {Q0 : Subgroup G} {z : G} (hzQ0 : z ∈ Q0)
    (hZ3 : Nat.card (Subgroup.center ↥Q0) = 3) (hzord : orderOf z = 3)
    (hzmem : (⟨z, hzQ0⟩ : ↥Q0) ∈ Subgroup.center ↥Q0) :
    Subgroup.zpowers (⟨z, hzQ0⟩ : ↥Q0) = Subgroup.center ↥Q0 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.zpowers_le]; exact hzmem
  · rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hzord]
    exact hZ3.le

private lemma exists_conj_inv_mem_zpowers_center
    {Q0 Q : Sylow 3 (adjointGroup .G2 K)} {z : adjointGroup .G2 K}
    (hzQ0 : z ∈ (Q0 : Subgroup (adjointGroup .G2 K)))
    (hZ0 : Subgroup.zpowers (⟨z, hzQ0⟩ : ↥Q0) = Subgroup.center ↥Q0)
    {w : ↥(Q : Subgroup (adjointGroup .G2 K))}
    (hw : w ∈ Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K)))
    {g : adjointGroup .G2 K} (hg : g • Q0 = Q) :
    ∃ (hmem : g⁻¹ * (w : adjointGroup .G2 K) * g ∈ (Q0 : Subgroup (adjointGroup .G2 K))),
      (⟨g⁻¹ * (w : adjointGroup .G2 K) * g, hmem⟩ : ↥Q0) ∈
        Subgroup.zpowers (⟨z, hzQ0⟩ : ↥Q0) := by
  classical
  have hQcoe : (Q : Subgroup (adjointGroup .G2 K)) =
      (Q0 : Subgroup (adjointGroup .G2 K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]; rfl
  have hwback_mem : g⁻¹ * (w : adjointGroup .G2 K) * g ∈
      (Q0 : Subgroup (adjointGroup .G2 K)) := by
    have hwQ : (w : adjointGroup .G2 K) ∈
        (Q0 : Subgroup (adjointGroup .G2 K)).map (MulAut.conj g).toMonoidHom := by
      rw [← hQcoe]; exact w.2
    obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp hwQ
    have h1 : g⁻¹ * (w : adjointGroup .G2 K) * g = c := by
      rw [← hcw]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h1]
    exact hc
  have hwback_center :
      (⟨g⁻¹ * (w : adjointGroup .G2 K) * g, hwback_mem⟩ : ↥Q0) ∈ Subgroup.center ↥Q0 := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : adjointGroup .G2 K) * (g⁻¹ * (w : adjointGroup .G2 K) * g) =
      (g⁻¹ * (w : adjointGroup .G2 K) * g) * (y : adjointGroup .G2 K)
    have hyQ : g * (y : adjointGroup .G2 K) * g⁻¹ ∈ (Q : Subgroup (adjointGroup .G2 K)) := by
      rw [hQcoe]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom y.2
    have hcomm := Subgroup.mem_center_iff.mp hw ⟨g * (y : adjointGroup .G2 K) * g⁻¹, hyQ⟩
    have hcommH : (g * (y : adjointGroup .G2 K) * g⁻¹) * (w : adjointGroup .G2 K) =
        (w : adjointGroup .G2 K) * (g * (y : adjointGroup .G2 K) * g⁻¹) := by
      simpa using congrArg Subtype.val hcomm
    calc (y : adjointGroup .G2 K) * (g⁻¹ * (w : adjointGroup .G2 K) * g)
        = g⁻¹ * ((g * (y : adjointGroup .G2 K) * g⁻¹) * (w : adjointGroup .G2 K)) * g := by
          group
      _ = g⁻¹ * ((w : adjointGroup .G2 K) * (g * (y : adjointGroup .G2 K) * g⁻¹)) * g := by
          rw [hcommH]
      _ = (g⁻¹ * (w : adjointGroup .G2 K) * g) * (y : adjointGroup .G2 K) := by group
  exact ⟨hwback_mem, by rw [hZ0]; exact hwback_center⟩

private lemma eq_conj_or_conj_inv_of_mem_zpowers [Finite (adjointGroup .G2 K)]
    {Q0 : Subgroup (adjointGroup .G2 K)} {z : adjointGroup .G2 K} (hzQ0 : z ∈ Q0)
    (hzord : orderOf z = 3) {w : adjointGroup .G2 K} (hw3 : orderOf w = 3)
    {g : adjointGroup .G2 K} (hmem : g⁻¹ * w * g ∈ Q0)
    (hback : (⟨g⁻¹ * w * g, hmem⟩ : ↥Q0) ∈ Subgroup.zpowers (⟨z, hzQ0⟩ : ↥Q0)) :
    w = g * z * g⁻¹ ∨ w = (g * z * g⁻¹)⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hback
  have hkH : z ^ k = g⁻¹ * (w : adjointGroup .G2 K) * g := by
    have := congrArg Subtype.val hk
    simpa using this
  set h : adjointGroup .G2 K := g * z * g⁻¹ with hh
  have hw_eq : (w : adjointGroup .G2 K) = h ^ k := by
    have h1 : (w : adjointGroup .G2 K) = g * z ^ k * g⁻¹ := by
      rw [hkH]; group
    rw [h1, hh, conj_zpow]
  have hhord : orderOf h = 3 := by rw [hh, orderOf_conj_eq, hzord]
  have hwh : (w : adjointGroup .G2 K) = h ∨ (w : adjointGroup .G2 K) = h⁻¹ := by
    have hwne : (w : adjointGroup .G2 K) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hw3
      omega
    have hk3 : h ^ (k % 3) = (w : adjointGroup .G2 K) := by
      have h1 : h ^ (k % 3) = h ^ k := by
        have := zpow_mod_orderOf h k
        rwa [hhord] at this
      rw [h1, ← hw_eq]
    have hk0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have hklt : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
    · exfalso
      rw [h0] at hk3
      exact hwne hk3.symm
    · left
      rw [h1] at hk3
      simpa using hk3.symm
    · right
      rw [h2] at hk3
      have hsq : h ^ 2 = h⁻¹ := by
        have h3 : h ^ 3 = 1 := by rw [← hhord]; exact pow_orderOf_eq_one h
        calc h ^ 2 = h ^ 2 * 1 := by rw [mul_one]
          _ = h ^ 2 * (h * h⁻¹) := by rw [mul_inv_cancel]
          _ = h ^ 3 * h⁻¹ := by group
          _ = h⁻¹ := by rw [h3, one_mul]
      exact hk3.symm.trans hsq
  exact hwh

private lemma centralizer_singleton_eq_of_zpowers_eq {G : Type} [Group G] {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  have hx : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hy : Subgroup.centralizer ({y} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hx, h, ← hy]

private lemma isSLThreePiAt_centralizer_conj {G : Type} [Group G] [Finite G] (g z : G)
    {q : ℕ}
    (hSL : IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set G)) q) :
    IsSLThreePiAt ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set G)) q := by
  have hiso : ↥(Subgroup.centralizer ({g * z * g⁻¹} : Set G)) ≃*
      ↥(Subgroup.centralizer ({z} : Set G)) :=
    (MulEquiv.subgroupCongr (centralizer_conj_eq_map g z)).trans
      ((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  exact CFSG.RankThree.PartTwo.Sec4.Res417.isSLThreePiAt_congr hiso hSL

theorem isSLThreePiAt_centralizer_center_sylow
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) (hnd3 : ¬ 3 ∣ Nat.card K)
    (hZ3 : ∀ Q : Sylow 3 (adjointGroup .G2 K),
      Nat.card (Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K))) = 3)
    (Q : Sylow 3 (adjointGroup .G2 K))
    (w : ↥(Q : Subgroup (adjointGroup .G2 K)))
    (hw : w ∈ Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K)))
    (hw3 : orderOf (w : adjointGroup .G2 K) = 3) :
    IsSLThreePiAt ↥(Subgroup.centralizer
      ({(w : adjointGroup .G2 K)} : Set (adjointGroup .G2 K))) (Nat.card K) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, Q0, hzQ0, hzord, hzS, hSL, hzmem⟩ :=
    exists_short_three_sylow_center (K := K) hK3 hK4 hnd3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) Q0 Q
  have hZ0 : Subgroup.zpowers (⟨z, hzQ0⟩ : ↥Q0) = Subgroup.center ↥Q0 :=
    zpowers_eq_center_of_card_center_three hzQ0 (hZ3 Q0) hzord hzmem
  have hwh : (w : adjointGroup .G2 K) = g * z * g⁻¹ ∨
      (w : adjointGroup .G2 K) = (g * z * g⁻¹)⁻¹ := by
    obtain ⟨hmem, hback⟩ := exists_conj_inv_mem_zpowers_center hzQ0 hZ0 hw hg
    exact eq_conj_or_conj_inv_of_mem_zpowers hzQ0 hzord hw3 hmem hback
  have hhord : orderOf (g * z * g⁻¹) = 3 := by rw [orderOf_conj_eq, hzord]
  have hzp : Subgroup.zpowers (w : adjointGroup .G2 K) =
      Subgroup.zpowers (g * z * g⁻¹) :=
    ((CFSG.HardMathSupport.RichardWeiss.Proving.zpowers_eq_zpowers_iff_of_orderOf_three
      hhord hw3).mpr hwh).symm
  have hcent_eq := centralizer_singleton_eq_of_zpowers_eq hzp
  rw [hcent_eq]
  exact isSLThreePiAt_centralizer_conj g z hSL

@[expose] def K12SL : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime → r ≠ 3 → 4 ≤ r ^ f →
    CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 r f →
    ∀ S : Sylow 3 Y, ∀ w ∈ Subgroup.center (S : Subgroup Y), orderOf (w : Y) = 3 →
      CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt ↥(Subgroup.centralizer ({(w : Y)} : Set Y)) (r ^ f)

private lemma ringChar_eq_of_card_eq_prime_pow
    {K : Type} [Field K] [Finite K] {r f : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hq4 : 4 ≤ r ^ f) (hKcard : Nat.card K = r ^ f) :
    ringChar K = r ∧ ringChar K ≠ 3 ∧ ¬ 3 ∣ Nat.card K ∧ 4 ≤ Nat.card K := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hrcprime, hcardchar⟩ := FiniteField.card K (ringChar K)
  have hpow : (ringChar K) ^ (n : ℕ) = r ^ f := by
    rw [← hcardchar, ← Nat.card_eq_fintype_card, ← hKcard]
  have hn : (n : ℕ) ≠ 0 := by
    intro hn
    rw [hn, pow_zero] at hpow
    omega
  have hdvd_pow : ringChar K ∣ r ^ f := by
    rw [← hpow]
    exact dvd_pow_self _ hn
  have hrc : ringChar K = r :=
    (Nat.prime_dvd_prime_iff_eq hrcprime hr).1 (hrcprime.dvd_of_dvd_pow hdvd_pow)
  have hK3 : ringChar K ≠ 3 := by rw [hrc]; exact hr3
  have hnd3K : ¬ 3 ∣ Nat.card K := by
    rw [hKcard]
    intro h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq4K : 4 ≤ Nat.card K := by rw [hKcard]; exact hq4
  exact ⟨hrc, hK3, hnd3K, hq4K⟩

private lemma two_le_of_four_le_two_pow {f : ℕ} (h : 4 ≤ 2 ^ f) : 2 ≤ f := by
  by_contra hf
  have hf1 : f ≤ 1 := by omega
  have : 2 ^ f ≤ 2 := by
    calc 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hf1
      _ = 2 := by norm_num
  omega

private lemma exists_image_mem_center_of_mem_center
    {Y : Type} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K]
    (e : Y ≃* adjointGroup .G2 K) (S : Sylow 3 Y)
    (w : ↥(S : Subgroup Y)) (hw : w ∈ Subgroup.center ↥(S : Subgroup Y))
    (hw3 : orderOf (w : Y) = 3) :
    ∃ (S' : Sylow 3 (adjointGroup .G2 K))
      (w' : ↥(S' : Subgroup (adjointGroup .G2 K))),
      w' ∈ Subgroup.center ↥(S' : Subgroup (adjointGroup .G2 K)) ∧
        (w' : adjointGroup .G2 K) = e (w : Y) ∧
        orderOf (w' : adjointGroup .G2 K) = 3 := by
  let S' : Sylow 3 (adjointGroup .G2 K) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS'coe : (S' : Subgroup (adjointGroup .G2 K)) =
      (S : Subgroup Y).map e.toMonoidHom := by
    simp [S']
  have hwS' : e (w : Y) ∈ (S' : Subgroup (adjointGroup .G2 K)) := by
    rw [hS'coe]
    exact Subgroup.mem_map_of_mem e.toMonoidHom w.2
  let w' : ↥(S' : Subgroup (adjointGroup .G2 K)) := ⟨e (w : Y), hwS'⟩
  have hw'mem : w' ∈ Subgroup.center ↥(S' : Subgroup (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : adjointGroup .G2 K) * e (w : Y) = e (w : Y) * (y : adjointGroup .G2 K)
    have hy : (y : adjointGroup .G2 K) ∈ (S : Subgroup Y).map e.toMonoidHom := by
      rw [← hS'coe]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hwx := Subgroup.mem_center_iff.mp hw (⟨x, hx⟩ : ↥(S : Subgroup Y))
    have hwxH : (x : Y) * (w : Y) = (w : Y) * (x : Y) := by
      simpa using congrArg Subtype.val hwx
    rw [← hxy]
    have hmul : e.toMonoidHom ((x : Y) * (w : Y)) = e.toMonoidHom ((w : Y) * (x : Y)) := by
      rw [hwxH]
    change e.toMonoidHom x * e.toMonoidHom (w : Y) = e.toMonoidHom (w : Y) * e.toMonoidHom x
    simpa only [map_mul] using hmul
  have hw'3 : orderOf (w' : adjointGroup .G2 K) = 3 := by
    show orderOf (e (w : Y)) = 3
    rw [MulEquiv.orderOf_eq, hw3]
  exact ⟨S', w', hw'mem, rfl, hw'3⟩

private lemma isSLThreePiAt_centralizer_of_mulEquiv {X Y : Type} [Group X] [Group Y]
    [Finite X] [Finite Y] (e : X ≃* Y) (w : X) {q : ℕ}
    (h : IsSLThreePiAt ↥(Subgroup.centralizer ({(e w)} : Set Y)) q) :
    IsSLThreePiAt ↥(Subgroup.centralizer ({w} : Set X)) q := by
  have hmap := centralizer_map_equiv_eq e w
  have hiso : ↥(Subgroup.centralizer ({w} : Set X)) ≃*
      ↥(Subgroup.centralizer ({(e w)} : Set Y)) :=
    ((Subgroup.centralizer ({w} : Set X)).equivMapOfInjective e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap.symm)
  exact CFSG.RankThree.PartTwo.Sec4.Res417.isSLThreePiAt_congr hiso h

theorem k12SL_holds :
    K12SL := by
  classical
  intro Y _ _ r f hr hr3 hq4 hmodel S w hw hw3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hmodel.2
  letI := hKfield
  letI := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨hrc, hK3, hnd3K, hq4K⟩ :=
    ringChar_eq_of_card_eq_prime_pow hr hr3 hq4 hKcard
  have hf2 : r = 2 → 2 ≤ f := by
    intro hr2
    subst hr2
    exact two_le_of_four_le_two_pow hq4
  have hLM : CFSG.Blueprint.LieModel Y .G2 0 r f :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (t := .G2) (n := 0) (p := r) (f := f)
      (by decide)).mpr ⟨rfl, hmodel⟩
  have hZ3 : ∀ Q : Sylow 3 (adjointGroup .G2 K),
      Nat.card (Subgroup.center ↥(Q : Subgroup (adjointGroup .G2 K))) = 3 := by
    intro Q
    let Qy : Sylow 3 Y := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective Q
    have hY := CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.g2SylowCenterCardThree_holds
      (Y := Y) (p := r) (f := f) hr hr3 hf2 hLM Qy
    exact (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.card_center_sylow_three_eq_of_mulEquiv
      e.symm Q Qy).trans hY
  obtain ⟨S', w', hw'mem, hw'val, hw'3⟩ := exists_image_mem_center_of_mem_center e S w hw hw3
  have hH := isSLThreePiAt_centralizer_center_sylow (K := K) hK3 hq4K hnd3K hZ3 S' w' hw'mem
    hw'3
  rw [hw'val] at hH
  have hY := isSLThreePiAt_centralizer_of_mulEquiv e (w : Y) hH
  simpa [← Nat.card_eq_fintype_card, hKcard] using hY

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
