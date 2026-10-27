module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Monster.GMS

private theorem commute_of_mem_normal_card_two
    {M : Type*} [Group M] {N : Subgroup M} [N.Normal]
    (hN : Nat.card ↥N = 2) {a : M} (ha : a ∈ N) (ha1 : a ≠ 1) :
    ∀ m : M, a * m = m * a := by
  have huniq := (Nat.card_eq_two_iff' (1 : ↥N)).mp hN
  obtain ⟨y, _, hy_uniq⟩ := huniq
  have haN : (⟨a, ha⟩ : ↥N) = y := hy_uniq ⟨a, ha⟩ (by simpa using ha1)
  intro m
  have hmem : m * a * m⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem a ha m
  have hne : (⟨m * a * m⁻¹, hmem⟩ : ↥N) ≠ 1 := by
    intro h
    apply ha1
    have h1 : m * a * m⁻¹ = 1 := congrArg Subtype.val h
    calc
      a = m⁻¹ * (m * a * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hbN : (⟨m * a * m⁻¹, hmem⟩ : ↥N) = y := hy_uniq _ hne
  have hba : m * a * m⁻¹ = a := congrArg Subtype.val (hbN.trans haN.symm)
  have hmul : m * a = a * m := by
    calc
      m * a = (m * a * m⁻¹) * m := by group
      _ = a * m := by rw [hba]
  exact hmul.symm

private theorem eq_of_ne_one_of_card_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : Nat.card H = 2) {a b : G} (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, _, hy_uniq⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hH
  have h := (hy_uniq ⟨a, ha⟩ (by simpa using ha1)).trans
    (hy_uniq ⟨b, hb⟩ (by simpa using hb1)).symm
  exact congrArg Subtype.val h

theorem gk7c_centralizer_le_of_core {K : Type*} [Group K] {p : ℕ} {e t : K} {J : Subgroup K}
    (hJ : J ≤ Subgroup.centralizer ({e} : Set K))
    (h2 : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set K)) = 2)
    (hcore : LargeEvenPPrimeCore p ↥(Subgroup.centralizer ({e} : Set K)) =
      (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf (Subgroup.centralizer ({e} : Set K)))
    (ht : t ∈ J ⊓ Subgroup.centralizer (J : Set K)) (ht1 : t ≠ 1) :
    Subgroup.centralizer ({e} : Set K) ≤ Subgroup.centralizer ({t} : Set K) := by
  set C := Subgroup.centralizer ({e} : Set K) with hC
  set N := (J ⊓ Subgroup.centralizer (J : Set K)).subgroupOf C with hN
  have hle : J ⊓ Subgroup.centralizer (J : Set K) ≤ C := le_trans inf_le_left hJ
  have hNcard : Nat.card ↥N = 2 := by
    rw [hN]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans h2
  haveI hNnormal : N.Normal := hcore ▸ LargeEvenPPrimeCore.normal p C
  have htN : (⟨t, hJ ht.1⟩ : ↥C) ∈ N := by
    rw [hN]
    exact Subgroup.mem_subgroupOf.2 ht
  intro g hg
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have hcomm := commute_of_mem_normal_card_two hNcard htN (by
    intro h
    exact ht1 (congrArg Subtype.val h)) ⟨g, hg⟩
  exact (congrArg Subtype.val hcomm).symm

section Baby

theorem gk7c_babyInv_of_core
    {e t : NativeSporadic.B} {J : Subgroup NativeSporadic.B}
    (he : orderOf e = 7) (hJ : J ≤ Subgroup.centralizer ({e} : Set NativeSporadic.B))
    (h2 : Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B)) = 2)
    (hcore : LargeEvenPPrimeCore 7 ↥(Subgroup.centralizer ({e} : Set NativeSporadic.B)) =
      (J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B)).subgroupOf
        (Subgroup.centralizer ({e} : Set NativeSporadic.B)))
    (ht : t ∈ J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B)) (ht1 : t ≠ 1) :
    BabyInv 0 t := by
  have P := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.bSevenElem_parts
  have hα : BabyInv 0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.babyInv_zero_of_rank_1860
      (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven = 7 :=
    orderOf_eq_prime P.x_pow P.x_ne
  obtain ⟨c, hc⟩ := isConj_iff.1
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bSeven_isConj hxS he)
  set C := Subgroup.centralizer ({e} : Set NativeSporadic.B) with hC
  set α' := c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * c⁻¹ with hα'def
  have hα' : BabyInv 0 α' := by
    rw [hα'def]
    exact hα.of_isConj (isConj_iff.2 ⟨c, rfl⟩)
  have hα'e : α' ∈ C := by
    refine (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
    rw [hα'def]
    rw [← hc]
    calc c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * c⁻¹ *
          (c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven * c⁻¹) =
        c * (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB *
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven) * c⁻¹ := by group
      _ = c * (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven *
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB) * c⁻¹ := by
        rw [P.alpha_x]
      _ = (c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven * c⁻¹) *
          (c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * c⁻¹) := by group
  have hle : C ≤ Subgroup.centralizer ({α'} : Set NativeSporadic.B) := by
    intro g hg
    have hg' : g * e = e * g :=
      (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 hg
    have hmem : c⁻¹ * g * c ∈
        Subgroup.centralizer ({CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven} :
          Set NativeSporadic.B) := by
      refine (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
      have hx' : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven =
          c⁻¹ * e * c := by rw [← hc]; group
      rw [hx']
      calc c⁻¹ * g * c * (c⁻¹ * e * c) = c⁻¹ * (g * e) * c := by group
        _ = c⁻¹ * (e * g) * c := by rw [hg']
        _ = c⁻¹ * e * c * (c⁻¹ * g * c) := by group
    have hα'' : c⁻¹ * g * c *
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB =
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * (c⁻¹ * g * c) :=
      (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1
        (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.centralizer_xSeven_le hmem)
    refine (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
    rw [hα'def]
    calc g * (c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * c⁻¹) =
        c * (c⁻¹ * g * c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB) * c⁻¹ :=
          by group
      _ = c * (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB *
          (c⁻¹ * g * c)) * c⁻¹ := by rw [hα'']
      _ = c * CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.alphaB * c⁻¹ * g := by group
  have hZcenter :
      Subgroup.zpowers (⟨α', hα'e⟩ : ↥C) ≤ Subgroup.center ↥C := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : NativeSporadic.B) * α' = α' * (g : NativeSporadic.B)
    exact (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 (hle g.2)
  have hZnormal : (Subgroup.zpowers (⟨α', hα'e⟩ : ↥C)).Normal :=
    Subgroup.normal_of_le_center hZcenter
  have hZcard : Nat.card ↥(Subgroup.zpowers (⟨α', hα'e⟩ : ↥C)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact hα'.1
  have hZle : Subgroup.zpowers (⟨α', hα'e⟩ : ↥C) ≤ LargeEvenPPrimeCore 7 ↥C := by
    show Subgroup.zpowers (⟨α', hα'e⟩ : ↥C) ≤ CFSG.pPrimeCore 7 ↥C
    exact le_sSup ⟨hZnormal, by rw [hZcard]; norm_num⟩
  have hα'N : (⟨α', hα'e⟩ : ↥C) ∈
      (J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B)).subgroupOf C := by
    rw [← hcore]
    exact hZle (Subgroup.mem_zpowers _)
  have hα'J : α' ∈ J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B) := by
    simpa using (Subgroup.mem_subgroupOf).1 hα'N
  have htN : (⟨t, hJ ht.1⟩ : ↥C) ∈
      (J ⊓ Subgroup.centralizer (J : Set NativeSporadic.B)).subgroupOf C :=
    Subgroup.mem_subgroupOf.2 ht
  have hα'ne : α' ≠ 1 := by
    intro h
    have hα'ord : orderOf α' = 2 := hα'.1
    rw [h, orderOf_one] at hα'ord
    exact absurd hα'ord (by norm_num)
  have ht_eq : t = α' := eq_of_ne_one_of_card_two h2 ht hα'J ht1 hα'ne
  rw [ht_eq]
  exact hα'

theorem gk7c_nine_dvd_card_centralizer
    {e : NativeSporadic.B} (he : orderOf e = 7) :
    9 ∣ Nat.card (Subgroup.centralizer ({e} : Set NativeSporadic.B)) := by
  have h :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.card_centralizer_seven_three e he
  have hdvd : 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({e} : Set NativeSporadic.B)) := by
    have := Nat.ordProj_dvd (Nat.card (Subgroup.centralizer ({e} : Set NativeSporadic.B))) 3
    rwa [h] at this
  simpa using hdvd

end Baby

end CFSG.StandardType.SporadicShape
