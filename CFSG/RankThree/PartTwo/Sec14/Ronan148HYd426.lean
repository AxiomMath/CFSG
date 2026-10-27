module

import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
import CFSG.RankThree.PartTwo.Sec14.Item145Bot
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofYd
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HInc
public import CFSG.RankThree.PartTwo.Sec4.Item426A6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_mem_center {K : Subgroup G} {d : G} (hdK : d ∈ K)
    (hKd : K ≤ Subgroup.centralizer ({d} : Set G)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)))
    {x : G} (hxK : x ∈ K) (hxC : x ∈ Subgroup.centralizer (K : Set G)) {k : ℕ}
    (hxk : x ^ 3 ^ k = 1) : x ∈ Subgroup.zpowers d := by
  set θ := aschbacherSolvableCore 3 ↥K with hθ
  obtain ⟨-, hθc, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  haveI : θ.Normal := by haveI := hθc; infer_instance
  set π := QuotientGroup.mk' θ with hπ
  set d' : ↥K := ⟨d, hdK⟩ with hd'
  set x' : ↥K := ⟨x, hxK⟩ with hx'
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hx'k : x' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
  have hcomm : x' * d' = d' * x' := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKd hxK))
  have hcen : ∀ y : ↥K, (∀ g : ↥K, g * y = y * g) → π y ∈ Subgroup.center (↥K ⧸ θ) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective θ g
    rw [← map_mul, ← map_mul, hy g]
  have hd'c : π d' ∈ Subgroup.center (↥K ⧸ θ) := hcen d' fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKd g.2))
  have hx'c : π x' ∈ Subgroup.center (↥K ⧸ θ) := hcen x' fun g =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) g g.2)
  have hπd' : π d' ≠ 1 := by
    intro h
    have hmem : d' ∈ θ := (QuotientGroup.eq_one_iff d').mp h
    have hord : orderOf d' = 3 := orderOf_eq_prime hd'3 hd'1
    have h3 : orderOf (⟨d', hmem⟩ : θ) = 3 := by rw [Subgroup.orderOf_mk]; exact hord
    have h := orderOf_dvd_natCard (⟨d', hmem⟩ : θ)
    rw [h3] at h
    exact hθ3 h
  have hord : orderOf (π d') = 3 := by
    refine orderOf_eq_prime ?_ hπd'
    rw [← map_pow, hd'3, map_one]
  have hZ : Subgroup.center (↥K ⧸ θ) = Subgroup.zpowers (π d') := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd'c)
    rw [hA6.1, Nat.card_zpowers, hord]
  rw [hZ] at hx'c
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx'c
  set y := x' * (d' ^ m)⁻¹ with hy
  have hyθ : y ∈ θ := by
    have h1 : π y = 1 := by rw [hy, map_mul, map_inv, map_zpow, hm, mul_inv_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hdcomm : Commute x' (d' ^ m) := (Commute.zpow_right hcomm m)
  have hdm : ((d' ^ m)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd'3, one_zpow,
      inv_one]
  have hy3 : y ^ 3 ^ (k + 1) = 1 := by
    rw [hy, (hdcomm.inv_right).mul_pow, pow_succ, pow_mul, hx'k, one_pow, one_mul,
      mul_comm (3 ^ k) 3, pow_mul, hdm, one_pow]
  have hy1 : y = 1 := by
    have h1 : orderOf y ∣ 3 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hy3
    have h2 : orderOf y ∣ Nat.card θ := by
      have : orderOf (⟨y, hyθ⟩ : θ) = orderOf y := Subgroup.orderOf_mk y hyθ
      exact this ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ (k + 1)) (Nat.card θ) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    have : orderOf y ∣ 1 := by
      rw [← hcop]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  have hxd : x' = d' ^ m := by
    rw [hy, mul_inv_eq_one] at hy1
    exact hy1
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  have h := congrArg Subtype.val hxd
  rw [SubgroupClass.coe_zpow] at h
  exact h.symm

theorem mem_sectionCentralizer_of_le_sup {A Y K : Subgroup G} {b : G} (hbA : b ∈ A)
    (hbY : b ∈ Subgroup.normalizer (Y : Set G)) (hKY : K ≤ Y)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (hY : Y ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) Y) :
    b ∈ Late.sectionCentralizer A Y (inSubgroup (aschbacherSolvableCore 3) Y) := by
  set T := inSubgroup (aschbacherSolvableCore 3) Y with hT
  have hKn : K ≤ Subgroup.normalizer (T : Set G) := hKY.trans (Sec6.le_normalizer_theta Y)
  have hbT : b ∈ Subgroup.normalizer (T : Set G) := Sec6.normalizer_le_normalizer_theta Y hbY
  refine ⟨hbA, fun y hy => ?_⟩
  have hmul : y ∈ ((K : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K T hKn]; exact hY hy
  obtain ⟨l, hl, t, ht, rfl⟩ := hmul
  have hbl : b * l = l * b := (Subgroup.mem_centralizer_singleton_iff.mp (hKb hl)).symm
  have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hbT t).mp ht
  have hcomm : b * (l * t) * b⁻¹ * (l * t)⁻¹ = l * ((b * t * b⁻¹) * t⁻¹) * l⁻¹ := by
    have : b * (l * t) * b⁻¹ = l * (b * t * b⁻¹) := by
      calc b * (l * t) * b⁻¹ = (b * l) * t * b⁻¹ := by group
        _ = (l * b) * t * b⁻¹ := by rw [hbl]
        _ = l * (b * t * b⁻¹) := by group
    rw [this]; group
  rw [hcomm]
  exact (Subgroup.mem_normalizer_iff.mp (hKn hl) _).mp (T.mul_mem hbt (T.inv_mem ht))


theorem inf_centralizer_le_of_eq_closure {B : Subgroup G} {b d : G}
    (hB : B = Subgroup.closure {b, d}) :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer (B : Set G) := by
  rintro x ⟨hxb, hxd⟩
  have hle : B ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hB, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxb).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hxd).symm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh))

theorem subgroupOf_mem_thetaComponentsIn_of_le {H M K : Subgroup G} (hMH : M ≤ H)
    (hK : K ∈ thetaComponentsIn M) : K.subgroupOf H ∈ thetaComponentsIn (M.subgroupOf H) := by
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  set e : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMH with he
  have hmem := map_mulEquiv_mem_thetaComponents Nat.prime_three e.symm hK'
  refine mem_thetaComponentsIn_iff.mpr ⟨fun z hz => ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hKM hz
  · convert hmem using 1
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv,
      MulEquiv.symm_symm, Subgroup.mem_subgroupOf]
    rfl

section Main


theorem step148HJTypeYdONA6_of_426 (h426 : Sec4.Item4_26ThetaA6) : Step148HJTypeYdONA6 := by
  intro G _ _ A c L hS Y hY _ _ B hB _ YB hYB _ _ b d Lb hc _ Yd hYd hYBYd hAYd hbn _ _ _ _ hA6
    hdYB
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, -⟩ := hc
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hbB : b ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hS.toSec13Data.commute hbA hdA)
  have hYdYC : Yd ≤ Y ⊓ C := le_of_mem_thetaComponentsIn hYd
  have hYdC : Yd ≤ C := hYdYC.trans inf_le_right
  have hYBC : YB ≤ C := hYBYd.trans hYdC
  have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
  have hYBYCB : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBb : YB ≤ Subgroup.centralizer ({b} : Set G) := hYBYCB.trans (inf_le_right.trans hCB)
  set H := Yd ⊔ Subgroup.zpowers b with hHdef
  have hYdH : Yd ≤ H := le_sup_left
  have hbH : b ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hHC : H ≤ C := sup_le hYdC (Subgroup.zpowers_le.mpr hbC)
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hS.isSimpleGroup hS.nonabelian hd1
  have hH4 : SectionFourHyp ↥H :=
    hS.toTheoremFourHyp.sectionFourHyp (fun hH => hCtop (top_le_iff.mp (hH ▸ hHC)))
  have hHN : H ≤ Subgroup.normalizer (Yd : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr (hAYd hbA))
  set L' := Yd.subgroupOf H with hL'def
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYdH).mpr hHN
  have hYdp : Group.IsPerfect Yd := isPerfect_of_mem_thetaComponentsIn hYd
  have hYdq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd
  have hL' : L' ∈ thetaComponents 3 ↥H :=
    (mem_thetaComponentsIn_iff.mp
      (Sec6.mem_thetaComponentsIn_of hYdH hYdp hL'n.isSubnormal hYdq)).2
  set c' : ↥H := ⟨b, hbH⟩ with hc'
  have hc'3 : orderOf c' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hb3 hb1
  have hΨY : Yd ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y ⊓ Subgroup.centralizer (B : Set G) := by
    rintro x ⟨hxYd, hxb⟩
    exact ⟨(hYdYC hxYd).1, inf_centralizer_le_of_eq_closure hBbd ⟨hxb, hYdC hxYd⟩⟩
  have hYBΨ : YB ≤ Yd ⊓ Subgroup.centralizer ({b} : Set G) := le_inf hYBYd hYBb
  have hYBΨmem : YB ∈ thetaComponentsIn (Yd ⊓ Subgroup.centralizer ({b} : Set G)) :=
    mem_thetaComponentsIn_iff.mpr ⟨hYBΨ, PartOne.subgroupOf_mem_thetaComponents_of_le
      Nat.prime_three hYBΨ hΨY (mem_thetaComponentsIn_iff.mp hYB).2⟩
  have hΨeq : (Yd ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf H =
      L' ⊓ Subgroup.centralizer ({c'} : Set ↥H) := by
    ext x
    simp only [hL'def, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subtype.ext h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, congrArg Subtype.val h2⟩
  set K' := YB.subgroupOf H with hK'def
  have hK' : K' ∈ thetaComponentsIn (L' ⊓ Subgroup.centralizer ({c'} : Set ↥H)) :=
    hΨeq ▸ subgroupOf_mem_thetaComponentsIn_of_le (inf_le_left.trans hYdH) hYBΨmem
  have hYBH : YB ≤ H := hYBYd.trans hYdH
  let eK : ↥K' ≃* ↥YB := Subgroup.subgroupOfEquivOfLe hYBH
  have hTA6 : Sec4.IsTripleCover (↥K' ⧸ aschbacherSolvableCore 3 ↥K') (alternatingGroup (Fin 6)) :=
    Sec13.isTripleCover_of_mulEquiv (thetaQuotEquiv eK).symm hA6
  have hdH : d ∈ H := hYdH (hYBYd hdYB)
  set dH : ↥H := ⟨d, hdH⟩ with hdHdef
  have hdHc : dH ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHC g.2))
  set Y₀ := K' ⊓ Subgroup.centralizer (K' : Set ↥H) with hY₀
  have hZ : inSubgroup (CFSG.pCore 3) Y₀ ≤ Subgroup.center ↥H := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥Y₀)) ⟨w, hw⟩
    have hk1 : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hwk : ((w : ↥H) : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun u : ↥Y₀ => ((u : ↥H) : G)) hk1
      simpa using this
    have hwYB : ((w : ↥H) : G) ∈ YB := w.2.1
    have hwC : ((w : ↥H) : G) ∈ Subgroup.centralizer (YB : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := Subgroup.mem_centralizer_iff.mp w.2.2 ⟨y, hYBH hy⟩
        (Subgroup.mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_mem_center hdYB (hYBC) hd3 hd1 hA6 hwYB hwC hwk)
    have hw' : (w : ↥H) = dH ^ m := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    change (w : ↥H) ∈ Subgroup.center ↥H
    rw [hw']
    exact Subgroup.zpow_mem _ hdHc m
  have hZne : inSubgroup (CFSG.pCore 3) Y₀ ≠ ⊥ := by
    have hdK : dH ∈ K' := Subgroup.mem_subgroupOf.mpr hdYB
    have hdKC : dH ∈ Subgroup.centralizer (K' : Set ↥H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t _
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHC t.2))
    set w : ↥Y₀ := ⟨dH, hdK, hdKC⟩ with hw
    have hwcomm : ∀ y : ↥Y₀, y * w = w * y := fun y =>
      Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHC (y : ↥H).2)))
    have hwn : (Subgroup.zpowers w).Normal := ⟨fun n hn g => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [((Commute.zpow_right (hwcomm g) m)).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers w m⟩
    have hw3 : w ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hd3))
    have hw1 : w ≠ 1 := fun h1 => hd1 (congrArg (fun u : ↥Y₀ => ((u : ↥H) : G)) h1)
    have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    have hwp : IsPGroup 3 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo, pow_one])
    have hwP : w ∈ CFSG.pCore 3 ↥Y₀ :=
      (le_sSup ⟨hwn, hwp⟩ : Subgroup.zpowers w ≤ CFSG.pCore 3 ↥Y₀) (Subgroup.mem_zpowers w)
    intro hbot
    have hmem : (w : ↥H) ∈ inSubgroup (CFSG.pCore 3) Y₀ := ⟨w, hwP, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hd1 (congrArg Subtype.val hmem)
  let eL : ↥L' ≃* ↥Yd := Subgroup.subgroupOfEquivOfLe hYdH
  rcases h426 ↥H hH4 L' hL' c' hc'3 K' hK' hTA6 hZne hZ with h1 | ⟨n, hn, -, hn2⟩ | ⟨hON, -⟩
  ·
    exfalso
    have hθmap : (inSubgroup (aschbacherSolvableCore 3) L').map H.subtype =
        inSubgroup (aschbacherSolvableCore 3) Yd := by
      rw [inSubgroup, inSubgroup, Subgroup.map_map,
        ← CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eL, Subgroup.map_map]
      rfl
    have hYdeq : Yd = YB ⊔ inSubgroup (aschbacherSolvableCore 3) Yd := by
      calc Yd = L'.map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hYdH).symm
        _ = (K' ⊔ inSubgroup (aschbacherSolvableCore 3) L').map H.subtype :=
          congrArg (Subgroup.map H.subtype) h1
        _ = YB ⊔ inSubgroup (aschbacherSolvableCore 3) Yd := by
          rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hYBH, hθmap]
    exact hbn (mem_sectionCentralizer_of_le_sup hbA (hAYd hbA) hYBYd hYBb (le_of_eq hYdeq))
  · exact absurd hn2
      (Sec13.not_isSLThreePiAt_two_pow (Sec13.card_eq_of_isTripleCover_six hTA6) hn)
  · exact Sec13.isTripleCover_of_mulEquiv (thetaQuotEquiv eL) hON

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
