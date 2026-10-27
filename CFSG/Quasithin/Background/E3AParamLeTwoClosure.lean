module

public import CFSG.Quasithin.Background.RonanE42Small
public import CFSG.Quasithin.Background.B1Key
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.LocalAnalysis.ComponentClassification.ThompsonAB

public section

namespace CFSG.Quasithin.E3

open CFSG.Quasithin
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem aParam_le_two_of_E8GenClosure (hW : ∀ w : W, w ^ 2 = 1) (Y : Subgroup (MulAut W))
    (hE8 : ∀ A : Subgroup ↥Y, (∀ a ∈ A, a ^ 2 = 1) → 8 ≤ Nat.card A →
      Nat.card A = 8 ∧
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set ↥Y)) = ⊤ ∧
      ∃ a ∈ A, a ≠ 1 ∧ 3 ∣ Nat.card ↥(Subgroup.normalClosure (A : Set ↥Y) ⊓
        Subgroup.centralizer ({a} : Set ↥Y))) :
    E3.aParam Y ≤ 2 := by
  classical
  refine CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty Y 2 ?_
  intro A hA
  rw [E3.aSet, Set.mem_setOf_eq] at hA
  obtain ⟨hAY, hAne, hAel, hAfix⟩ := hA
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hAel.2
  have hAp : IsPGroup 2 A := hAel.isPGroup
  have hcard_gt : 4 < Nat.card A := by
    by_contra hnot
    push Not at hnot
    have hm : E3.mQuot A ⊥ < 3 := by
      have hcard := E3.card_eq_two_pow_mul hAp (bot_le : (⊥ : Subgroup (MulAut W)) ≤ A)
      rw [Subgroup.card_bot, mul_one] at hcard
      rw [hcard] at hnot
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4] at hnot
      have h2 : E3.mQuot A ⊥ ≤ 2 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hnot
      omega
    have hfixbot : fixV (⊥ : Subgroup (MulAut W)) = fixV A := hAfix ⊥ bot_le hm
    have htop : fixV A = ⊤ := by
      rw [← hfixbot]
      exact CFSG.Quasithin.B1.fixV_bot
    exact hAne (CFSG.Quasithin.B1.eq_bot_of_fixV_eq_top htop)
  have hA8 : 8 ≤ Nat.card A := by
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hn3 : 3 ≤ n := by
      by_contra h
      have hn2 : n ≤ 2 := by omega
      have hle : Nat.card A ≤ 4 := by
        rw [hn]
        calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
          _ = 4 := by norm_num
      omega
    rw [hn]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  let A' : Subgroup ↥Y := A.subgroupOf Y
  have hA'card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  have hA'elem : ∀ a ∈ A', a ^ 2 = 1 := by
    intro a ha
    have haA : (a : MulAut W) ∈ A := Subgroup.mem_subgroupOf.mp ha
    exact Subtype.ext (by simpa using hA2 (a : MulAut W) haA)
  have hA'eight : 8 ≤ Nat.card A' := by rw [hA'card]; exact hA8
  obtain ⟨hA'card8, hcent, aY, haY, haY1, hthree_a⟩ := hE8 A' hA'elem hA'eight
  have hcard8 : Nat.card A = 8 := by
    rw [← hA'card]
    exact hA'card8
  let U : Subgroup W := fixV A
  have hfix_a : ∀ a : ↥Y, a ∈ A' → a ≠ 1 →
      fixV (Subgroup.zpowers (a : MulAut W)) = U := by
    intro a haA' ha1
    have haA : (a : MulAut W) ∈ A := Subgroup.mem_subgroupOf.mp haA'
    have ha1' : (a : MulAut W) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hsq : (a : MulAut W) ^ 2 = 1 := hA2 _ haA
    have horder : orderOf (a : MulAut W) = 2 := orderOf_eq_prime hsq ha1'
    have hcardZ : Nat.card (Subgroup.zpowers (a : MulAut W)) = 2 := by
      rw [Nat.card_zpowers, horder]
    have hzA : Subgroup.zpowers (a : MulAut W) ≤ A := Subgroup.zpowers_le.2 haA
    have hm2 : E3.mQuot A (Subgroup.zpowers (a : MulAut W)) = 2 := by
      have hcard := E3.card_eq_two_pow_mul hAp hzA
      rw [hcard8, hcardZ] at hcard
      have hpow : 2 ^ E3.mQuot A (Subgroup.zpowers (a : MulAut W)) = 2 ^ 2 := by
        have : 2 ^ E3.mQuot A (Subgroup.zpowers (a : MulAut W)) = 4 := by omega
        simpa using this
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
    exact hAfix _ hzA (by omega)
  let N : Subgroup (MulAut W) :=
    { carrier := {g | (∀ u ∈ U, g u ∈ U) ∧ (∀ u ∈ U, g⁻¹ u ∈ U)}
      one_mem' := by
        refine ⟨?_, ?_⟩
        · intro u hu
          simpa using hu
        · intro u hu
          simpa using hu
      mul_mem' := by
        intro g h hg hh
        refine ⟨fun u hu => hg.1 (h u) (hh.1 u hu), ?_⟩
        intro u hu
        have hgu : g⁻¹ u ∈ U := hg.2 u hu
        have hhgu : h⁻¹ (g⁻¹ u) ∈ U := hh.2 (g⁻¹ u) hgu
        simpa [mul_inv_rev, MulAut.mul_apply] using hhgu
      inv_mem' := by
        intro g hg
        exact ⟨fun u hu => hg.2 u hu, fun u hu => by simpa using hg.1 u hu⟩ }
  have hHle : ∀ a : ↥Y, a ∈ A' → a ≠ 1 →
      (Subgroup.centralizer ({a} : Set ↥Y)).map Y.subtype ≤ N := by
    intro a haA' ha1
    refine Subgroup.map_le_iff_le_comap.2 ?_
    intro y hy
    have hca : a * y = y * a := (Subgroup.mem_centralizer_iff.mp hy) a (by simp)
    have hca' : (a : MulAut W) * (y : MulAut W) = (y : MulAut W) * (a : MulAut W) :=
      Subtype.ext_iff.mp hca
    have hfixa : fixV (Subgroup.zpowers (a : MulAut W)) = U := hfix_a a haA' ha1
    have huZ : ∀ u ∈ U, u ∈ fixV (Subgroup.zpowers (a : MulAut W)) := by
      intro u hu
      rw [hfixa]
      exact hu
    refine ⟨?_, ?_⟩
    · intro u hu
      have hau : (a : MulAut W) u = u := mem_fixV_zpowers_iff.mp (huZ u hu)
      have hay : (a : MulAut W) ((y : MulAut W) u) = (y : MulAut W) u := by
        calc (a : MulAut W) ((y : MulAut W) u)
            = ((a : MulAut W) * (y : MulAut W)) u := rfl
          _ = ((y : MulAut W) * (a : MulAut W)) u := by rw [hca']
          _ = (y : MulAut W) ((a : MulAut W) u) := rfl
          _ = (y : MulAut W) u := by rw [hau]
      have hyuZ : (y : MulAut W) u ∈ fixV (Subgroup.zpowers (a : MulAut W)) :=
        mem_fixV_zpowers_iff.mpr hay
      rw [hfixa] at hyuZ
      exact hyuZ
    · intro u hu
      have hau : (a : MulAut W) u = u := mem_fixV_zpowers_iff.mp (huZ u hu)
      have hcaInv : (a : MulAut W) * (y : MulAut W)⁻¹ =
          (y : MulAut W)⁻¹ * (a : MulAut W) := by
        have hcomm : Commute (y : MulAut W) (a : MulAut W) := hca'.symm
        exact (hcomm.inv_left).eq.symm
      have hay : (a : MulAut W) ((y : MulAut W)⁻¹ u) = (y : MulAut W)⁻¹ u := by
        calc (a : MulAut W) ((y : MulAut W)⁻¹ u)
            = ((a : MulAut W) * (y : MulAut W)⁻¹) u := rfl
          _ = ((y : MulAut W)⁻¹ * (a : MulAut W)) u := by rw [hcaInv]
          _ = (y : MulAut W)⁻¹ ((a : MulAut W) u) := rfl
          _ = (y : MulAut W)⁻¹ u := by rw [hau]
      have hyuZ : (y : MulAut W)⁻¹ u ∈ fixV (Subgroup.zpowers (a : MulAut W)) :=
        mem_fixV_zpowers_iff.mpr hay
      rw [hfixa] at hyuZ
      exact hyuZ
  have hYleN : Y ≤ N := by
    have hmap : (⨆ a ∈ A', ⨆ (_ : a ≠ 1),
        Subgroup.centralizer ({a} : Set ↥Y)).map Y.subtype = Y := by
      rw [hcent, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap]
    refine Subgroup.map_le_iff_le_comap.2 ?_
    exact iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 =>
      (Subgroup.map_le_iff_le_comap).mp (hHle a ha ha1)
  let K : Subgroup ↥Y :=
    { carrier := {y | ∀ u ∈ U, (y : MulAut W) u = u}
      one_mem' := by intro u hu; rfl
      mul_mem' := by
        intro g h hg hh u hu
        change ((g : MulAut W) * (h : MulAut W)) u = u
        rw [MulAut.mul_apply, hh u hu, hg u hu]
      inv_mem' := by
        intro g hg u hu
        have h := congrArg (fun v => (g : MulAut W)⁻¹ v) (hg u hu)
        simpa using h.symm }
  have hAK : A' ≤ K := by
    intro a ha
    intro u hu
    exact (CFSG.Quasithin.mem_fixV.mp hu) (a : MulAut W) (Subgroup.mem_subgroupOf.mp ha)
  have hKnormal : K.Normal := by
    refine ⟨?conj_mem⟩
    intro k hk g u hu
    have hgu : (g : MulAut W)⁻¹ u ∈ U := (hYleN g.2).2 u hu
    have hkgu : (k : MulAut W) ((g : MulAut W)⁻¹ u) = (g : MulAut W)⁻¹ u :=
      hk ((g : MulAut W)⁻¹ u) hgu
    change ((g : MulAut W) * (k : MulAut W) * (g : MulAut W)⁻¹) u = u
    rw [MulAut.mul_apply, MulAut.mul_apply, hkgu]
    exact MulAut.apply_inv_self (M := W) (g : MulAut W) u
  have hncK : Subgroup.normalClosure (A' : Set ↥Y) ≤ K := by
    have : K.Normal := hKnormal
    exact Subgroup.normalClosure_le_normal hAK
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' 3 (hp := ⟨Nat.prime_three⟩) hthree_a
  let xY : ↥Y := (x : ↥Y)
  have hxYnc : xY ∈ Subgroup.normalClosure (A' : Set ↥Y) := (Subgroup.mem_inf.mp x.2).1
  have hxYmem : xY ∈ Subgroup.centralizer ({aY} : Set ↥Y) := (Subgroup.mem_inf.mp x.2).2
  have hxYK : xY ∈ K := hncK hxYnc
  have hxcomm : aY * xY = xY * aY :=
    (Subgroup.mem_centralizer_iff.mp hxYmem) aY (by simp)
  have hxcomm' : (aY : MulAut W) * (xY : MulAut W) = (xY : MulAut W) * (aY : MulAut W) :=
    Subtype.ext_iff.mp hxcomm
  have hxY3 : (xY : MulAut W) ^ 3 = 1 := by
    have hx3 : x ^ 3 = 1 := by
      rw [← hxord]
      exact pow_orderOf_eq_one x
    simpa [xY] using congrArg (fun z : ↥(Subgroup.normalClosure (A' : Set ↥Y) ⊓
      Subgroup.centralizer ({aY} : Set ↥Y)) => ((z : ↥Y) : MulAut W)) hx3
  have hxYne : (xY : MulAut W) ≠ 1 := by
    intro h
    have hxYone : xY = 1 := (Subgroup.subtype_injective Y) (by simpa using h)
    have hxone : x = 1 := Subtype.ext hxYone
    rw [hxone, orderOf_one] at hxord
    omega
  have horder_a : orderOf (aY : MulAut W) = 2 := by
    have haA : (aY : MulAut W) ∈ A := Subgroup.mem_subgroupOf.mp haY
    exact orderOf_eq_prime (hA2 _ haA) (fun h => haY1 (Subtype.ext h))
  have hBp : IsPGroup 2 (Subgroup.zpowers (aY : MulAut W)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, horder_a, pow_one]
  have hcommutes : ∀ element : Subgroup.zpowers (aY : MulAut W),
      Commute (xY : MulAut W) ((Subgroup.zpowers (aY : MulAut W)).subtype element) := by
    intro element
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp element.2
    change Commute (xY : MulAut W) (element : MulAut W)
    rw [← hk]
    exact Commute.zpow_right
      (show Commute (xY : MulAut W) (aY : MulAut W) from hxcomm'.symm) k
  have hfixed : ∀ member : W,
      (∀ element : Subgroup.zpowers (aY : MulAut W),
        (Subgroup.zpowers (aY : MulAut W)).subtype element member = member) →
      (xY : MulAut W) member = member := by
    intro member hmem
    have hamem : (aY : MulAut W) member = member :=
      hmem ⟨(aY : MulAut W), Subgroup.mem_zpowers (aY : MulAut W)⟩
    have hmemU : member ∈ U := by
      rw [← hfix_a aY haY haY1]
      exact mem_fixV_zpowers_iff.mpr hamem
    exact hxYK member hmemU
  have hx1 : (xY : MulAut W) = 1 :=
    CFSG.ComponentClassification.ThompsonAB.coprime_eq_one (V := W)
      (B := Subgroup.zpowers (aY : MulAut W)) 2
      (CFSG.Quasithin.isPGroup_two_of_sq_eq_one hW) hBp
      (Subgroup.subtype (Subgroup.zpowers (aY : MulAut W))) (xY : MulAut W)
      hcommutes hfixed 3 hxY3 (by norm_num)
  exact hxYne hx1

end CFSG.Quasithin.E3
