module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootBase
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.GH74.Uniqueness.Bender CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender
open Subgroup

variable {P : Type} [Group P] [Finite P] {n : ℕ}

section Certified


theorem IsPSUGp.exists_sylow_centralizer_of_odd (hP : IsPSUGp P 3 n) (Q : Sylow 2 P)
    {X : Subgroup P} (hX : Odd (Nat.card X))
    (hXC : X ≤ centralizer ((sylowCenter Q : Subgroup P) : Set P)) :
    ∃ Q' : Sylow 2 P, Q' ≠ Q ∧ X ≤ centralizer ((sylowCenter Q' : Subgroup P) : Set P) := by
  have hn : 2 ≤ n := two_le_of_isPSUGp hP
  have hB : BenderType P n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    benderType_of_lieModel_PSU3 hP
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have hZroot : sylowCenter Q = rootCenter (Q : Subgroup P) := rfl
  have hcardZ : Nat.card (sylowCenter Q) = 2 ^ n := by
    rw [hZroot]
    exact hc.card_center
  have hcard_gt : 1 < Nat.card (sylowCenter Q) := by
    rw [hcardZ]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  haveI : Nontrivial (sylowCenter Q) := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  obtain ⟨z, hzZ, hz1⟩ := Subgroup.exists_ne_one_of_nontrivial (sylowCenter Q)
  have hzroot : z ∈ rootCenter (Q : Subgroup P) := hZroot ▸ hzZ
  have hset : ({z} : Set P) ⊆ (sylowCenter Q : Set P) := by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hzZ
  have hXz : X ≤ centralizer ({z} : Set P) :=
    hXC.trans (Subgroup.centralizer_le hset)
  have hXsup : X ≤ (Q : Subgroup P) ⊔ fixCartan (Q : Subgroup P) t := by
    rw [← hc.centralizer_eq hzroot hz1]
    exact hXz
  have hAM : X ≤ borel (Q : Subgroup P) :=
    hXsup.trans (sup_le (le_borel _) (by
      exact (fixCartan_le_cartan (Q : Subgroup P) t).trans
        (cartan_le_borel (Q : Subgroup P) t)))
  obtain ⟨q', hq'Q, hconj⟩ := hc.exists_conj_cartan_of_odd (Q.isPGroup') hAM hX
  have hconj_fix : ∀ a ∈ X, q' * a * q'⁻¹ ∈ fixCartan (Q : Subgroup P) t := by
    intro a ha
    have haz : a ∈ centralizer ({z} : Set P) := Subgroup.centralizer_le hset (hXC ha)
    have hq'z : q' ∈ centralizer ({z} : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ((mem_rootCenter_iff.mp hzroot).2 q' hq'Q).symm
    have hc_cent : q' * a * q'⁻¹ ∈ centralizer ({z} : Set P) :=
      (centralizer ({z} : Set P)).mul_mem
        ((centralizer ({z} : Set P)).mul_mem hq'z haz)
        ((centralizer ({z} : Set P)).inv_mem hq'z)
    rw [← hc.cartan_inf_centralizer_eq hzroot hz1]
    exact Subgroup.mem_inf.mpr ⟨hconj a ha, hc_cent⟩
  have hconjSub : conjSubgroup X (q'⁻¹) ≤ fixCartan (Q : Subgroup P) t := by
    intro x hx
    have hxX : q'⁻¹ * x * q' ∈ X := by
      have h := mem_conjSubgroup_iff.mp hx
      rwa [inv_inv] at h
    have hfix := hconj_fix (q'⁻¹ * x * q') hxX
    have hid : q' * (q'⁻¹ * x * q') * q'⁻¹ = x := by group
    rwa [hid] at hfix
  have hfix_le : fixCartan (Q : Subgroup P) t ≤
      centralizer (conjSubgroup (rootCenter (Q : Subgroup P)) t : Set P) := by
    have hmono : conjSubgroup (fixCartan (Q : Subgroup P) t) t ≤
        conjSubgroup (centralizer (rootCenter (Q : Subgroup P) : Set P)) t :=
      E3.conjSubgroup_mono_left t (by
        rw [BenderCore.centralizer_rootCenter_eq hc]
        exact le_sup_right)
    rw [E3.conjSubgroup_centralizer] at hmono
    intro d hd
    apply hmono
    rw [mem_conjSubgroup_iff]
    have hdt : t * d * t⁻¹ = d := by
      rw [inv_eq_of_mul_self hc.sq_eq_one]
      exact (hc.mem_fixCartan_iff.mp hd).2
    rwa [hdt]
  obtain ⟨Q'', hQ''sub, hQ''cent⟩ := sylowCenter_conj_exists Q (t * q')
  have hne : Q'' ≠ Q := by
    intro hEq
    have hconjQ : conjSubgroup (Q : Subgroup P) (t * q') = (Q : Subgroup P) := by
      rw [← hQ''sub, hEq]
    have hgN : t * q' ∈ borel (Q : Subgroup P) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconjQ
    have hq'B : q' ∈ borel (Q : Subgroup P) := le_borel _ hq'Q
    have htB : t ∈ borel (Q : Subgroup P) := by
      have h1 : (t * q') * q'⁻¹ ∈ borel (Q : Subgroup P) :=
        (borel (Q : Subgroup P)).mul_mem hgN ((borel (Q : Subgroup P)).inv_mem hq'B)
      have hid : (t * q') * q'⁻¹ = t := by group
      rwa [hid] at h1
    exact hc.not_mem htB
  refine ⟨Q'', hne, ?_⟩
  have hle1 : conjSubgroup X (q'⁻¹) ≤
      centralizer (conjSubgroup (rootCenter (Q : Subgroup P)) t : Set P) :=
    hconjSub.trans hfix_le
  have hle2 := E3.conjSubgroup_mono_left q' hle1
  rw [E3.conjSubgroup_inv_conj, E3.conjSubgroup_centralizer, conjSubgroup_conjSubgroup]
    at hle2
  rw [hQ''cent]
  exact hle2

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
