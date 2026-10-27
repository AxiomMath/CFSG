module

public import CFSG.Quasithin.EmptyFaithful.ModHLocalPair
public import CFSG.Quasithin.EmptyFaithful.ModHJ2Core
public import CFSG.Quasithin.EmptyFaithful.ModHEl
public import CFSG.Sporadic.Schreier.RuIso
public import CFSG.Sporadic.Schreier.RuOuter

public section

namespace CFSG.Quasithin.ModH.RuEl

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Sporadic.RuSchreier CFSG.Quasithin.ModH.SylowCore CFSG.Quasithin.R3c14

theorem ru_fixing_central
    (α : MulAut ruP) (hα : ∀ s ∈ (ruSylow : Subgroup ruP), α s = s) :
    ∃ c : ruP, c ∈ (Subgroup.center (ruSylow : Subgroup ruP)).map (ruSylow : Subgroup ruP).subtype ∧
      ∀ x, α x = c * x * c⁻¹ := by
  refine LocalPair.exists_conj_of_local_pair_strong ruSylow (ruC.subgroupOf ruP) ruCP_eq
    (ruK.subgroupOf ruP) (Subgroup.subgroupOf_mono _ ruK_leS) (ruN.subgroupOf ruP) ruNP_eq
    (ruJ.subgroupOf ruP) (isPGroup_ruJ.of_equiv (Subgroup.subgroupOfEquivOfLe ruJ_le).symm)
    (Subgroup.subgroupOf_mono _ ruJ_leS) (Subgroup.subgroupOf_mono _ ruJ_leC) ?_ ?_ ?_ ?_ ?_ α hα
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono _ ruJ_leC)]
    intro h k hh hk
    rw [mem_subgroupOf_iff] at hh hk ⊢
    exact (Subgroup.normal_subgroupOf_iff ruJ_leC).1 ruJ_normal h k hh hk
  · intro x hx
    obtain ⟨hxC, hxJ⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruJ_le, mem_subgroupOf_iff] at hxJ
    rw [mem_subgroupOf_iff] at hxC ⊢
    exact ruCentralizer_J ⟨hxC, hxJ⟩
  · intro x hx
    obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruK_le, mem_subgroupOf_iff] at hxK
    rw [mem_subgroupOf_iff] at hxN ⊢
    exact ruCentralizer_K ⟨hxN, hxK⟩
  · rw [← Subgroup.subgroupOf_sup ruC_le ruN_le, ← ruP_eq_sup, Subgroup.subgroupOf_self]
  · exact Subgroup.subgroupOf_mono _ ruS_leN

theorem ru_fixing_strong
    (α : MulAut ruP) (hα : ∀ s ∈ (ruSylow : Subgroup ruP), α s = s) :
    α = 1 ∨ α = MulAut.conj (⟨ruZ, ruZ_mem⟩ : ruP) := by
  obtain ⟨c, hcZ, hc⟩ := ru_fixing_central α hα
  have hcZ' : c ∈ ((Subgroup.center (ruSP : Subgroup ruP)).map ruSP.subtype : Subgroup ruP) := hcZ
  rw [ruSP_center] at hcZ'
  have hcz : (c : Equiv.Perm (Fin 4060)) = 1 ∨ (c : Equiv.Perm (Fin 4060)) = ruZ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hcZ')
    rw [← hk, ← zpow_mod_orderOf, orderOf_ruZ]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp [h]
    · right
      simp [h]
  rcases hcz with h | h
  · left
    have hc1 : c = 1 := Subtype.ext h
    exact MulEquiv.ext fun x => by rw [hc x, hc1]; simp
  · right
    have hc1 : c = ⟨ruZ, ruZ_mem⟩ := Subtype.ext h
    exact MulEquiv.ext fun x => by rw [hc x, hc1, MulAut.conj_apply]

theorem strongSylow_ruP :
    StrongSylow ruP := by
  have hzS : (⟨ruZ, ruZ_mem⟩ : ruP) ∈ (ruSylow : Subgroup ruP) :=
    Subgroup.mem_subgroupOf.2 ruZ_memS
  refine ⟨ruSylow, ⟨ruZ, ruZ_mem⟩, hzS, ?_, fun α hα => ru_fixing_strong α hα⟩
  intro t ht
  have hz : (⟨ruZ, ruZ_mem⟩ : ruP) ∈
      ((Subgroup.center (ruSP : Subgroup ruP)).map ruSP.subtype : Subgroup ruP) := by
    rw [ruSP_center]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _)
  obtain ⟨y, hy, hyz⟩ := hz
  have h1 := Subgroup.mem_center_iff.1 hy (⟨t, ht⟩ : ruSP)
  have h2 : t * (y : ruP) = (y : ruP) * t := congrArg (fun u : ruSP => (u : ruP)) h1
  have h3 : (y : ruP) = ⟨ruZ, ruZ_mem⟩ := hyz
  rw [h3] at h2
  exact h2.symm

theorem strongSylow_ru :
    StrongSylow (NativeSporadic.Carrier .Ru) :=
  @StrongSylow.of_equiv (NativeSporadic.Carrier .Ru) ruP _ _ _ ruEquivP strongSylow_ruP

theorem center_eq_bot_ru :
    Subgroup.center (NativeSporadic.Carrier .Ru) = ⊥ := by
  have hs : IsSimpleGroup (NativeSporadic.Carrier .Ru) := (CFSG.Sporadic.Ru.fam_ru_simplicity).2.2
  have hc : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (NativeSporadic.Carrier .Ru)) with h1 | h1
  · exact h1
  · exfalso
    have : IsMulCommutative (NativeSporadic.Carrier .Ru) := Subgroup.center_eq_top_iff.1 h1
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hc] at hp
    norm_num at hp

theorem not_elConfig_ru :
    ¬ ElConfig (NativeSporadic.Carrier .Ru) := by
  have hs := strongSylow_ru
  have hZ := center_eq_bot_ru
  have : Finite (NativeSporadic.Carrier .Ru) := (CFSG.Sporadic.Ru.fam_ru_simplicity).1
  obtain ⟨P, hP⟩ := hs.exists_center_small hZ
  exact ModH.not_elConfig_of_center hs.pointwise
    (ModH.centerSmall_of_one (K1.isSylowTwoOf_top_iff.2 ⟨P.isPGroup', P.not_dvd_index⟩) hP)

end CFSG.Quasithin.ModH.RuEl
