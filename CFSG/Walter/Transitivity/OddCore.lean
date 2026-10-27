module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Walter.Transitivity

open CFSG

section Abstract

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem eq_bot_of_coprime_of_pCore_le_normalizer
    (hchar : Subgroup.centralizer (pCore p H : Set H) ≤ pCore p H) {L : Subgroup H}
    (hL : Nat.Coprime p (Nat.card L))
    (hPL : pCore p H ≤ Subgroup.normalizer (L : Set H)) : L = ⊥ := by
  have hdisj : Disjoint L (pCore p H) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := H)).exists_card_eq
    rw [hn]
    exact (hL.pow_left n).symm
  have hcent : L ≤ Subgroup.centralizer (pCore p H : Set H) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hcP : l * s * l⁻¹ * s⁻¹ ∈ pCore p H :=
      (pCore p H).mul_mem ((pCore_normal (p := p) (G := H)).conj_mem s hs l)
        ((pCore p H).inv_mem hs)
    have hcL : l * s * l⁻¹ * s⁻¹ ∈ L := by
      have h : s * l⁻¹ * s⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hPL hs) l⁻¹).1 (L.inv_mem hl)
      simpa [mul_assoc] using L.mul_mem hl h
    have hc : l * s * l⁻¹ * s⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj hcL hcP
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm
  refine eq_bot_iff.mpr fun l hl => ?_
  exact Subgroup.disjoint_def.mp hdisj hl (hchar (hcent hl))

theorem le_pPrimeCore_of_sylow_le_normalizer [Group.IsSolvable H] (P : Sylow p H)
    {L : Subgroup H} (hL : Nat.Coprime p (Nat.card L))
    (hPL : (P : Subgroup H) ≤ Subgroup.normalizer (L : Set H)) : L ≤ pPrimeCore p H := by
  let N : Subgroup H := pPrimeCore p H
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hcore : pPrimeCore p (H ⧸ N) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hchar : Subgroup.centralizer (pCore p (H ⧸ N) : Set (H ⧸ N)) ≤ pCore p (H ⧸ N) := by
    rw [← Fitting_eq_pcore (H ⧸ N) p hcore]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  have hPbar : pCore p (H ⧸ N) ≤ (Sylow.mapSurjective hsurj P : Subgroup (H ⧸ N)) :=
    (pCore_isPGroup (p := p) (G := H ⧸ N)).le_sylow_of_normal _
  have hbot : L.map (QuotientGroup.mk' N) = ⊥ := by
    refine eq_bot_of_coprime_of_pCore_le_normalizer hchar
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd L _) hL) (hPbar.trans ?_)
    rw [Sylow.coe_mapSurjective]
    exact (Subgroup.map_mono hPL).trans (Subgroup.le_normalizer_map _)
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

end Abstract

section Ambient

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_map_pPrimeCore_of_sylow_le_normalizer {Y : Subgroup G} [Group.IsSolvable Y]
    (T : Sylow p G) (hTY : (T : Subgroup G) ≤ Y) {L : Subgroup G} (hLY : L ≤ Y)
    (hL : Nat.Coprime p (Nat.card L))
    (hTL : (T : Subgroup G) ≤ Subgroup.normalizer (L : Set G)) :
    L ≤ (pPrimeCore p Y).map Y.subtype := by
  have hcard : Nat.card (L.subgroupOf Y) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv
  have hle : L.subgroupOf Y ≤ pPrimeCore p Y := by
    refine le_pPrimeCore_of_sylow_le_normalizer (T.subtype hTY) (hcard ▸ hL) ?_
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hLY]
    exact fun x hx => hTL hx
  have h := Subgroup.map_mono (f := Y.subtype) hle
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLY] at h

omit [Finite G] [Fact p.Prime] in
theorem le_normalizer_map_pPrimeCore (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (((pPrimeCore p Y).map Y.subtype : Subgroup G) : Set G) := by
  intro y hy
  have hmem : (⟨y, hy⟩ : Y) ∈ Subgroup.normalizer (pPrimeCore p Y : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  exact Subgroup.le_normalizer_map Y.subtype ⟨⟨y, hy⟩, hmem, rfl⟩

theorem coprime_card_map_pPrimeCore (Y : Subgroup G) :
    Nat.Coprime p (Nat.card ((pPrimeCore p Y).map Y.subtype : Subgroup G)) := by
  rw [Subgroup.card_map_of_injective Y.subtype_injective]
  exact pPrimeCore_coprime_card

end Ambient

end CFSG.Walter.Transitivity
