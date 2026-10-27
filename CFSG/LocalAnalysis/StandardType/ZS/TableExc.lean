module

public import CFSG.LocalAnalysis.StandardType.ZS.TablePair
import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem throughRefl_of_propOneEightAt [Module.Finite (ZMod p) U] {m : ℕ}
    (hm : Module.finrank (ZMod p) U = m) (h4 : 4 ≤ m) (h18 : PropOneEightAt p m)
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hT : TableHyp p J)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J) (hone : OneClass p J) {d : ℕ}
    (hd : DMax p J d) (hd3 : 3 < d) : ThroughRefl p (m - 1) J := by
  have hR : IsRGroup p J := ⟨hT.reflGen, hT.transvectionFree⟩
  obtain ⟨N, hNJ, hNgen, hNsplit, _⟩ := h18 h4 U J hm hR hT.irreducible hprim d hd hd3
  have hm4 : 0 < m - 1 := by omega
  obtain ⟨x, hxN, hxrefl⟩ := exists_isRefl_of_splitSupport hNgen hNsplit hm4
  exact throughRefl_of_oneClass hone hNJ hxN hxrefl hNgen hNsplit

theorem tableConclusions_of_dMax_three (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J) (hone : OneClass p J) {d : ℕ}
    (hd : DMax p J d) (hcop : Nat.Coprime d p) (h2 : 2 < d) : TableConclusions p 3 J := by
  refine ⟨Or.inl hneg, coprimeWitness_of_neg_mem hp hneg, ?_⟩
  obtain ⟨x, hxJ, y, hyJ, hrx, hry, hxy⟩ := hd.2
  have hcop' : Nat.Coprime (orderOf (x * y)) p := by rw [hxy]; exact hcop
  have h2' : 2 < orderOf (x * y) := by rw [hxy]; exact h2
  exact throughRefl_two_of_oneClass hp hone hxJ hyJ hrx hry hcop' h2'

theorem tableConclusions_of_dMax_four (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hU : Module.finrank (ZMod p) U = 4) {J : Subgroup (U ≃ₗ[ZMod p] U)} (hT : TableHyp p J)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J) (hone : OneClass p J) {d : ℕ}
    (hd : DMax p J d) (hd3 : 3 < d) (h18 : PropOneEightAt p 4) : TableConclusions p 4 J := by
  refine ⟨Or.inl hneg, coprimeWitness_of_neg_mem hp hneg, ?_⟩
  exact throughRefl_of_propOneEightAt hU (le_refl 4) h18 hT hprim hone hd hd3

theorem tableConclusions_exc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (k : ExcRow) (hadm : k.admissible p)
    (hdeg : Module.finrank (ZMod p) U = k.deg) (hcen : Nat.card (Subgroup.center J) = k.cen)
    (hd : DMax p J k.dmax) (hone : OneClass p J) (hT : TableHyp p J)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J)
    (h18 : PropOneEightAt p (Module.finrank (ZMod p) U)) :
    TableConclusions p (Module.finrank (ZMod p) U) J := by
  have hA : AbsIrred p J := absIrred_of_reflGen hT.reflGen hT.irreducible
  have h2c : 2 ∣ Nat.card (Subgroup.center J) := by
    rw [hcen]
    cases k <;> norm_num [ExcRow.cen]
  have h0c : Nat.card (Subgroup.center J) ≠ 0 := by
    rw [hcen]
    cases k <;> norm_num [ExcRow.cen]
  have hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J :=
    neg_mem_of_two_dvd_card_center hA h2c h0c
  cases k
  · rw [hdeg]
    exact tableConclusions_of_dMax_four hp hdeg hT hprim hneg hone hd
      (by norm_num [ExcRow.dmax]) (by simpa [hdeg, ExcRow.deg] using h18)
  · rw [hdeg]
    exact tableConclusions_of_dMax_four hp hdeg hT hprim hneg hone hd
      (by norm_num [ExcRow.dmax]) (by simpa [hdeg, ExcRow.deg] using h18)
  · exfalso
    obtain ⟨x, hxJ, y, hyJ, hrx, hry, hxy⟩ := hT.dLarge
    exact absurd (hd.1 x hxJ y hyJ hrx hry) (not_le.mpr hxy)
  · exfalso
    obtain ⟨x, hxJ, y, hyJ, hrx, hry, hxy⟩ := hT.dLarge
    exact absurd (hd.1 x hxJ y hyJ hrx hry) (not_le.mpr hxy)
  · rw [hdeg]
    exact tableConclusions_of_dMax_four hp hdeg hT hprim hneg hone hd
      (by norm_num [ExcRow.dmax]) (by simpa [hdeg, ExcRow.deg] using h18)
  · rw [hdeg]
    have hcop : Nat.Coprime 5 p := (Nat.coprime_primes Nat.prime_five Fact.out).mpr (Ne.symm hadm)
    exact tableConclusions_of_dMax_three hp hneg hone hd hcop (by norm_num [ExcRow.dmax])
  · rw [hdeg]
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp)
    have hcop : Nat.Coprime 4 p := by simpa using Nat.Coprime.pow_left 2 h2p
    exact tableConclusions_of_dMax_three hp hneg hone hd hcop (by norm_num [ExcRow.dmax])
  · rw [hdeg]
    have h6 : 6 ∣ p - 1 := by
      have := card_center_dvd_sub_one hA
      rwa [hcen] at this
    have hp5 : p ≠ 5 := by
      intro h
      rw [h] at h6
      norm_num at h6
    have hcop : Nat.Coprime 5 p := (Nat.coprime_primes Nat.prime_five Fact.out).mpr (Ne.symm hp5)
    exact tableConclusions_of_dMax_three hp hneg hone hd hcop (by norm_num [ExcRow.dmax])
  · exfalso
    have h6 : 6 ∣ p - 1 := by
      have := card_center_dvd_sub_one hA
      rwa [hcen] at this
    rw [hadm] at h6
    norm_num at h6
  · rw [hdeg]
    exact tableConclusions_of_dMax_four hp hdeg hT hprim hneg hone hd
      (by norm_num [ExcRow.dmax]) (by simpa [hdeg, ExcRow.deg] using h18)

end CFSG.StandardType.ZS
