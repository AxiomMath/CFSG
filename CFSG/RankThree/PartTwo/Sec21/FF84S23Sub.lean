module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import Mathlib.GroupTheory.IsSubnormal

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open Subgroup

section Subnormal

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem map_pPrimeCore_le_of_normal' [Fact p.Prime] {H K : Subgroup G} (hle : H ≤ K)
    (hN : (H.subgroupOf K).Normal) :
    (CFSG.pPrimeCore p H).map H.subtype ≤ (CFSG.pPrimeCore p K).map K.subtype := by
  set H' : Subgroup K := H.subgroupOf K with hH'
  have : H'.Normal := hN
  let e : H' ≃* H := Subgroup.subgroupOfEquivOfLe hle
  have hA : ((CFSG.pPrimeCore p H').map H'.subtype).Normal := inferInstance
  have hAcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p H').map H'.subtype)) := by
    rw [Subgroup.card_map_of_injective H'.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hAle : (CFSG.pPrimeCore p H').map H'.subtype ≤ CFSG.pPrimeCore p K :=
    le_sSup ⟨hA, hAcop⟩
  have hid : (CFSG.pPrimeCore p H).map H.subtype =
      ((CFSG.pPrimeCore p H').map H'.subtype).map K.subtype := by
    rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso p e, Subgroup.map_map]
    rfl
  rw [hid]
  exact Subgroup.map_mono hAle

theorem map_pPrimeCore_le_of_isSubnormal' [Fact p.Prime] {H : Subgroup G}
    (hH : H.IsSubnormal) : (CFSG.pPrimeCore p H).map H.subtype ≤ CFSG.pPrimeCore p G := by
  induction hH with
  | top => exact (CFSG.pPrimeCore_map_iso p (Subgroup.topEquiv (G := G))).le
  | step H K hle hK hN ih => exact (map_pPrimeCore_le_of_normal' hle hN).trans ih

theorem le_pPrimeCore_of_isSubnormal' [Fact p.Prime] {A : Subgroup G} (hA : A.IsSubnormal)
    (hcop : Nat.Coprime p (Nat.card A)) : A ≤ CFSG.pPrimeCore p G := by
  refine le_trans ?_ (map_pPrimeCore_le_of_isSubnormal' hA)
  have htop : (⊤ : Subgroup A) ≤ CFSG.pPrimeCore p A := by
    refine le_sSup ⟨inferInstance, ?_⟩
    simpa using hcop
  intro a ha
  exact ⟨⟨a, ha⟩, htop (Subgroup.mem_top _), rfl⟩

theorem dvd_card_of_isSubnormal' (hp : p.Prime) (hcore : CFSG.pPrimeCore p G = ⊥)
    {H : Subgroup G} (hH : H.IsSubnormal) (hne : H ≠ ⊥) : p ∣ Nat.card H := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hdvd
  have hle := le_pPrimeCore_of_isSubnormal' hH ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  rw [hcore, le_bot_iff] at hle
  exact hne hle

end Subnormal

end CFSG.RankThree.PartTwo.Sec21.FF84
