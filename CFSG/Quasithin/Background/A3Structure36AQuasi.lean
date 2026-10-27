module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.Quasithin

namespace A36A

variable {X : Type*} [Group X]

theorem center_le_fittingSubgroup : Subgroup.center X ≤ CFSG.fittingSubgroup X :=
  le_sSup (show Subgroup.center X ∈ {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} from
    ⟨inferInstance, inferInstance⟩)

theorem center_le_solvableRadical : Subgroup.center X ≤ CFSG.solvableRadical X :=
  A3.le_solvableRadical inferInstance inferInstance

theorem solvableRadical_le_center [Finite X]
    (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X) :
    CFSG.solvableRadical X ≤ Subgroup.center X := by
  set R : Subgroup X := CFSG.solvableRadical X
  have hRn : R.Normal := inferInstance
  have hRs : Group.IsSolvable ↥R := A3.solvableRadical_isSolvable
  have hFR : CFSG.fittingSubgroupOf R ≤ Subgroup.center X :=
    (CFSG.fittingSubgroupOf_le_fittingSubgroup R hRn).trans hF
  intro r hr
  have hcent : (⟨r, hr⟩ : ↥R) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥R : Set ↥R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfZ : (f : X) ∈ Subgroup.center X := hFR (Subgroup.mem_map_of_mem R.subtype hf)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hfZ r).symm
  have hrF := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hRs hcent
  exact hFR (Subgroup.mem_map_of_mem R.subtype hrF)

theorem center_eq_solvableRadical [Finite X]
    (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X) :
    Subgroup.center X = CFSG.solvableRadical X :=
  le_antisymm center_le_solvableRadical (solvableRadical_le_center hF)

theorem fittingSubgroup_eq_center (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X) :
    CFSG.fittingSubgroup X = Subgroup.center X :=
  le_antisymm hF center_le_fittingSubgroup

theorem isQuasisimple_of_fitting_le_center [Finite X] (hperf : Group.IsPerfect X)
    (hs : IsSimpleGroup (X ⧸ CFSG.solvableRadical X))
    (hna : ∃ a b : X ⧸ CFSG.solvableRadical X, a * b ≠ b * a)
    (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X) :
    CFSG.IsQuasisimple X := by
  let e : X ⧸ CFSG.solvableRadical X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientMulEquivOfEq (center_eq_solvableRadical hF).symm
  have := hs
  obtain ⟨a, b, hab⟩ := hna
  exact ⟨hperf, e.symm.isSimpleGroup, e a, e b, fun h => hab (e.injective (by
    rw [map_mul, map_mul, h]))⟩

theorem odd_card_center [Finite X] (h2 : CFSG.pCore 2 X = ⊥) :
    Odd (Nat.card (Subgroup.center X)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hdvd : 2 ∣ Nat.card (Subgroup.center X) := even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set z : X := (x : X) with hz
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe, hx]
  have hzc : Subgroup.zpowers z ≤ Subgroup.center X := Subgroup.zpowers_le.mpr x.2
  have hn : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hzc
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hz2]
    exact ⟨1, by norm_num⟩
  have hle : Subgroup.zpowers z ≤ CFSG.pCore 2 X := le_sSup ⟨hn, hp⟩
  rw [h2, le_bot_iff] at hle
  have hz1 : z = 1 := by
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [hle] at this
    exact Subgroup.mem_bot.mp this
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem oddCore_eq_center [Finite X] (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X)
    (hodd : Odd (Nat.card (Subgroup.center X))) :
    CFSG.oddCore X = Subgroup.center X := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hodd⟩)
  refine sSup_le fun N hN => ?_
  obtain ⟨hNn, hNodd⟩ := hN
  have hs : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥N hNodd
  exact ((A3.le_solvableRadical hNn hs).trans (center_eq_solvableRadical hF).ge)

theorem generalizedFitting_eq_top (hQ : CFSG.IsQuasisimple X) :
    CFSG.generalizedFitting X = ⊤ :=
  CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hQ

theorem generalizedFitting_ne_fittingSubgroup (hQ : CFSG.IsQuasisimple X)
    (hF : CFSG.fittingSubgroup X ≤ Subgroup.center X) :
    CFSG.generalizedFitting X ≠ CFSG.fittingSubgroup X := by
  intro h
  rw [generalizedFitting_eq_top hQ] at h
  rw [← h] at hF
  have hc : Subgroup.center X = ⊤ := top_le_iff.mp hF
  obtain ⟨-, -, a, b, hab⟩ := hQ
  have : Subsingleton (X ⧸ Subgroup.center X) := QuotientGroup.subsingleton_iff.mpr hc
  exact hab (Subsingleton.elim _ _)

end A36A

end CFSG.Quasithin
