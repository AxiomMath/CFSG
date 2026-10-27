module

public import CFSG.Quasithin.Background.C126NatBlock
public import CFSG.Quasithin.Background.C126NatFstar
public import CFSG.Quasithin.Background.C1PackClassG
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Quasithin.Background.C1GNA7Base
public import CFSG.Quasithin.Background.C1PackSolvBasic

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem perfectCore_le_centralizer_of_solvable {P V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hPN : P ≤ Subgroup.normalizer (V : Set G)) (hsolv : Group.IsSolvable ↥(autI hV P)) :
    perfectCore P ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have h1 : (perfectCore (P.subgroupOf (Subgroup.normalizer (V : Set G)))).map
      (Subgroup.normalizer (V : Set G)).subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPN]
  rw [← h1] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h2 : (perfectCore (P.subgroupOf (Subgroup.normalizer (V : Set G)))).map (convI hV) = ⊥ := by
    rw [map_perfectCore]
    exact (isSolvable_iff_perfectCore_eq_bot _).1 hsolv
  have h3 : convI hV y = 1 := by
    have : convI hV y ∈ (perfectCore (P.subgroupOf (Subgroup.normalizer (V : Set G)))).map
        (convI hV) := Subgroup.mem_map_of_mem _ hy
    rw [h2, Subgroup.mem_bot] at this
    exact this
  exact (convI_eq_one_iff hV y).1 h3

theorem inClassG_of_e23 (hE23 : E2.E23Statement) {P S MP : Subgroup G}
    (h : MinParabolic P S MP) (hF : CharTwo P) (hSQ : IsSQTKTC P) (hS : baum S = S)
    (hJ : ¬ thompsonJ S ≤ Subgroup.centralizer (VZ S P : Set G)) : InClassG P S := by
  obtain ⟨-, hVel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo h.isSylow hF (le_refl _)
  have hc := hE23 G P S MP (VZ S P) hVel h (C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ) hF hred hJ
  have hPN : P ≤ Subgroup.normalizer (VZ S P : Set G) := hred.2.1
  obtain ⟨L, n, hPL, hnat⟩ := exists_single_block_e23 hVel h hS hPN hc
  by_cases hn : 2 ≤ n
  · exact ⟨h.isSylow, hF, (minParabolic_iff.1 h).1,
      hasNaturalFstar_of_single_block hVel hPN hPL hn hnat⟩
  · have hn1 : n = 1 := by
      obtain ⟨h1, -⟩ := hnat
      omega
    subst hn1
    obtain ⟨-, F, iF, iFin, hF2, e, -⟩ := hnat
    have hLsolv : Group.IsSolvable ↥L := by
      have hq : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; simpa using hF2
      have : Finite F := Finite.of_fintype F
      have hc6 : Nat.card ↥L = 6 := by
        rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
          hq]
        norm_num
      exact CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hc6]; norm_num)
    have hUV : ¬ P ≤ Subgroup.centralizer (VZ S P : Set G) := fun hle =>
      hJ ((B6.thompsonJ_le S).trans (h.isSylow.1.trans hle))
    have hperf := perfectCore_le_centralizer_of_solvable hVel hPN (hPL ▸ hLsolv)
    have hsolv : Group.IsSolvable ↥P := C1Pack.isSolvable_of_perfectCore_le h hred hUV hperf
    exact C1Pack.inClassG_of_solvable_minParabolic h hF hsolv
      (C1Pack.pRank_le_two_of_isSQTKTC hSQ) hJ hS

end CFSG.Quasithin.C126.Nat
