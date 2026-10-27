module

public import CFSG.OddTranspositions.SevenThreeNotSolvable
public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem Delta_inter_solvableRadical_eq_empty (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    Delta D ((u * v * w) ^ n) ∩
      ((CFSG.solvableRadical (thirdK D ((u * v * w) ^ n))).map
        (thirdK D ((u * v * w) ^ n)).subtype : Subgroup G) = ∅ := by
  classical
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := thirdK D z
  have hKns : ¬ Group.IsSolvable K := thirdK_not_solvable hS htri hn hn1 hord
  have hthird := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  obtain ⟨-, -, hzu, -, -, -⟩ := hthird
  have huΔ : u ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.1, hzu.symm⟩
  haveI hRn : (CFSG.solvableRadical K).Normal := OddTransp.solvableRadical_normal K
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxΔ, hxR⟩
  obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.mp hxR
  have hxK : (⟨x, Delta_subset_thirdK hxΔ⟩ : K) ∈ CFSG.solvableRadical K := by
    have hxr : (⟨x, Delta_subset_thirdK hxΔ⟩ : K) = r := Subtype.ext (by simpa using hre.symm)
    rwa [hxr]
  obtain ⟨c, hcK, hcu⟩ := thirdK_transitive hS hL htri hn hord x hxΔ
  have huR : (⟨u, Delta_subset_thirdK huΔ⟩ : K) ∈ CFSG.solvableRadical K := by
    have hconj := hRn.conj_mem (⟨x, Delta_subset_thirdK hxΔ⟩ : K) hxK
      (⟨c⁻¹, K.inv_mem hcK⟩ : K)
    have heq : (⟨u, Delta_subset_thirdK huΔ⟩ : K) =
        (⟨c⁻¹, K.inv_mem hcK⟩ : K) * (⟨x, Delta_subset_thirdK hxΔ⟩ : K) *
          (⟨c⁻¹, K.inv_mem hcK⟩ : K)⁻¹ := by
      apply Subtype.ext
      show u = c⁻¹ * x * (c⁻¹)⁻¹
      rw [← hcu]
      group
    rwa [heq]
  have hΔR : Delta D z ⊆ ((CFSG.solvableRadical K).map K.subtype : Subgroup G) := by
    intro y hy
    obtain ⟨c', hc'K, hc'y⟩ := thirdK_transitive hS hL htri hn hord y hy
    have hconj := hRn.conj_mem (⟨u, Delta_subset_thirdK huΔ⟩ : K) huR
      (⟨c', hc'K⟩ : K)
    refine ⟨(⟨c' * u * c'⁻¹, ?_⟩ : K), hconj, ?_⟩
    · exact K.mul_mem (K.mul_mem hc'K (Delta_subset_thirdK huΔ)) (K.inv_mem hc'K)
    · show c' * u * c'⁻¹ = y
      exact hc'y
  have hKle : K ≤ ((CFSG.solvableRadical K).map K.subtype : Subgroup G) := by
    rw [show K = Subgroup.closure (Delta D z) from rfl, Subgroup.closure_le]
    exact hΔR
  have hRtop : CFSG.solvableRadical K = ⊤ := by
    rw [eq_top_iff]
    intro k hk
    obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.mp (hKle k.2)
    have hk_eq : k = (r : K) := Subtype.ext (by simpa using hre.symm)
    rw [hk_eq]
    exact hr
  haveI hRs : Group.IsSolvable ↥(CFSG.solvableRadical K) := OddTransp.isSolvable_solvableRadical
  have hsurj : Function.Surjective (Subgroup.subtype (CFSG.solvableRadical K)) := by
    rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, hRtop]
  exact hKns (Group.isSolvable_of_surjective (f := Subgroup.subtype (CFSG.solvableRadical K)) hsurj)

end CFSG.OddTranspositions
