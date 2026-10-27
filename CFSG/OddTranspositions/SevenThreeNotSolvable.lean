module

public import CFSG.OddTranspositions.SevenThreeKind
public import CFSG.OddTranspositions.SolvableTriangles

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem thirdK_not_solvable (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    ¬ Group.IsSolvable ↥(thirdK D ((u * v * w) ^ n)) := by
  intro hsolv
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := thirdK D z
  let ΔK : Set K := K.subtype ⁻¹' Delta D z
  have hthird := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  obtain ⟨hz2, hz1, hzu, hzv, hzw, hbD⟩ := hthird
  have huΔ : u ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.1, hzu.symm⟩
  have hvΔ : v ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.2.1, hzv.symm⟩
  have hwΔ : w ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.2.2.1, hzw.symm⟩
  have huK : (⟨u, Delta_subset_thirdK huΔ⟩ : K) ∈ ΔK := huΔ
  have hvK : (⟨v, Delta_subset_thirdK hvΔ⟩ : K) ∈ ΔK := hvΔ
  have hwK : (⟨w, Delta_subset_thirdK hwΔ⟩ : K) ∈ ΔK := hwΔ
  have hNK : IsNormalSet ΔK := by
    intro k x hx
    have hxΔ : (x : G) ∈ Delta D z := hx
    have hxD : (x : G) ∈ D := (mem_Delta_iff.mp hxΔ).1
    have hxz : Commute (x : G) z := (mem_Delta_iff.mp hxΔ).2
    have hkz : Commute (k : G) z :=
      (Subgroup.mem_centralizer_iff.mp (thirdK_le_centralizer k.2) z
        (Set.mem_singleton z)).symm
    change ((k * x * k⁻¹ : K) : G) ∈ Delta D z
    refine mem_Delta_iff.mpr ⟨hS.normal (k : G) (x : G) hxD, ?_⟩
    exact ((hkz.symm.mul_right hxz.symm).mul_right hkz.symm.inv_right).symm
  have hoddK : IsOddTransp ΔK := by
    constructor
    · intro x hx
      rw [← Subgroup.orderOf_coe]
      exact hS.oddT.1 _ (mem_Delta_iff.mp hx).1
    · intro x hx y hy
      have h := hS.oddT.2 (x : G) (mem_Delta_iff.mp hx).1 (y : G) (mem_Delta_iff.mp hy).1
      have hcoe : orderOf (x * y : K) = orderOf ((x : G) * (y : G)) := by
        rw [← Subgroup.orderOf_coe]
        simp
      rwa [hcoe]
  have hgenK : Subgroup.closure ΔK = ⊤ := by
    change Subgroup.closure ((Subgroup.closure (Delta D z)).subtype ⁻¹' Delta D z) = ⊤
    exact Subgroup.closure_preimage_eq_top _
  have htriK : IsTriangle ΔK ⟨u, Delta_subset_thirdK huΔ⟩
      ⟨w, Delta_subset_thirdK hwΔ⟩ ⟨v, Delta_subset_thirdK hvΔ⟩ := by
    refine ⟨huK, hvK, hwK, ?_, ?_, ?_, ?_⟩
    · intro h
      exact htri.2.2.2.1 (Subtype.ext_iff.mp h)
    · exact (commute_iff_eq _ _).mpr (Subtype.ext htri.2.2.2.2.1.eq)
    · intro h
      exact htri.2.2.2.2.2.1 ((commute_iff_eq _ _).mpr (by
        simpa using congrArg (fun x : K => (x : G)) h.eq))
    · intro h
      exact htri.2.2.2.2.2.2 ((commute_iff_eq _ _).mpr (by
        simpa using congrArg (fun x : K => (x : G)) h.eq))
  have h4 := triangle_secondKind_of_solvable hNK hoddK hgenK hsolv htriK
  have h4' : orderOf (u * v * w) = 4 := by
    have := h4
    rw [← Subgroup.orderOf_coe] at this
    simpa using this
  rw [hord] at h4'
  obtain ⟨k, hk⟩ := hn
  rw [hk] at h4'
  omega

end CFSG.OddTranspositions
