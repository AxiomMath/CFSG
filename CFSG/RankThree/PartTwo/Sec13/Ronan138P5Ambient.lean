module

import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138P5

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem isList46_of_mem_thetaComponentsAt (h46 : Sec4.Item4_6) {x : G} (hx : orderOf x = 3)
    (hM : SectionFourHyp (Subgroup.centralizer ({x} : Set G))) {Lx : Subgroup G}
    (hLx : Lx ∈ thetaComponentsAt 3 x) : Sec4.IsList46 (Lx ⧸ aschbacherSolvableCore 3 Lx) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hLx
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxZ : (⟨x, hxC⟩ : C) ∈ Subgroup.center C :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hZ3 : 3 ∣ Nat.card (Subgroup.center C) := by
    have h := orderOf_dvd_natCard (⟨⟨x, hxC⟩, hxZ⟩ : Subgroup.center C)
    rwa [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hx] at h
  have h := h46 C hM hZ3 (Lx.subgroupOf C) hL'
  set e₀ : Lx.subgroupOf C ≃* Lx := Subgroup.subgroupOfEquivOfLe hLC with he₀
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv
    (QuotientGroup.congr _ _ e₀
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e₀)) h

end CFSG.RankThree.PartTwo.Sec13.Ronan138P5
