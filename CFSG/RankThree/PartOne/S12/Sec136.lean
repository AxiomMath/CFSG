module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem apply_c_of_mem_torusImage {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hcE : c ∈ E) {g : MulAut E} (hg : g ∈ torusImage E L) :
    g ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
  have hnL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  show (n : G) * c * (n : G)⁻¹ = c
  rw [← Sec12Three.comm_c_L h (n : G) hnL, mul_inv_cancel_right]

@[reducible, expose] def commGroupOf {E : Subgroup G} (hEc : ∀ a b : ↥E, a * b = b * a) : CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := hEc }

end CFSG.RankThree.PartOne
