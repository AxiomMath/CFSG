module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartTwo.Sec21.UniqueFixedPoint
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

public section

namespace CFSG.RankThree.Holt

open CFSG.RankThree.PartTwo.Sec21 CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem uniqueFixed_iff {N : Subgroup G} {z : G} :
    (∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N)) ↔ ∀ g : G, g⁻¹ * z * g ∈ N ↔ g ∈ N := by
  constructor
  · intro h g
    rw [← smul_mk_eq_iff, ← mk_eq_mk_one_iff]
    exact h g
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [smul_mk_eq_iff, mk_eq_mk_one_iff]
      exact h g

theorem existsUnique_fixed_of_uniqueFixed {N : Subgroup G} {z : G}
    (hfix : ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N)) : ∃! q : G ⧸ N, z • q = q :=
  ⟨((1 : G) : G ⧸ N), (hfix _).mpr rfl, fun q hq => (hfix q).mp hq⟩

end CFSG.RankThree.Holt
