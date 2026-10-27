module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem zl_aut_eq_one {Bs K : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hnt : GGNoTransvection 3 Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) {θ : MulAut ↥Bs} (hθ : θ ∈ ggAutomizer K Bs)
    (hθb : ∀ b : ↥Bs, ((b⁻¹ * θ b : ↥Bs) : G) ∈ Subgroup.zpowers y) : θ = 1 := by
  have hθy := ggAutomizer_fix_of_centralizes hyBs hKy θ hθ
  rcases ggAut_eq_one_or_isTransvection hyBs hy1 hBs hθy hθb with h | htv
  · exact h
  · exfalso
    obtain ⟨g, -, hgN, hθg⟩ := mem_ggAutomizer_iff.mp hθ
    exact hnt θ ⟨g, Subgroup.mem_top g, hgN, hθg⟩ htv

end ZL

end E6Dep

end CFSG.StandardType

end
