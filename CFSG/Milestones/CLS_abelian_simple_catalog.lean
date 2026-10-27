module

public import CFSG.Assembly.InCatalog

public section

universe u v w

namespace CFSG.Assembly

theorem _root_.CFSG.Milestones.cls_abelian_simple_catalog (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hcomm : ∀ a b : G, a * b = b * a) : InCatalog G :=
  _root_.CFSG.Assembly.abelian_simple G hcomm

end CFSG.Assembly
