module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Data
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4V2
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructMain
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Lo2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G}

theorem ff79_3_4_of_in (hO : FF79KLemmaOP) (hG : IsSimpleGroup G)
    (hna : ∃ x y : G, x * y ≠ y * x) (hKp : KProper InCatalog G) (hs : FF79Sec3 b J)
    (h : FF79Sec34In b J B A P D) :
    ∀ a ∈ B ⊓ J, orderOf a = 3 → IsLnq 2 2 2 (Lay (J ⊓ Cen a)) →
      IsElemAb 3 2 (U34 b a J A) ∧ b ∈ Nor (U34 b a J A) ∧
        IsLnq 3 2 2 (⊤ : Subgroup (layer (CenS (U34 b a J A) ⧸
          pPrimeCore 3 (CenS (U34 b a J A))))) := by
  intro a ha hoa hK
  have hU := sec34_UFacts hs h ha hoa hK
  have haC : a ∈ CenS (U34 b a J A) := by
    intro x hx
    haveI := hU.elemU.1
    have := (IsMulCommutative.is_comm (M := ↥(U34 b a J A))).comm ⟨x, hx⟩ ⟨a, hU.a_mem⟩
    exact congrArg Subtype.val this
  have hd := sec34_APData hG hna hKp hs h hU hoa hK haC
  obtain ⟨L, hL⟩ := ap_struct hd
  have := ap_of_struct_K hO hd.beta3 hL hd.K_fix hd.K_a5
  exact ⟨hU.elemU, hU.b_nor, this⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
