module

public import CFSG.CharacterTheory.BlockSectionOrthogonality

public section

universe u v w

namespace CFSG.BlockSectionOrthogonality

open CFSG in
theorem _root_.CFSG.Milestones.block_section_orthogonality (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hpm : (p : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (B : Set (G → ℂ)) (hB : BlocksIsBlock m G B)
    (x y xp yp : G) (hx : BlocksIsPPart p x xp) (hy : BlocksIsPPart p y yp)
    (hxy : ¬ IsConj xp yp) :
    ∑ᶠ χ ∈ B, χ x * starRingEnd ℂ (χ y) = 0 :=
  _root_.CFSG.BlockSectionOrthogonality.block_section_orthogonality p hp m hm hpm G B hB x y xp yp hx hy hxy

end CFSG.BlockSectionOrthogonality
