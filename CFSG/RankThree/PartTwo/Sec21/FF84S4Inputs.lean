module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.Assembly.ComponentTypeDefs
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly (InCatalog)

@[expose] def LemmaSz : Prop :=
  ∀ (H : Type) [Group H] [Finite H], IsSimpleGroup H → (∃ x y : H, x * y ≠ y * x) →
    KCore.KGroupNonab InCatalog H → ¬ 3 ∣ Nat.card H → 5 ∣ Nat.card H

variable {G : Type} [Group G]

structure FF84Post [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G) : Prop where
  sec : FF84Sec4 b L B K b₁ b₂
  z1 : Subgroup.center L = ⊥
  o3 : Opp 3 (Cen b) = ⊥
  o3' : Opp 3 (Cen (b * b₁)) = ⊥
  cB : CenS B = B
  cb : Subgroup.zpowers b ⊔ L = Cen b
  cbL : Subgroup.zpowers b ⊓ L = ⊥

theorem post_of_items (h43 : FF84_4_3) (h44 : FF84_4_4) (h46 : FF84_4_6) [Finite G]
    {b : G} {L B K : Subgroup G} {b₁ b₂ : G} (h : FF84Sec4 b L B K b₁ b₂) :
    FF84Post b L B K b₁ b₂ :=
  ⟨h, (h43 G b L B K b₁ b₂ h).2, (h44 G b L B K b₁ b₂ h).1, (h44 G b L B K b₁ b₂ h).2,
    (h46 G b L B K b₁ b₂ h).1, (h46 G b L B K b₁ b₂ h).2.1, (h46 G b L B K b₁ b₂ h).2.2⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
