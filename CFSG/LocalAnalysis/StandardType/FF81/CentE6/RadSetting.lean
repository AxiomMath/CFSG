module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Std

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

structure RadGeom {G : Type} [Group G] (t : G) (Q L : Subgroup G)
    (eL : ↥L ≃* SL(6, ZMod 2)) (π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))) (b : G) :
    Prop where
  t_mul_self : t * t = 1
  t_ne_one : t ≠ 1
  t_mem : t ∈ Q
  isPGroup : IsPGroup 2 Q
  le_cen_Q : Q ≤ Subgroup.centralizer ({t} : Set G)
  le_cen_L : L ≤ Subgroup.centralizer ({t} : Set G)
  conj_mem : ∀ l ∈ L, ∀ q ∈ Q, l * q * l⁻¹ ∈ Q
  inf_eq_bot : L ⊓ Q = ⊥
  surj : Function.Surjective π
  ker_iff : ∀ q : ↥Q, π q = 1 ↔ (q : G) ∈ Subgroup.zpowers t
  equivariant : ∀ (l : ↥L) (q : ↥Q) (hq : (l : G) * (q : G) * (l : G)⁻¹ ∈ Q),
    Multiplicative.toAdd (π ⟨(l : G) * (q : G) * (l : G)⁻¹, hq⟩) =
      cubeAct (eL l) (Multiplicative.toAdd (π q))
  b_mem : b ∈ L
  b_mark : eL ⟨b, b_mem⟩ = bStd

structure RadSetting {G : Type} [Group G] (t : G) (Q L : Subgroup G)
    (eL : ↥L ≃* SL(6, ZMod 2)) (π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))) (b : G) :
    Prop extends RadGeom t Q L eL π b where
  fuse : ∀ x y : G, x ∈ L → y ∈ L → IsConj b x → IsConj b y → ∃ l ∈ L, y = l * x * l⁻¹
  cen_le : ∀ g : G, g * t = t * g → g * b = b * g → g ∈ Q ⊔ L

end CFSG.StandardType.FF81.CentE6
