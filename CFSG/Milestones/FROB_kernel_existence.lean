module

public import CFSG.Adapters.FrobeniusKernel

public section

universe u v w

namespace CFSG.FrobeniusKernel

theorem _root_.CFSG.Milestones.frobenius_kernel (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} :=
  _root_.CFSG.FrobeniusKernel.frobenius_kernel_isNormal G X hcard htrans hstab hfrob

end CFSG.FrobeniusKernel

namespace CFSG.Adapters

open Pointwise in
theorem _root_.CFSG.Milestones.frobenius_kernel_existence {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hH1 : H ≠ ⊥) (hHG : H ≠ ⊤)
    (hfrob : ∀ g : G, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥) :
    ∃ K : Subgroup G,
      (K : Set G) = {1} ∪ (Set.univ \ ⋃ g : G, ((MulAut.conj g • H : Subgroup G) : Set G)) ∧
      K.Normal ∧ (∀ x : G, ∃ k ∈ K, ∃ h ∈ H, x = k * h) ∧ K ⊓ H = ⊥ ∧
      Nat.card K = H.index :=
  _root_.CFSG.Adapters.frobenius_kernel H hH1 hHG hfrob

end CFSG.Adapters
