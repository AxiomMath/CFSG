module

public import CFSG.Walter.FinalNative
public import CFSG.Walter.W67.Section6.Lemma65
public import CFSG.Walter.Ree.Thompson2.BaseGrp
public import CFSG.Walter.FinalRee

public section

universe u v w

namespace CFSG.Open

open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    (∃ f : ℕ, 2 ≤ f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (G ≃* PSL(2, GaloisField p f))) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nat.card G = ordRee (3 ^ (2 * m + 1))) ∨
    Nonempty (G ≃* walterJ1) :=
  Walter.walter_order_form_of_lemma65_base Walter.W67.lemma_6_5 Walter.Ree.T2.baseExists G hnonab
    P hP

end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) (hP : IsMulCommutative (P : Subgroup G)) :
    (∃ f : ℕ, 2 ≤ f ∧ Blueprint.LieModel G .PSL 2 2 f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Blueprint.LieModel G .PSL 2 p f) ∨
    (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Blueprint.LieModel G .twistedG2 0 3 f) ∨
      Blueprint.NativeSporadic.IsSporadic G .J1 :=
  Walter.walter_models_native_of_lemma65_base Walter.W67.lemma_6_5 Walter.Ree.T2.baseExists G
    hnonab P hP

end CFSG.Open
