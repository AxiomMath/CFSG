module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofUnitary
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofTools
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts

section Kinds


@[expose] def K419OneFieldCensus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsComponent L →
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ x a : G, x ^ 3 = 1 → x * a = a * x →
    (InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
    a ∈ Subgroup.normalizer (L : Set G) → orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → IsType419 K →
      InducesStdKind L a .field ∨ InducesStdKind L a .graphField

end Kinds

open Res419Two

theorem k419OneField_of
    (h46 : Item4_6) (hC : K419OneFieldCensus) : K419OneField := by
  intro G _ _ L A c a K hcfg ht hx
  obtain ⟨hG, hL, hA, -, hAc, hc, ha, hac, hK, hKc, -⟩ := hcfg
  obtain ⟨x, hxA, hxk⟩ := hx
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_ne_comm_of_isComponent hKc
  have haL : a ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_le hL hK hy hz hyz
  have ha3 : a ^ 3 = 1 := hA.prop.2 a ha
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have haC : a ∉ Subgroup.centralizer (L : Set G) := fun h => hac (hAc ▸ ⟨ha, h⟩)
  have hcL : c ∈ Subgroup.centralizer (L : Set G) :=
    (show c ∈ A ⊓ Subgroup.centralizer (L : Set G) from hAc ▸ Subgroup.mem_zpowers c).2
  have hxa : x * a = a * x :=
    congrArg Subtype.val (hA.prop.1.is_comm.comm ⟨x, hxA⟩ ⟨a, ha⟩)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hC G L hL (isList46_of_centralizer h46 hG hL hc hcL) x a (hA.prop.2 x hxA) hxa hxk haL
    (orderOf_eq_prime ha3 ha1) haC K hK hKc ht

end CFSG.RankThree.PartTwo.Sec4
