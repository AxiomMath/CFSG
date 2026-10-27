module

public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Defs

structure Sec11StdLocal (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) (a : G) (R Y : Subgroup G) : Prop extends Sec8.Hyp81 G A c L a where
  card_eq : Nat.card A = 27
  invTwo_or_commutator : (Sec8.InvTwoBarNontrivial A L ∨
    ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
      ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
        Sec4.thetaQuotCentralizer L) ∨
    (¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) ∧
      ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8)
  isSylowOf : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G))
  isSylowOf_inf : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ Subgroup.normalizer (A : Set G))
    (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G))
  isList1016 : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)
  mem_thetaComponentsAt_Y : Y ∈ thetaComponentsAt 3 a
  sec11K_le : sec11K L a ≤ Y

structure ResidueConfig (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) (a : G) (R Y : Subgroup G) (d : G) : Prop
    extends Sec11StdLocal G A c L a R Y where
  inf_eq_zpowers : A ⊓ L = Subgroup.zpowers d
  not_mem_zpowers : d ∉ Subgroup.zpowers c
  normalizer_le : Subgroup.normalizer (A : Set G) ≤
    Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G)
  isIrreducibleOn : Sec21.IsIrreducibleOn
    (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d}))
  isSylowOf_top : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤
  threeElement_centralizes : ∀ w ∈ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) →
    ∀ b ∈ Subgroup.closure ({c, d} : Set G), w * b * w⁻¹ = b
  mem_sd16 : ∀ w ∈ Subgroup.normalizer (A : Set G),
    (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
    (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
    (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
    (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))
  closure_eq : Subgroup.closure ({c, d, a} : Set G) = A
  exists_transvection : ∀ b ∈ Subgroup.closure ({c, d} : Set G),
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∀ y ∈ Subgroup.closure ({c, d} : Set G), w * y * w⁻¹ = y) ∧ w * a * w⁻¹ = a * b
  conj_mem_of_mem_normalizer : ∀ w ∈ Subgroup.normalizer (A : Set G),
    w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G)
  residue :
    (Even (Nat.card (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({a} : Set G)))) ∧
      (∀ w ∈ Subgroup.normalizer (A : Set G),
        (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
        (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c)) ∧
      ∃ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d ∧
        n * d * n⁻¹ ∈ Subgroup.zpowers c ∧ n * a * n⁻¹ = a⁻¹) ∨
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))

end Defs

section Glue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem Sec11Std.toSec11StdLocal (h : Sec11Std G A c L a R Y) : Sec11StdLocal G A c L a R Y :=
  { h.toHyp81 with
    card_eq := h.card_eq
    invTwo_or_commutator := h.invTwo_or_commutator
    isSylowOf := h.isSylowOf
    isSylowOf_inf := h.isSylowOf_inf
    isList1016 := h.isList1016
    mem_thetaComponentsAt_Y := h.mem_thetaComponentsAt_Y
    sec11K_le := h.sec11K_le }

theorem Sec11StdLocal.toSec11StdOfCtx (h : Sec11StdLocal G A c L a R Y)
    (hctx : A ∉ partTwoT G ∨ A ∈ partTwoS G) : Sec11Std G A c L a R Y :=
  { h.toHyp81 with
    card_eq := h.card_eq
    invTwo_or_commutator := h.invTwo_or_commutator
    isSylowOf := h.isSylowOf
    isSylowOf_inf := h.isSylowOf_inf
    not_mem_partTwoT_or_mem_partTwoS := hctx
    isList1016 := h.isList1016
    mem_thetaComponentsAt_Y := h.mem_thetaComponentsAt_Y
    sec11K_le := h.sec11K_le }

theorem Sec11StdLocal.toSec11Std (h : Sec11StdLocal G A c L a R Y) (hT : A ∉ partTwoT G) :
    Sec11Std G A c L a R Y :=
  h.toSec11StdOfCtx (Or.inl hT)

end Glue

end CFSG.RankThree.PartTwo.Sec11
