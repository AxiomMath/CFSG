module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityUniqueAction

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding
open CFSG.OrderReductions.UniqueInvolutionAction
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality
open CFSG.ProperTwoGeneratedCore

universe u v

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem localNormalizer_normal_odd_join_quotient
    (L U : Subgroup G) [L.Normal] (hUodd : Odd (Nat.card U)) :
    Odd (Nat.card ((L ⊔ U : Subgroup G) ⧸ L.subgroupOf (L ⊔ U))) := by
  let F := L ⊔ U
  let LF := L.subgroupOf F
  let q := QuotientGroup.mk' LF
  let f : U →* (F ⧸ LF) := q.comp (Subgroup.inclusion (le_sup_right : U ≤ F))
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective LF x
    obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp g.property
    let lF : F := ⟨l, (le_sup_left : L ≤ F) hl⟩
    let tF : F := ⟨t, (le_sup_right : U ≤ F) ht⟩
    have hprod : lF * tF = g := Subtype.ext hlt
    have hlone : q lF = 1 := by
      change lF ∈ q.ker
      rw [QuotientGroup.ker_mk']
      exact hl
    refine ⟨⟨t, ht⟩, ?_⟩
    change q tF = q g
    rw [← hprod, map_mul, hlone, one_mul]
  exact hUodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hfsurj)

theorem localNormalizer_normal_odd_join_involution_mem
    (L U : Subgroup G) [L.Normal] (hUodd : Odd (Nat.card U))
    (x : (L ⊔ U : Subgroup G)) (hx : orderOf x = 2) : (x : G) ∈ L := by
  let F := L ⊔ U
  let LF := L.subgroupOf F
  let q := QuotientGroup.mk' LF
  have hodd : Odd (Nat.card (F ⧸ LF)) :=
    localNormalizer_normal_odd_join_quotient L U hUodd
  have hsq : (q x) ^ 2 = 1 := by
    rw [← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
  have hqone : q x = 1 := square_one_eq_one_of_mem_odd_subgroup
    (⊤ : Subgroup (F ⧸ LF)) (by simpa only [Subgroup.card_top] using hodd)
    (Subgroup.mem_top _) hsq
  have hmem : x ∈ q.ker := hqone
  rw [QuotientGroup.ker_mk'] at hmem
  exact hmem

theorem localNormalizer_normal_odd_join_unique_involutions
    {Ω : Type v} [MulAction G Ω]
    (L U : Subgroup G) [L.Normal] (hUodd : Odd (Nat.card U))
    (A : Subgroup L) (hA : IsStronglyEmbedded A)
    (z : L) (hz : orderOf z = 2)
    (hzunique : ∃! a : Ω, (z : G) • a = a) :
    ∀ x : Involution (L ⊔ U : Subgroup G),
      ∃! a : Ω, x.val • a = a := by
  intro x
  have hxL := localNormalizer_normal_odd_join_involution_mem L U hUodd x.val x.property
  let xL : L := ⟨(x.val : G), hxL⟩
  have hxorder : orderOf xL = 2 := (Subgroup.orderOf_coe xL).symm.trans
    ((Subgroup.orderOf_coe x.val).trans x.property)
  have hzI : IsInvolution z := ⟨(orderOf_eq_prime_iff.mp hz).2,
    (orderOf_eq_prime_iff.mp hz).1⟩
  have hxI : IsInvolution xL := ⟨(orderOf_eq_prime_iff.mp hxorder).2,
    (orderOf_eq_prime_iff.mp hxorder).1⟩
  obtain ⟨g, hg⟩ := hA.involutions_conjugate hzI hxI
  have hgG : rightConjugateElem (z : G) (g : G) = (x.val : G) :=
    congrArg Subtype.val hg
  exact unique_fixed_of_right_conjugate (G := G) hzunique hgG

theorem localNormalizer_normal_odd_join_strong_embedding
    {Ω : Type v} [MulAction G Ω] [Finite Ω] [Nontrivial Ω]
    (L U : Subgroup G) [L.Normal] (hUodd : Odd (Nat.card U))
    (A : Subgroup L) (hA : IsStronglyEmbedded A)
    (hrank : TwoRankAtLeastTwo L)
    (htrans : MulAction.IsPretransitive L Ω)
    (z : L) (hz : orderOf z = 2)
    (hzunique : ∃! a : Ω, (z : G) • a = a) (a : Ω) :
    fusionStronglyEmbedded (MulAction.stabilizer (L ⊔ U : Subgroup G) a) ∧
      MulAction.IsMultiplyPretransitive (L ⊔ U : Subgroup G) Ω 2 := by
  let F := L ⊔ U
  let : MulAction.IsPretransitive F Ω := normal_join_action_transitive L U htrans
  let zF : F := ⟨z.val, (le_sup_left : L ≤ F) z.property⟩
  have hzF : orderOf zF = 2 := (Subgroup.orderOf_coe zF).symm.trans
    ((Subgroup.orderOf_coe z).trans hz)
  have heven : Even (Nat.card F) := even_iff_two_dvd.mpr (by
    rw [← hzF]
    exact orderOf_dvd_natCard zF)
  have hunique := localNormalizer_normal_odd_join_unique_involutions L U hUodd A hA
    z hz hzunique
  have hstrong : fusionStronglyEmbedded (MulAction.stabilizer F a) :=
    (stronglyEmbedded_right_conjugate_iff _).mp
      (stronglyEmbedded_stabilizer_of_unique_fixed heven hunique a)
  have hrankF : TwoRankAtLeastTwo F := hrank.map_of_injective
    (Subgroup.inclusion (le_sup_left : L ≤ F)) (Subgroup.inclusion_injective _)
  exact ⟨hstrong, rank_two_stronglyEmbedded_action_double_transitive
    inferInstance a hstrong hrankF⟩

end CFSG.ShultStronglyClosedTI
