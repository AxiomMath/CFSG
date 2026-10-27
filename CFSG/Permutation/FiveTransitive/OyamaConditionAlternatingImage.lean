module

public import CFSG.Permutation.FiveTransitive.OyamaConditionFourTransitive

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionAlternatingImage

open MulAction

private theorem sylow_at_fixed_embedding
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b))
    (c:Fin 4 ↪ fixedPoints ((P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype) X) :
    ∃R:Sylow 2 (stabilizer G (c.trans (Function.Embedding.subtype _))),
      (R:Subgroup (stabilizer G (c.trans (Function.Embedding.subtype _)))).map
        (stabilizer G (c.trans (Function.Embedding.subtype _))).subtype =
      (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype := by
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let cX:Fin 4 ↪ X := c.trans (Function.Embedding.subtype _)
  have hA:IsPGroup 2 A := P.isPGroup'.map (stabilizer G b).subtype
  have hAc:A≤stabilizer G cX := by
    intro a ha
    apply Function.Embedding.ext
    intro i
    exact mem_fixedPoints.mp (c i).property ⟨a,ha⟩
  obtain ⟨R,hR⟩ := LocalSylowFixedMaximal.exists_sylow_containing (stabilizer G cX) A hA hAc
  let B := (R:Subgroup (stabilizer G cX)).map (stabilizer G cX).subtype
  have hfix:4≤Nat.card (fixedPoints B X) := by
    have hc:Nat.card (fixedPoints B X)=6 := (hcond.2.1 cX R).1
    omega
  exact ⟨R,LocalSylowFixedMaximal.eq_of_four_fixed hcond.2.1 b P B
    (R.isPGroup'.map (stabilizer G cX).subtype) hR hfix⟩

private theorem image_four_transitive
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    IsMultiplyPretransitive (FixedSetNormalizerHom.fixedPermHom G X A).range (fixedPoints A X) 4 := by
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let f := FixedSetNormalizerHom.fixedPermHom G X A
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  rw [isMultiplyPretransitive_iff]
  intro c d
  let cX:Fin 4 ↪ X := c.trans (Function.Embedding.subtype _)
  let dX:Fin 4 ↪ X := d.trans (Function.Embedding.subtype _)
  obtain ⟨R,hR⟩ := sylow_at_fixed_embedding hcond b P c
  obtain ⟨S,hS⟩ := sylow_at_fixed_embedding hcond b P d
  obtain ⟨g,hg,hmap⟩ := StabilizerSylowConjugacy.exists_conjugating_transporter cX dX
    (h4.exists_smul_eq cX dX) R S
  rw [hR,hS] at hmap
  have hgn:g∈Subgroup.normalizer (A:Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  let n:Subgroup.normalizer (A:Set G) := ⟨g,hgn⟩
  refine ⟨⟨f n,⟨n,rfl⟩⟩,?_⟩
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  exact DFunLike.congr_fun hg i

theorem image_eq_alternating
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    letI := Fintype.ofFinite (fixedPoints A X)
    letI := Classical.decEq (fixedPoints A X)
    (FixedSetNormalizerHom.fixedPermHom G X A).range=alternatingGroup (fixedPoints A X) := by
  intro A
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  apply le_antisymm (OyamaNormalizerTwoTransitive.image_le_alternating hcond b P)
  apply IsMultiplyPretransitive.alternatingGroup_le
  have hdeg:Nat.card (fixedPoints A X)-2=4 := by
    have hc:Nat.card (fixedPoints A X)=6 := (hcond.2.1 b P).1
    omega
  rw [hdeg]
  exact image_four_transitive hcond b P

end FiveTransitive.OyamaConditionAlternatingImage

end CFSG
