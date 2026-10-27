module

public import Mathlib.Data.Fintype.CardEmbedding
public import CFSG.Permutation.FiveTransitive.OyamaEightLocalAction
public import CFSG.Permutation.FiveTransitive.ThreeOrbitNormalizerFixed

public section

namespace CFSG

namespace FiveTransitive.OyamaThreeOrbitOrders

open MulAction

@[expose] def ThreeOrbits (G X:Type*) [Group G] [MulAction G X] : Prop :=
  ∀s:Set X,s.ncard=3 → Nat.card (orbitRel.Quotient (fixingSubgroup G s)
    (SubMulAction.ofFixingSubgroup G s))=3

private theorem normalizer_card_le
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:ThreeOrbits G X)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    Nat.card (FixedSetNormalizerHom.fixedPermHom G X A).range≤120 := by
  classical
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let F := fixedPoints A X
  let f := FixedSetNormalizerHom.fixedPermHom G X A
  let J := f.range
  let _ := Fintype.ofFinite F
  have hc:Nat.card F=6 := (hcond.2.1 b P).1
  let e:Fin 3 ↪ F := (Fin.castLEEmb (show 3≤Nat.card F by omega)).trans (Finite.equivFin F).symm.toEmbedding
  let eX:Fin 3 ↪ X := e.trans (Function.Embedding.subtype _)
  let s:Set X := Set.range eX
  have hs:s.ncard=3 := by simpa only [Nat.card_fin] using Set.ncard_range_of_injective eX.injective
  have hAs:A≤fixingSubgroup G s := by
    intro a ha
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨i,rfl⟩
    exact mem_fixedPoints.mp (e i).property ⟨a,ha⟩
  have heven:Even (Nat.card X) := Nat.even_iff.mpr
    (EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1)
  have hfour:OyamaTripleSylow.FourFixedSix G X := by
    intro t ht T
    exact (EvenSixTupleLocal.to_set_property hcond.2.1 t ht T).1
  have hid (n:J) (hn:n • e=e):n=1 := by
    obtain ⟨g,hg⟩ := n.property
    have hgs:g.val∈fixingSubgroup G s := by
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨i,rfl⟩
      have hi := DFunLike.congr_fun hn i
      have hiv := congrArg Subtype.val hi
      change (n.val (e i)).val=(e i).val at hiv
      rw [←hg] at hiv
      exact hiv
    have hfix := ThreeOrbitNormalizerFixed.fixes_six_of_fixes_three heven hfour s hs
      (horb s hs) A (P.isPGroup'.map (stabilizer G b).subtype) hAs hc
      g.val hgs g.property
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (n.val x).val=x.val
    rw [←hg]
    exact hfix x.val x.property
  have hinj:Function.Injective (fun n:J => n • e) := by
    intro n m h
    have heq := hid (m⁻¹*n) (by
      calc
        (m⁻¹*n:J) • e=m⁻¹ • (n • e) := mul_smul _ _ _
        _ = m⁻¹ • (m • e) := congrArg (fun z:Fin 3 ↪ F => m⁻¹ • z) h
        _ = e := inv_smul_smul m e)
    have hm := congrArg (fun z:J => m*z) heq
    simpa only [mul_inv_cancel_left,mul_one] using hm
  have hle := Nat.card_le_card_of_injective (fun n:J => n • e) hinj
  have hF:Fintype.card F=6 := by rwa [←Nat.card_eq_fintype_card]
  have hEmbed:Nat.card (Fin 3 ↪ F)=120 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq,Fintype.card_fin,hF]
    norm_num [Nat.descFactorial]
  rw [hEmbed] at hle
  exact hle

theorem normalizer_card_eq_sixty
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:ThreeOrbits G X)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    Nat.card (FixedSetNormalizerHom.fixedPermHom G X A).range=60 := by
  have hle := normalizer_card_le hcond horb b P
  have hcases := OyamaEightLocalAction.normalizer_card hcond b P
  rcases hcases with h|h
  · exact h
  · omega

theorem normalizer_pair_fixer_card
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:ThreeOrbits G X)
    (b:Fin 4 ↪ X) (P:Sylow 2 (stabilizer G b))
    (s:Set (fixedPoints ((P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype) X))
    (hs:s.ncard=2) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    Nat.card (fixingSubgroup (FixedSetNormalizerHom.fixedPermHom G X A).range s)=2 := by
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let J := (FixedSetNormalizerHom.fixedPermHom G X A).range
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  have h6:Fintype.card (fixedPoints A X)=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact (hcond.2.1 b P).1
  have hi := TwoTransitiveA6Card.two_fixer_index h6 J
    (OyamaNormalizerTwoTransitive.two_transitive hcond b P) s hs
  have hm := (fixingSubgroup J s).index_mul_card
  have hcard := normalizer_card_eq_sixty hcond horb b P
  change Nat.card J=60 at hcard
  rw [hi,hcard] at hm
  change Nat.card (fixingSubgroup J s)=2
  omega

end FiveTransitive.OyamaThreeOrbitOrders

end CFSG
