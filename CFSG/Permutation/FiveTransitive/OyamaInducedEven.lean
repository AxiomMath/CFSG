module

public import CFSG.Permutation.FiveTransitive.ActionImageStabilizerSylow
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitChoice
public import CFSG.Permutation.FiveTransitive.FixedNormalizerImageEven
public import CFSG.Permutation.FiveTransitive.OyamaLocalSylowFixedSet
public import CFSG.Permutation.FiveTransitive.EvenSixTupleLocal

public section

namespace CFSG

namespace FiveTransitive.OyamaInducedEven

open MulAction FixedNormalizerAction FixedNormalizerImage OyamaMinimalOrbitDescent

@[expose] abbrev InducedEven {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (Q:Subgroup G) : Prop :=
  letI := Fintype.ofFinite (Fixed (X:=X) Q)
  EvenSixTupleLocal.Property (Image (X:=X) Q) (Fixed (X:=X) Q)

theorem exists_even_descent
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4:IsMultiplyPretransitive G X 4) (a:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G a)) (hP:(P:Subgroup (stabilizer G a))≠⊥)
    (hlocal:EvenSixTupleLocal.Property G X) :
    ∃Q:Subgroup G,Q<ambientSylow a P ∧
      fixedPoints (ambientSylow a P) X ⊂ fixedPoints Q X ∧ InducedEven (X:=X) Q ∧
      ∀(b:Fin 4 ↪ Fixed (X:=X) Q)(S:Sylow 2 (stabilizer (Image (X:=X) Q) b)),
      let T := (S:Subgroup (stabilizer (Image (X:=X) Q) b)).map
        (stabilizer (Image (X:=X) Q) b).subtype
      T≠⊥ ∧ ∀t:Image (X:=X) Q,t∈T → t≠1 →
        ∀x:Fixed (X:=X) Q,x∉fixedPoints T (Fixed (X:=X) Q) → t • x≠x := by
  classical
  obtain ⟨Q,hQP,hstrict,hdescent⟩ :=
    OyamaMinimalOrbitChoice.exists_four_point_descent h4 a P hP
  let _ := Fintype.ofFinite (Fixed (X:=X) Q)
  have hall (b:Fin 4 ↪ Fixed (X:=X) Q)(S:Sylow 2 (stabilizer (Image (X:=X) Q) b)) :
      let T := (S:Subgroup (stabilizer (Image (X:=X) Q) b)).map
        (stabilizer (Image (X:=X) Q) b).subtype
      (Nat.card (fixedPoints T (Fixed (X:=X) Q))=6 ∧
        EvenSixTupleLocal.EvenFixed (Image (X:=X) Q) (Fixed (X:=X) Q) T) ∧
      T≠⊥ ∧ ∀t:Image (X:=X) Q,t∈T → t≠1 →
        ∀x:Fixed (X:=X) Q,x∉fixedPoints T (Fixed (X:=X) Q) → t • x≠x := by
    obtain ⟨R,hR⟩ := ActionImageStabilizerSylow.preimage_sylow_tuple_stabilizer
      (Normalizer Q) (Fixed (X:=X) Q) 4 b S
    obtain ⟨U,hU⟩ := sylow_localFixer_image Q b R
    have hb:∀i,ambientEmbedding b i∈fixedPoints Q X := by
      intro i
      change (b i).val∈fixedPoints Q X
      simpa only [fixed_eq] using (b i).property
    obtain ⟨hQU,hcard,hmove,_hkernel,hsemi⟩ := hdescent (ambientEmbedding b) hb U
    have hQb:Q≤stabilizer G (ambientEmbedding b) := by
      intro q hq
      apply Function.Embedding.ext
      intro i
      exact mem_fixedPoints.mp (hb i) ⟨q,hq⟩
    obtain ⟨V,hV⟩ := OyamaLocalSylowFixedSet.exists_same_fixed_set
      h4 a (ambientEmbedding b) P Q hQP hQb U hcard
    let B := (R:Subgroup (stabilizer (Normalizer Q) b)).map
      (stabilizer (Normalizer Q) b).subtype
    change (U:Subgroup ↥(Normalizer Q ⊓ stabilizer G (ambientEmbedding b))).map
      (Normalizer Q ⊓ stabilizer G (ambientEmbedding b)).subtype=Ambient B at hU
    have hQA:Q≤Ambient B := by rw [←hU]; exact hQU.le
    have hcardA:Nat.card (fixedPoints (Ambient B) X)=6 := by
      rw [←hU,hcard]
      exact (hlocal a P).1
    have hmoveA:∃r:G,r∈Ambient B ∧ ∃x∈fixedPoints Q X,r • x≠x := by rwa [←hU]
    have hsemiA:∀r:G,r∈Ambient B → r∉Q → ∀x∈fixedPoints Q X,
        x∉fixedPoints (Ambient B) X → r • x≠x := by rwa [←hU]
    have hFV:fixedPoints (Ambient B) X=fixedPoints (ambientSylow (ambientEmbedding b) V) X := by
      rwa [←hU]
    have heven:EvenSixTupleLocal.EvenFixed (Image (X:=X) Q) (Fixed (X:=X) Q)
        (Restricted (X:=X) B) := by
      intro n hn
      exact FixedNormalizerImageEven.sign_eq_one Q B hQA (ambientEmbedding b) V hFV
        (hlocal (ambientEmbedding b) V).2 n hn
    dsimp only
    rw [hR]
    exact ⟨⟨(Nat.card_congr (fixedEquiv B hQA)).trans hcardA,heven⟩,
      nontrivial_of_moves B hmoveA,semiregular B hsemiA⟩
  exact ⟨Q,hQP,hstrict,(fun b S => (hall b S).1),fun b S => (hall b S).2⟩

end FiveTransitive.OyamaInducedEven

end CFSG
