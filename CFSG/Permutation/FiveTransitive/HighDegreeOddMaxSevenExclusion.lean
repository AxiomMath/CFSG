module

public import CFSG.Permutation.FiveTransitive.HighDegreeOddTwoOrbitCyclic
public import CFSG.Permutation.FiveTransitive.CyclicTwoNormalizedSeed
public import CFSG.Permutation.FiveTransitive.CyclicTwoFullSylowActual
public import CFSG.Permutation.FiveTransitive.HighDegreeFullSylowExceptionContradiction
public import CFSG.Permutation.FiveTransitive.OddPointStabilizerFixity

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.HighDegreeOddMaxSevenExclusion

open MulAction FixedNormalizerAction

private theorem contradiction
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X))
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7) : False := by
  classical
  obtain ⟨H, hHG, _, _, _, hH5, _, heven, hentrance⟩ :=
    HighDegreeOddTwoOrbitCyclic.exists_entrance X G hcard h5 hnotAlt hodd hmax
  have hmaxH : ∀ t : H, orderOf t = 2 → (fixedBy X t).ncard ≤ 7 := by
    intro t ht
    exact hmax (Subgroup.inclusion hHG t)
      ((orderOf_injective (Subgroup.inclusion hHG) (Subgroup.inclusion_injective hHG) t).trans ht)
  obtain ⟨a⟩ : Nonempty (Fin 5 ↪ X) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  let P : Sylow 2 (stabilizer H a) := default
  obtain ⟨x, Q, _, _, _, _, _, _, h7, h7', _, _, htop, _, _, hS,
    _, _, hnmod, _, hsemi, _, _, hQtwo, _, htrans⟩ := hentrance a P
  obtain ⟨S,hS'⟩ := hS
  have hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1 := by
    intro q z hz hqz
    apply Subtype.ext
    by_contra hq
    exact hsemi q.val q.property hq z hz hqz
  have hzero := fun A hQA hA u huA huQ hu => (htrans A hQA hA u huA huQ hu).1
  obtain ⟨v,hv,hvQ,hlocal,hfour,_⟩ := CyclicTwoNormalizedSeed.exists_double_seed
    hcard hH5 (fun g => by
      convert heven g using 1
      congr 2
      exact Subsingleton.elim _ _) hnmod hmaxH Q hQtwo h7' hfree S hS' htop hzero
  obtain ⟨A,_,hfull⟩ := CyclicTwoFullSylowActual.exists_sylow_semiregular
    (fun g => by
      convert heven g using 1
      congr 2
      exact Subsingleton.elim _ _) hnmod hmaxH Q hQtwo h7' hfree S hS' htop v hv hlocal hfour hzero
  obtain ⟨q,hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQtwo])
  have hqG : orderOf q.val = 2 := (Subgroup.orderOf_coe q).trans hq
  have hqv : Commute q.val v.val := NormalizerTwoElementInvolution.central_of_card_two Q hQtwo v q
  exact HighDegreeFullSylowExceptionContradiction.contradiction hcard hH5 hmaxH Q hQtwo A
    q hqG v hv hvQ hqv (fixedBy X v.val \ fixedPoints Q X)
    (fun z hz => ⟨hz.2, Or.inl hz.1⟩)
    (fun g z hzF hzO hgz => hfull g z hzF (fun hvz => hzO ⟨hvz,hzF⟩) hgz)

theorem exists_involution_fixed_ge_nine
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) :
    ∃ t : G, orderOf t = 2 ∧ 9 ≤ (fixedBy X t).ncard := by
  classical
  have hn : ¬ ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7 :=
    contradiction X G hcard h5 hnotAlt hodd
  push Not at hn
  obtain ⟨t, ht, hfix⟩ := hn
  have hp : IsPGroup 2 (Subgroup.zpowers t) := IsPGroup.of_card
    ((Nat.card_zpowers t).trans (ht.trans (pow_one 2).symm))
  have hparity := OddPointStabilizerFixity.odd_fixed_card (Subgroup.zpowers t) hp
    (show Odd (Nat.card X) by simpa only [Nat.card_eq_fintype_card] using hodd)
  rw [OyamaSixFixedBranch.fixedPoints_zpowers_eq_fixedBy, Nat.card_coe_set_eq,
    Nat.odd_iff] at hparity
  exact ⟨t, ht, by omega⟩

end FiveTransitive.HighDegreeOddMaxSevenExclusion

end CFSG
