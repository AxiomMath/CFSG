module

public import CFSG.Permutation.FiveTransitive.Degree54FiveFixedCases
public import CFSG.Permutation.FiveTransitive.Degree54FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree54FiveElevenCentralizer
public import CFSG.Permutation.FiveTransitive.FiveGroup625ElevenAutomorphism
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveSylowData

open MulAction Subgroup SylowFixedActionCore

private theorem fixed_ne_twenty_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) ≠ 24 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro hF
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 24 := by rwa [← hfixeq]
  have hbound := Degree54FiveGroupBound.card_le_five_of_fixed_twenty_four
    P hcard h5 hnotAlt Q hQ hfixed.ge
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hNexp := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hN5 : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hNexp a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  have hsize : 5 ≤ Nat.card F := by change 5 ≤ Nat.card (sylowFixedPoints X P s S); omega
  let b : Fin 5 ↪ F := (Fin.castLEEmb hsize).trans (Finite.equivFin F).symm.toEmbedding
  let t : Set F := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive N F t.ncard := by rw [ht]; exact hN5
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hd : 11 ∣ (fixingSubgroup N t).index := by
    rw [hi,ht]
    change 11 ∣ (Nat.card (sylowFixedPoints X P s S)).choose 5 * Nat.factorial 5
    rw [hF]
    norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 11
    (hd.trans (fixingSubgroup N t).index_dvd_card)
  have haut : Q.normalizerMonoidHom g = 1 :=
    FiveGroup625ElevenAutomorphism.eq_one hQ (by omega) _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hone := Degree54FiveElevenCentralizer.card_eq_one_of_eleven P hcard h5 hnotAlt Q hQ
    g.val ((Subgroup.orderOf_coe g).trans hg) hcomm
  have heq : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  exact hS (heq.symm.trans hone)

theorem five_fixed_card_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    Nat.card (sylowFixedPoints X P s S) = 9 ∧
      alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 9 :=
    (Degree54FiveFixedCases.five_fixed_card_cases P hcard h5 hnotAlt s hs S hS).resolve_right
      (fixed_ne_twenty_four P hcard h5 hnotAlt s hs S hS)
  refine ⟨hF,?_⟩
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := (toPermHom N F).range
  change alternatingGroup F ≤ J
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5 a b ha hb
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩

end FiveTransitive.Degree54FiveSylowData

end CFSG
