module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree58SylowPrimeFixed

open MulAction SylowFixedActionCore

theorem five_dvd_card
    {G Y : Type*} [Group G] [Finite G] [Finite Y] [MulAction G Y]
    (h5 : IsMultiplyPretransitive G Y 5) (hsize : 5 ≤ Nat.card Y) : 5 ∣ Nat.card G := by
  classical
  let b : Fin 5 ↪ Y := (Fin.castLEEmb hsize).trans (Finite.equivFin Y).symm.toEmbedding
  let t : Set Y := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive G Y t.ncard := by rw [ht]; exact h5
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hd : 5 ∣ (fixingSubgroup G t).index := by
    rw [hi,ht]
    exact dvd_mul_of_dvd_right (by norm_num [Nat.factorial]) _
  exact hd.trans (fixingSubgroup G t).index_dvd_card

theorem bounds_and_transitive
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    5 ≤ Nat.card (sylowFixedPoints X P s S) ∧
      Nat.card (sylowFixedPoints X P s S) ≤ 29 ∧
      IsMultiplyPretransitive (sylowNormalizer X P s S) (sylowFixedPoints X P s S) 5 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hQne : Q ≠ ⊥ := by intro he; apply hS; rw [← hQcard,he]; simp
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hQne
  rw [← FixedNormalizerAction.fixed_eq Q,hcard] at hupper
  have hlower := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlower
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  refine ⟨hlower,hupper,?_⟩
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
  refine ⟨g,?_⟩
  apply Function.Embedding.ext
  intro i
  exact hg i

theorem eleven_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) [Fintype (sylowFixedPoints X P s S)]
    (hS : Nat.card S ≠ 1) :
    alternatingGroup (sylowFixedPoints X P s S) ≤
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  obtain ⟨hlo,hhi,hN5⟩ := bounds_and_transitive 11 (by decide) P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at hlo
  change Nat.card F ≤ 29 at hhi
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 11 = Nat.card F % 11 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hF : Nat.card F = 14 ∨ Nat.card F = 25 := by omega
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu
    F (toPermHom N F).range
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,fun i => DFunLike.congr_fun hg i⟩

end FiveTransitive.Degree58SylowPrimeFixed

end CFSG
