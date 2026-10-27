module

public import CFSG.Permutation.FiveTransitive.ThreePrimeFourPGroup
public import CFSG.Permutation.FiveTransitive.ThreePrimeFourCycleObstruction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.FixedActionGoursat

public section

namespace CFSG

namespace FiveTransitive.ThreePrimeFourFiveFixer

open MulAction SylowFixedActionCore FixedNormalizerAction

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    (hp : p.Prime) (hp17 : 17 ≤ p)
    (P : Subgroup (Equiv.Perm X)) (hn : Fintype.card X = 3 * p + 4)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hclass : ∀ (F : Type) [Fintype F] [DecidableEq F]
      (J : Subgroup (Equiv.Perm F)),
      5 ≤ Fintype.card F → Fintype.card F < Fintype.card X →
      IsMultiplyPretransitive J F 5 →
      Nat.card J = (Fintype.card F).factorial ∨
      (7 ≤ Fintype.card F ∧ Nat.card J = (Fintype.card F).factorial / 2) ∨
      (Fintype.card F = 12 ∧ Nat.card J = 95040) ∨
      (Fintype.card F = 24 ∧ Nat.card J = 244823040))
    (s : Set X) (hs : s.ncard = 5) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  intro hd
  let S : Sylow p (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : p ∣ Nat.card S := by
    simpa only [pow_one] using S.pow_dvd_card_of_pow_dvd_card (n := 1) (by simpa only [pow_one] using hd)
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hQcardS : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQne : Q ≠ ⊥ := by
    intro he
    rw [← hQcardS, he, Subgroup.card_bot] at hdiv
    exact hp.not_dvd_one hdiv
  have hQ : IsPGroup p Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hbase := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hbase
  change 5 ≤ Nat.card F at hbase
  have hfixQ : 5 ≤ Nat.card (fixedPoints Q X) := by rw [← hfixed]; exact hbase
  have hF : Nat.card F = p + 4 := by
    rw [hfixed]
    exact ThreePrimeFourPGroup.fixed_card hp17 P hn h5 hnotAlt Q hQ hQne hfixQ
  have hQcard : Nat.card Q = p :=
    ThreePrimeFourPGroup.card_eq_prime hp17 P hn h5 hnotAlt Q hQ hQne hfixQ
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := Image (X := X) Q
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
    refine ⟨⟨toPermHom (sylowNormalizer X P s S) F g,⟨g,rfl⟩⟩,?_⟩
    apply Function.Embedding.ext
    exact hg
  have hFF : Fintype.card F = p + 4 := by rwa [← Nat.card_eq_fintype_card]
  have hAlt : alternatingGroup F ≤ J := by
    apply FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
      F J (by rw [hFF]; omega)
    rcases hclass F J (by rw [hFF]; omega) (by rw [hFF,hn]; omega) hJ5 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h.2
    · rw [hFF] at h; omega
    · have hpeq : p = 20 := by rw [hFF] at h; omega
      rw [hpeq] at hp
      norm_num at hp
  let _ : IsCyclic Q := isCyclic_of_prime_card hQcard
  obtain ⟨r,hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  let u : P := r.val
  have hu : orderOf u = p := (Subgroup.orderOf_coe r).trans (hr.trans hQcard)
  have heq : Subgroup.zpowers u = Q := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr r.property) (by rw [Nat.card_zpowers,hu,hQcard])
  have hufix : Nat.card (Function.fixedPoints u.val) = p + 4 := by
    rw [← show fixedPoints (Subgroup.zpowers u) X = Function.fixedPoints u.val from
      CentralizingSingletonFixed.fixed_zpowers u,heq,← hfixed]
    exact hF
  let _ : Fintype (Fixed (X := X) (Subgroup.zpowers u)) := Fintype.ofFinite _
  apply hnotAlt (ThreePrimeFourCycleObstruction.alternatingGroup_le hp hp17 P hn h5 u hu hufix ?_)
  have htransport (R : Subgroup P) (hR : R = Q) :
      let _ : Fintype (Fixed (X := X) R) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) R) ≤ Image (X := X) R := by
    subst R
    exact hAlt
  exact htransport (Subgroup.zpowers u) heq

end FiveTransitive.ThreePrimeFourFiveFixer

end CFSG
