module

public import CFSG.Permutation.FiveTransitive.StabilizerSylowConjugacy
public import CFSG.Permutation.FiveTransitive.SylowNormalizerExtension

public section

namespace CFSG

namespace FiveTransitive.OyamaSylowAssembly

open MulAction

theorem exists_conjugate_sylow_containing_local
    {G Y : Type*} [Group G] [Finite G] [MulAction G Y]
    {p : ℕ} [Fact p.Prime] (a b : Y) (hab : ∃g:G,g • a=b)
    (P : Sylow p (stabilizer G a)) (Q : Subgroup G)
    (hQP : Q < (P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype)
    (hQb : Q≤stabilizer G b)
    (R : Sylow p ↥(Subgroup.normalizer (Q : Set G) ⊓ stabilizer G b)) :
    ∃ (S : Sylow p (stabilizer G b)) (g:G), g • a=b ∧
      ((P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype).map
        (MulAut.conj g).toMonoidHom =
        (S : Subgroup (stabilizer G b)).map (stabilizer G b).subtype ∧
      Q < (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype ∧
      (R : Subgroup ↥(Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b)).map
        (Subgroup.normalizer (Q:Set G) ⊓ stabilizer G b).subtype =
      (S : Subgroup (stabilizer G b)).map (stabilizer G b).subtype ⊓
        Subgroup.normalizer (Q:Set G) := by
  have hPA : IsPGroup p ((P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype) :=
    P.isPGroup'.map (stabilizer G a).subtype
  have hQ : IsPGroup p Q := hPA.of_injective (Subgroup.inclusion hQP.le)
    (Subgroup.inclusion_injective hQP.le)
  have hstab : Nat.card (stabilizer G a)=Nat.card (stabilizer G b) := by
    obtain ⟨g,hg⟩ := hab
    exact Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv
  have hcard : Nat.card Q < p^(Nat.card (stabilizer G b)).factorization p := by
    have hlt : Nat.card Q < Nat.card ((P : Subgroup (stabilizer G a)).map (stabilizer G a).subtype) := by
      by_contra hn
      exact hQP.ne (Subgroup.eq_of_le_of_card_ge hQP.le (by omega))
    have he := Nat.card_congr ((P : Subgroup (stabilizer G a)).equivMapOfInjective
      (stabilizer G a).subtype Subtype.val_injective).toEquiv
    rw [←he,P.card_eq_multiplicity,hstab] at hlt
    exact hlt
  obtain ⟨S,hQR,hR⟩ := SylowNormalizerExtension.exists_sylow_extension
    (stabilizer G b) Q hQb hQ hcard R
  obtain ⟨g,hg,hconj⟩ := StabilizerSylowConjugacy.exists_conjugating_transporter a b hab P S
  exact ⟨S,g,hg,hconj,hQR,hR⟩

end FiveTransitive.OyamaSylowAssembly

end CFSG
