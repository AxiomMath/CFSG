module

public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleSubgroup
public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.TwoPrimeCycleEntrance

open MulAction Subgroup FixedNormalizerAction

private theorem sylow_fixed_image
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5)
    (S : Sylow p P) (hfixed : Nat.card (fixedPoints S X) = f) :
    Image (X := X) (S : Subgroup P) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let s : Set X := fixedPoints S X
  have hs : s.ncard = f := by rw [← Nat.card_coe_set_eq]; exact hfixed
  have hle : (S : Subgroup P) ≤ fixingSubgroup P s := by
    intro q hq
    apply (mem_fixingSubgroup_iff P).mpr
    intro x hx
    exact hx (⟨q,hq⟩ : S)
  let T : Sylow p (fixingSubgroup P s) := S.subtype hle
  have himage : GenericSylowFixedAction.sylowImage P X s T = (S : Subgroup P) := by
    ext q
    change q ∈ ((S : Subgroup P).subgroupOf (fixingSubgroup P s)).map
      (fixingSubgroup P s).subtype ↔ q ∈ S
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hq
      exact ⟨⟨q,hle hq⟩,hq,rfl⟩
  have hftrans : IsMultiplyPretransitive P X f := by
    let _ := h5
    exact isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5)
      (by omega) (by rw [Nat.card_eq_fintype_card,hcard]; omega)
  have hexp : ∀ a b : Fin f → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := hftrans.exists_smul_eq (⟨a,ha⟩ : Fin f ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hlocal := GenericSylowFixedAction.sylowNormalizer_transitive_on_fixedPoints
    P X f hexp s hs T
  change ∀ a b : Fin f → Fixed (X := X) (GenericSylowFixedAction.sylowImage P X s T),
    Function.Injective a → Function.Injective b →
    ∃ g : Normalizer (GenericSylowFixedAction.sylowImage P X s T), ∀ i, g • a i = b i at hlocal
  rw [himage] at hlocal
  let F := Fixed (X := X) (S : Subgroup P)
  let J := Image (X := X) (S : Subgroup P)
  have hF : Nat.card F = f := by
    change Nat.card (Fixed (X := X) (S : Subgroup P)) = f
    rw [fixed_eq]
    exact hfixed
  have hJf : IsMultiplyPretransitive J F f := by
    rw [isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g,hg⟩ := hlocal a b a.injective b.injective
    refine ⟨⟨toPermHom (Normalizer (S : Subgroup P)) F g,⟨g,rfl⟩⟩,?_⟩
    apply Function.Embedding.ext
    intro i
    exact hg i
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive J F (Nat.card F - 1)
  rw [hF]
  let _ := hJf
  exact isMultiplyPretransitive_of_le (G := J) (α := F) (n := f) (by omega) (by rw [hF])

theorem exists_generator
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ r : P, orderOf r = p ∧ r.val.cycleType = {p,p} ∧
      Nat.card (Fixed (X := X) (zpowers r)) = f ∧ Image (X := X) (zpowers r) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive P X 5 (by omega) h5
  rw [hcard] at hd
  have hpdesc : p ∣ (2 * p + f).descFactorial 5 := by
    rw [Nat.descFactorial_eq_prod_range]
    have hfactor := Finset.dvd_prod_of_mem (fun i => 2 * p + f - i)
      (show f ∈ Finset.range 5 by apply Finset.mem_range.mpr; omega)
    rw [Nat.add_sub_cancel] at hfactor
    exact (dvd_mul_left p 2).trans hfactor
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G := P) p (hpdesc.trans hd)
  have hR : IsPGroup p (zpowers r) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hr,pow_one]
  obtain ⟨S,hRS⟩ := hR.exists_le_sylow
  have hSne : (S : Subgroup P) ≠ ⊥ := by
    intro he
    have hrS := hRS (mem_zpowers r)
    rw [he,mem_bot] at hrS
    rw [hrS,orderOf_one] at hr
    have hpne : p ≠ 1 := hp.ne_one
    exact hpne hr.symm
  have hScard := TwoPrimeCycleSubgroup.card_eq_prime p f hp hp13 hf P hcard h5 hnotAlt
    (S : Subgroup P) S.isPGroup' hSne
  have hSfixed := TwoPrimeCycleSubgroup.fixed_card p f hp hp13 hf P hcard h5 hnotAlt
    (S : Subgroup P) S.isPGroup' hSne
  have heq : zpowers r = (S : Subgroup P) := Subgroup.eq_of_le_of_card_ge hRS (by
    rw [Nat.card_zpowers,hr,hScard])
  refine ⟨r,hr,TwoPrimeCycleSubgroup.order_prime_cycle_type p f hp hp13 hf P hcard h5 hnotAlt r hr,?_,?_⟩
  · rw [heq,fixed_eq]
    exact hSfixed
  · rw [heq]
    exact sylow_fixed_image p f hp hp13 hf P hcard h5 S hSfixed

end FiveTransitive.TwoPrimeCycleEntrance

end CFSG
