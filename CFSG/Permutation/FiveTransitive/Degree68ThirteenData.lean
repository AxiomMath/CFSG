module

public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage
public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree68ThirteenData

open MulAction Subgroup FixedNormalizerAction

private theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hn : Fintype.card X = 68)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 13 ∣ Nat.card (fixingSubgroup P s))
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (hne : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) = 3 := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hpd : 13 ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left (by
    intro he; exact hne (Subgroup.card_eq_one.mp he))
  have hlt : Nat.card (fixedPoints Q X) < 5 := by
    by_contra hh
    have hlarge : 5 ≤ (fixedPoints Q X).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
    let i : Q →* fixingSubgroup P s := Q.subtype.codRestrict (fixingSubgroup P s)
      (fun q => (mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx q))
    have hi : Function.Injective i := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : fixingSubgroup P s => z.val) hab)
    exact hfree s hs (hpd.trans (Subgroup.card_dvd_of_injective i hi))
  have hm := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % 13 = Nat.card (fixedPoints Q X) % 13 at hm
  rw [Nat.card_eq_fintype_card (α := X),hn] at hm
  have he : (68 : ℕ) % 13 = 3 := by norm_num
  rw [he,Nat.mod_eq_of_lt (by omega : Nat.card (fixedPoints Q X) < 13)] at hm
  exact hm.symm

private theorem card_eq_thirteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hn : Fintype.card X = 68)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 13 ∣ Nat.card (fixingSubgroup P s))
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (hne : Q ≠ ⊥) : Nat.card Q = 13 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hf := fixed_card P hn hfree Q hQ hne
  have hfreeQ : ∀ q : Q, ∀ x : X, x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    by_contra hq
    let R : Subgroup P := (zpowers q).map Q.subtype
    have hR : IsPGroup 13 R := (hQ.to_subgroup (zpowers q)).map Q.subtype
    have hqR : q.val ∈ R := ⟨q,mem_zpowers q,rfl⟩
    have hRne : R ≠ ⊥ := by
      intro he
      have hh := hqR
      rw [he,mem_bot] at hh
      exact hq (Subtype.ext hh)
    have hrfix := fixed_card P hn hfree R hR hRne
    have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
      intro y hy r
      obtain ⟨a,ha,hea⟩ := r.property
      change r.val • y = y
      rw [← hea]
      rcases hy with rfl | hy
      · exact (zpowers_le.mpr (show q ∈ stabilizer Q y from hqx)) ha
      · exact hy a
    have hlo := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hx,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hf,hrfix] at hlo
    omega
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (fun q x hx => (hx q).symm ▸ hx) hfreeQ
  rw [← Nat.card_coe_set_eq,hf,Nat.card_eq_fintype_card (α := X),hn] at hd
  norm_num at hd
  have hle : Nat.card Q ≤ 65 := Nat.le_of_dvd (by omega) hd
  obtain ⟨k,hk⟩ := IsPGroup.iff_card.mp hQ
  have hk1 : k ≤ 1 := by
    by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 13) (by omega : 2 ≤ k)
    rw [← hk] at hpow
    norm_num at hpow
    omega
  have hk0 : k ≠ 0 := by
    intro he
    rw [he,pow_zero] at hk
    exact hne (Subgroup.card_eq_one.mp hk)
  simpa only [show k = 1 by omega,pow_one] using hk

private theorem exists_generator_of_prime_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hn : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 13 ∣ Nat.card (fixingSubgroup P s)) :
    ∃ u : P, orderOf u = 13 ∧
      Nat.card (Fixed (X := X) (zpowers u)) = 3 ∧ Image (X := X) (zpowers u) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive P X 5 (by omega) h5
  rw [hn] at hd
  have h13 : 13 ∣ Nat.card P := (by norm_num [Nat.descFactorial] : 13 ∣ (68 : ℕ).descFactorial 5).trans hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := P) 13 h13
  have hR : IsPGroup 13 (zpowers u) := IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers,hu,pow_one])
  obtain ⟨S,hRS⟩ := hR.exists_le_sylow
  have hSne : (S : Subgroup P) ≠ ⊥ := by
    intro he
    have hh := hRS (mem_zpowers u)
    rw [he,mem_bot] at hh
    rw [hh,orderOf_one] at hu
    norm_num at hu
  have hScard := card_eq_thirteen P hn hfree (S : Subgroup P) S.isPGroup' hSne
  have hSfix := fixed_card P hn hfree (S : Subgroup P) S.isPGroup' hSne
  have heq : zpowers u = (S : Subgroup P) := Subgroup.eq_of_le_of_card_ge hRS
    (by rw [Nat.card_zpowers,hu,hScard])
  refine ⟨u,hu,?_,?_⟩
  · rw [heq,fixed_eq]
    exact hSfix
  · rw [heq]
    exact AmbientSylowSmallFixedImage.sylow_fixed_image 13 3 (by norm_num) (by omega)
      P (by omega) h5 S hSfix

theorem exists_generator
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ u : P, orderOf u = 13 ∧
      Nat.card (Fixed (X := X) (zpowers u)) = 3 ∧ Image (X := X) (zpowers u) = ⊤ := by
  exact exists_generator_of_prime_free P hcard h5 (fun s hs =>
    Degree68LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 13 (by norm_num) (by omega))

end FiveTransitive.Degree68ThirteenData

end CFSG
