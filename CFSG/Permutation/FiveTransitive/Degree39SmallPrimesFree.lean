module

public import CFSG.Permutation.FiveTransitive.Degree39PrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree39SylowPrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree39FiveCentralizerBound
public import CFSG.Permutation.FiveTransitive.Degree39CyclicPrimeExclusion
public import CFSG.Permutation.FiveTransitive.FiveSevenSmallAut
public import CFSG.Permutation.FiveTransitive.Degree39ElevenAut
public import CFSG.Permutation.FiveTransitive.Degree39ElevenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree39SmallPrimesFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  let H := fixingSubgroup P s
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) p hd
  have hZ : IsPGroup p (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let instF : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup p Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hSge : p ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hSge; have := hp.two_le; omega
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  obtain ⟨height,hupper,hAlt⟩ := Degree39SylowPrimeFixed.bounds_and_alternating
    p hp hcases P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 19 at hupper
  change alternatingGroup F ≤ rho.range at hAlt
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree39PrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (20 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    apply hS
    rw [← hQcard,he,he0,pow_zero]
  have hQprime : Nat.card Q = p := by
    by_cases hp7 : p = 7
    · rw [hp7] at hQ he hmod ⊢
      let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hFcases : Nat.card F = 11 ∨ Nat.card F = 18 := by omega
      have he2 : e ≤ 2 := by
        by_contra hn
        have h343 : 343 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 7 (by omega : 3 ≤ e)
        have hc := h343.trans htuple
        rcases hFcases with h | h <;> rw [h] at hc <;> norm_num at hc
      have hQ49 : Nat.card Q ≤ 7 ^ 2 := by
        rw [he]
        exact Nat.pow_le_pow_right (by norm_num : 0 < 7) he2
      have hfiveImage : 5 ∣ Nat.card rho.range :=
        (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 5) (by norm_num)
          (by rw [← Nat.card_eq_fintype_card]; omega)).trans
          (Subgroup.card_dvd_of_le hAlt)
      have hfiveN : 5 ∣ Nat.card N := hfiveImage.trans (Subgroup.card_range_dvd rho)
      let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 hfiveN
      have hz5 : z ^ 5 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have hauto : Q.normalizerMonoidHom z = 1 :=
        FiveSevenSmallAut.eq_one (Or.inr ⟨rfl,rfl⟩) Q hQ hQ49 _
          (by rw [← map_pow,hz5,map_one])
      have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
        intro q
        have hh : z.val * q.val * z.val⁻¹ = q.val := congrArg Subtype.val (DFunLike.congr_fun hauto q)
        simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * z.val) hh
      have hQ7 := Degree39FiveCentralizerBound.card_le_seven P hcard h5 hnotAlt Q hQ z.val
        ((Subgroup.orderOf_coe z).trans hz) hcomm
      have he1 : e ≤ 1 := by
        by_contra hn
        have hh := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 2 ≤ e)
        rw [← he] at hh
        change 49 ≤ Nat.card Q at hh
        omega
      have heq : e = 1 := by omega
      simpa only [heq,pow_one] using he
    · by_cases hp11 : p = 11
      · rw [hp11] at hQ he hmod ⊢
        let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
        have hFcases : Nat.card F = 6 ∨ Nat.card F = 17 := by omega
        have he2 : e ≤ 2 := by
          by_contra hn
          have h1331 : 1331 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 11 (by omega : 3 ≤ e)
          have hc := h1331.trans htuple
          rcases hFcases with h | h <;> rw [h] at hc <;> norm_num at hc
        have hQ121 : Nat.card Q ≤ 121 := by
          rw [he]
          exact Nat.pow_le_pow_right (by norm_num : 0 < 11) he2
        have haut := Degree39ElevenAut.nine_not_dvd Q hQ hQ121
        have hfive := Degree39ElevenCentralizer.five_dvd_centralizer Q hFcases hAlt haut
        let C := Subgroup.centralizer (Q : Set P)
        let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 hfive
        have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
          intro q
          exact ((Subgroup.mem_centralizer_iff.mp z.property) q.val q.property).symm
        have hone := Degree39FiveCentralizerBound.eleven_eq_one P hcard h5 hnotAlt Q hQ z.val
          ((Subgroup.orderOf_coe z).trans hz) hcomm
        exfalso
        apply hS
        rw [← hQcard]
        exact hone
      · have hsmall : p = 13 ∨ p = 17 := by tauto
        have he1 : e ≤ 1 := by
          by_contra hn
          have hp2 : p ^ 2 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow p (by omega : 2 ≤ e)
          have hc := hp2.trans htuple
          rcases hsmall with rfl | rfl
          · have hF : Nat.card F = 13 := by omega
            rw [hF] at hc
            norm_num at hc
          · have hF : Nat.card F = 5 := by omega
            rw [hF] at hc
            norm_num at hc
        have heq : e = 1 := by omega
        simpa only [heq,pow_one] using he
  let r : P := u
  have hr : orderOf r = p := (Subgroup.orderOf_coe u).trans hu
  have hRQ : zpowers r = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hr,hQprime]
  let instR : Fintype (PrimeCyclicFixedAction.cyclicFixedPoints X P r) := Fintype.ofFinite _
  have htransport (A : Subgroup P) [iA : Fintype (FixedNormalizerAction.Fixed (X := X) A)] (hA : A = Q) :
      5 ≤ Nat.card (FixedNormalizerAction.Fixed (X := X) A) ∧
      alternatingGroup (FixedNormalizerAction.Fixed (X := X) A) ≤ FixedNormalizerAction.Image (X := X) A := by
    subst A
    cases Subsingleton.elim iA instF
    exact ⟨height,hAlt⟩
  obtain ⟨hF,hJ⟩ := @htransport (zpowers r) instR hRQ
  exact @Degree39CyclicPrimeExclusion.excluded X _ _ p hp
    (by rcases hcases with rfl | rfl | rfl | rfl <;> norm_num) P hcard h5 hnotAlt r instR hr hF hJ

end FiveTransitive.Degree39SmallPrimesFree

end CFSG
