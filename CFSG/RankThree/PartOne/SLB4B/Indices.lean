module

public import CFSG.RankThree.PartOne.SLB4B.RankFourL
public import CFSG.RankThree.PartOne.SLB4B.RankFourSpThree
public import CFSG.RankThree.PartOne.SLB4B.RankFourUThree
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.SLB4B

open TauCeti CFSG.RankThree.PartOne.SRC

theorem p_ne_two_of_card_odd (q : PrimePower) (h : q.card % 2 = 1) : q.p ≠ 2 := by
  intro h2
  have : 2 ∣ q.card := by
    rw [PrimePower.card_def, h2]
    exact dvd_pow_self 2 q.exponent_pos.ne'
  omega

theorem three_le_card (q : PrimePower) (hq2 : q.p ≠ 2) : 3 ≤ q.card := by
  have h2 := q.prime_p.two_le
  rw [PrimePower.card_def]
  exact (show 3 ≤ q.p by omega).trans (Nat.le_self_pow q.exponent_pos.ne' q.p)

theorem card_eq_three_or_five_le (q : PrimePower) (hq2 : q.p ≠ 2) : q.card = 3 ∨ 5 ≤ q.card := by
  have h3 := three_le_card q hq2
  have hodd : q.card % 2 = 1 := by
    rw [PrimePower.card_def]
    exact Nat.odd_iff.mp (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
  omega

theorem prime_pow_eq_three {p e : ℕ} (hp : p.Prime) (he : 0 < e) (h : p ^ e = 3) :
    p = 3 ∧ e = 1 := by
  have hdvd : p ∣ 3 := h ▸ dvd_pow_self p he.ne'
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h)⟩

theorem rankFourCover_typeA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hr : 4 ≤ r) (hq2 : q.p ≠ 2) :
    RankFourCover q.p (ValidLieTypeIndex.Group ⟨.A r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact rankFourCover_of_mulEquiv (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
    (rankFourCover_psl (F := GaloisField q.p q.exponent) (p := q.p) (e := q.exponent)
      (GaloisField.card _ _ q.exponent_pos.ne') hq2 (by omega))

section Unitary


theorem rankFourCover_typeTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hr : 4 ≤ r) (hq2 : q.p ≠ 2) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ RankFourCover p (ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) := by
  have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p := by
    simp [ValidLieTypeIndex.characteristic]
  have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent := by
    simp [ValidLieTypeIndex.fieldExponent]
  have hpr : (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩).Prime := by
    rw [hℓ]; exact q.prime_p
  have : Fact (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩).Prime := ⟨hpr⟩
  have hp2 : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ≠ 2 := by rw [hℓ]; exact hq2
  have he1 : 1 ≤ ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ := by
    rw [hfe]; exact q.exponent_pos
  refine ⟨ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩, hpr, hp2,
    rankFourCover_of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv) ?_⟩
  rcases card_eq_three_or_five_le q hq2 with h3 | h5
  · have h3' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact h3
    obtain ⟨hp3, he3⟩ := prime_pow_eq_three q.prime_p q.exponent_pos h3'
    exact rankFourCover_psu_three (by rw [hℓ]; exact hp3) (by rw [hfe]; exact he3)
      (n := r + 1) (by omega)
  · have hq : 4 ≤ ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
        ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ := by
      rw [hℓ, hfe, ← PrimePower.card_def]; omega
    exact rankFourCover_psu hp2 he1 hq (n := r + 1) (by omega)

end Unitary

theorem rankFourCover_typeC (q : PrimePower) (hv : (LieTypeIndex.C 3 q).Valid) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ RankFourCover p (ValidLieTypeIndex.Group ⟨.C 3 q, hv⟩) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hc : ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_C 3 q
  have hpr : (ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩).Prime := by
    rw [hc]; exact q.prime_p
  have : Fact (ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩).Prime := ⟨hpr⟩
  have hp2 : ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩ ≠ 2 := by rw [hc]; exact hrange.2
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C 3 q, hv⟩
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hv⟩) =
      ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩ ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, hc]
    simp [ValidLieTypeIndex.fieldOrder]
  refine ⟨ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩, hpr, hp2,
    rankFourCover_of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj 3 q hv) ?_⟩
  rcases card_eq_three_or_five_le q hrange.2 with h3 | h5
  · have h3' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact h3
    obtain ⟨hp3, he3⟩ := prime_pow_eq_three q.prime_p q.exponent_pos h3'
    exact rankFourCover_psp6_three
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hv⟩))
      (p := ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩) (e := q.exponent)
      (by rw [hc]; exact hp3) he3 hK
  · have h5' : 5 ≤ ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩ ^ q.exponent := by
      rw [hc, ← PrimePower.card_def]; exact h5
    exact rankFourCover_psp6_of_five_le
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hv⟩))
      (p := ValidLieTypeIndex.characteristic ⟨.C 3 q, hv⟩) (e := q.exponent) hK hp2 h5'

end CFSG.RankThree.PartOne.SLB4B
