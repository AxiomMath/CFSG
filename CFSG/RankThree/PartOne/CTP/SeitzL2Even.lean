module

public import CFSG.RankThree.PartOne.CTP.SeitzL2
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.GorensteinWalter CFSG.Open
open BenderSuzuki.MatrixGroups
open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

section Arith

theorem not_two_dvd_sq_sub_one {s : ℕ} (hs : 2 ∣ s) (hs1 : 1 ≤ s) : ¬ 2 ∣ s ^ 2 - 1 := by
  obtain ⟨c, rfl⟩ := hs
  have h1 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
  have hc : 1 ≤ c := by omega
  have h2 : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ hc
  rw [h1]
  generalize c ^ 2 = u at *
  omega

end Arith

theorem isCoatom_of_mulEquiv_psl2_even {F : Type} [Field F]
    [Finite F] {f m r : ℕ} (hF : Nat.card F = 2 ^ f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : f = m * r) (hm2 : 2 ≤ m) {H : Subgroup (PSL2MatrixGroup F)}
    (e : H ≃* PSL2MatrixGroup (GaloisField 2 m)) : IsCoatom H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hm0 : m ≠ 0 := by omega
  have hf0 : f ≠ 0 := by rw [hf]; exact Nat.mul_ne_zero hm0 hr.ne_zero
  set s := 2 ^ m with hs
  have hs4 : 4 ≤ s := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hseven : 2 ∣ s := dvd_pow_self 2 hm0
  have hq : 2 ^ f = s ^ r := by rw [hf, pow_mul]
  have hs2 : 16 ≤ s ^ 2 := by nlinarith
  have hodd : ¬ 2 ∣ s ^ 2 - 1 := not_two_dvd_sq_sub_one hseven (by omega)
  have hcop : Nat.Coprime (s ^ 2 - 1) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have hcardH : Nat.card H = s * (s ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.Walter.psl2_even_card hm0)
  have hcardG : Nat.card (PSL2MatrixGroup F) = s ^ r * ((s ^ r) ^ 2 - 1) := by
    have hfe := CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f (Nat.pos_of_ne_zero hf0) hF
    have e2 := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv hfe (Fin 2)
    rw [Nat.card_congr e2.toEquiv, CFSG.Walter.psl2_even_card hf0, hq]
  have hNge : 60 ≤ s * (s ^ 2 - 1) := calc 60 = 4 * 15 := by norm_num
    _ ≤ s * (s ^ 2 - 1) := Nat.mul_le_mul hs4 (by omega)
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hc
        have : 0 < 2 ^ f := by positivity
        omega
      · exact h0
    rw [hc, show 2 * c - 1 = 2 * (c - 1) + 1 by omega]
    simp
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hcardH, hcardG]
    have hsq : s < s ^ r := calc s = s ^ 1 := (pow_one s).symm
      _ < s ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
    have h1 : s ^ 2 - 1 < (s ^ r) ^ 2 - 1 := by
      have : s ^ 2 < (s ^ r) ^ 2 := Nat.pow_lt_pow_left hsq (by norm_num)
      omega
    exact Nat.mul_lt_mul'' hsq h1
  intro K hHK hK
  have hHKc : Nat.card H < Nat.card K := Subgroup.card_lt_of_lt hHK
  have hHKd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  have htd : s ^ 2 - 1 ∣ Nat.card K := by
    rw [hcardH] at hHKd
    exact (dvd_mul_left (s ^ 2 - 1) s).trans hHKd
  have hsd : s ∣ Nat.card K := by
    rw [hcardH] at hHKd
    exact (dvd_mul_right s (s ^ 2 - 1)).trans hHKd
  rw [hcardH] at hHKc
  obtain ⟨c2, hc2⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
  have hc21 : 1 ≤ c2 := by
    have : 0 < 2 ^ f := by positivity
    omega
  rcases dickson_psl2_subgroup_list hF K with
    ⟨m', -, hmc, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz2, hz, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, ⟨eS4⟩⟩ |
      ⟨h5, ⟨eA5⟩⟩ | ⟨m', t, -, -, -, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, -⟩ |
      ⟨m', hm'f, ⟨eP⟩⟩ | ⟨m', hm'f, ⟨eG⟩⟩
  ·
    rw [hmc] at htd
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m' hcop) htd
    omega
  ·
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    rw [hcard] at hsd
    have h2z : 2 ∣ z := hseven.trans hsd
    rcases hz with hz | hz
    · have := h2z.trans hz
      rw [hc2] at this
      omega
    · have := h2z.trans hz
      rw [hc2] at this
      omega
  ·
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    have hKc : Nat.card K = 2 * z := by
      rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    have hzodd : ¬ 2 ∣ z := by
      intro h2z
      rcases hz with hz | hz
      · have := h2z.trans hz
        rw [hc2] at this
        omega
      · have := h2z.trans hz
        rw [hc2] at this
        omega
    rw [hKc] at hsd
    have hcz : Nat.Coprime s z :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hzodd)
    have hs2' : s ∣ 2 := hcz.dvd_of_dvd_mul_right hsd
    have := Nat.le_of_dvd (by norm_num) hs2'
    omega
  ·
    have h12 : Nat.card K = 12 := by
      rw [Nat.card_congr eA4.toEquiv, card_alternatingFour']
    rw [h12] at hHKc
    omega
  ·
    have h24 : Nat.card K = 24 := by
      rw [Nat.card_congr eS4.toEquiv, card_permFour]
    rw [h24] at hHKc
    omega
  ·
    have h60 : Nat.card K = 60 := by
      rw [Nat.card_congr eA5.toEquiv, card_alternatingFive']
    rw [h60] at hHKc
    omega
  ·
    rw [hgcd, Nat.div_one] at htq
    have hKc : Nat.card K = 2 ^ m' * t := by
      have hcomp : E.IsComplement' C := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
      rw [← hEcard, ← hCcard, hcomp.card_mul_card]
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ t :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ f - 1 := by
      have : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      rw [← this]
      exact h1.trans htq
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    rw [hf] at h3
    have h4 : 2 ∣ r := by
      rw [show 2 * m = m * 2 by ring] at h3
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm
  ·
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp hm'f)
    have hKc : Nat.card K = 2 ^ m' * ((2 ^ m') ^ 2 - 1) :=
      (Nat.card_congr eP.toEquiv).trans (CFSG.Walter.psl2_even_card hm'0)
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ (2 ^ m') ^ 2 - 1 :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ (2 * m') - 1 := by
      have e1 : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 ^ m') ^ 2 = 2 ^ (2 * m') := by rw [← pow_mul, mul_comm]
      rw [← e1, ← e2]
      exact h1
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    have hmd : m ∣ m' := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h3
    obtain ⟨j, rfl⟩ := hmd
    have hjr : j ∣ r := by
      rw [hf] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    rcases (Nat.dvd_prime hr).mp hjr with rfl | rfl
    · rw [hKc, mul_one, ← hs] at hHKc
      exact lt_irrefl _ hHKc
    · apply hK
      apply Subgroup.eq_top_of_card_eq
      rw [hKc, hcardG, ← hf, hq]
  ·
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp (by simpa using hm'f))
    have hKc : Nat.card K = 2 ^ m' * ((2 ^ m') ^ 2 - 1) := by
      rw [Nat.card_congr eG.toEquiv, card_pgl2_galoisField hm'0, ← pow_mul, mul_comm m' 2]
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ (2 ^ m') ^ 2 - 1 :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ (2 * m') - 1 := by
      have e1 : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 ^ m') ^ 2 = 2 ^ (2 * m') := by rw [← pow_mul, mul_comm]
      rw [← e1, ← e2]
      exact h1
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    have hmd : m ∣ m' := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h3
    obtain ⟨j, rfl⟩ := hmd
    have h2j : 2 * j ∣ r := by
      rw [hf, show 2 * (m * j) = m * (2 * j) by ring] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    have h4 : 2 ∣ r := (dvd_mul_right 2 j).trans h2j
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm

section Fixed

variable {F : Type} [Field F] [Finite F]

theorem isCoatom_or_fixed_psl2FieldAut_even {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hchar : ringChar F = 2) {τ : F ≃+* F} (hτ : orderOf τ = p) :
    IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) ∨
      ¬ p ∣ Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ)) := by
  have : Fact (ringChar F).Prime := ⟨finiteField_characteristic_prime F⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := one_le_finiteFieldExponent F
  have hFc : Nat.card F = 2 ^ finiteFieldExponent F := by
    rw [← hchar]
    exact finiteField_card_eq F
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield
    (finiteField_characteristic_prime F) hf (finiteField_card_eq F) τ
  rw [hτ] at hdvd hcard
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hmeq : finiteFieldExponent F / p = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hp.pos
  rw [hmeq, hchar] at hcard
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (hp.odd_of_ne_two (by omega)) hτ
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedSubfield F τ) 2 m hm1 hcard
  let e' := e.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2))
  by_cases hm2 : 2 ≤ m
  · exact Or.inl (isCoatom_of_mulEquiv_psl2_even hFc hp (by omega) (by rw [hm, mul_comm]) hm2 e')
  · right
    have hm1' : m = 1 := by omega
    have h6 : Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ)) = 6 := by
      rw [Nat.card_congr e'.toEquiv, CFSG.Walter.psl2_even_card hm1.ne', hm1']
      norm_num
    rw [h6]
    intro h
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · exact absurd h (by norm_num)
    · exact absurd hp (by norm_num)

theorem fieldAutData_psl2_even {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hchar : ringChar F = 2) : FieldAutData (PSL2 F) p :=
  fieldAutData_psl2 hp hp5 fun _ hτ => isCoatom_or_fixed_psl2FieldAut_even hp hp5 hchar hτ

end Fixed

theorem extSeitzAtOuter_A1_even {q : TauCeti.PrimePower}
    (h2 : q.p = 2) : ExtSeitzAtOuter (.A 1 q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have e : K ≃* PSL2 (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hchar : ringChar (GaloisField q.p q.exponent) = 2 := by
    rw [ringChar.eq (GaloisField q.p q.exponent) q.p]
    exact h2
  have hd : FieldAutData K p :=
    (fieldAutData_psl2_even hp hp5 hchar).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end CFSG.RankThree.PartOne.CTP
