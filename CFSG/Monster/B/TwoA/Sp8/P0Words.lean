
module

public import CFSG.Monster.B.TwoA.Sp8.P0WordsBase
import all CFSG.Monster.B.TwoA.Sp8.P0WordsBase

public import CFSG.Monster.B.TwoA.Sp8.LagrangianRadical
public import Certificates.Certificate812461

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section

end

private theorem conjHom_uGen_bvec (k : ℕ) (hk : k < 10) (x : ℕ) :
    conjHom ⟨wordD (uGenWords.getD k []), wordD_mem_NA8 _⟩ (bvec 8 x) =
      bvec 8 (actWord (uGenWords.getD k []) x) :=
  conjHom_wordD (uGenWords.getD k []) (uGenWords_lt k hk) x

private theorem conjHom_uGen_fixed_on_lam0 (k : ℕ) (hk : k < 10) {v : V8}
    (hv : v ∈ lam0) :
    conjHom ⟨wordD (uGenWords.getD k []), wordD_mem_NA8 _⟩ v = v := by
  refine Submodule.span_induction (p := fun v _ =>
    conjHom ⟨wordD (uGenWords.getD k []), wordD_mem_NA8 _⟩ v = v) ?_ ?_ ?_ ?_ hv
  · intro x hx
    have hx' : x = bvec 8 1 ∨ x = bvec 8 2 ∨ x = bvec 8 12 ∨ x = bvec 8 48 := by
      simpa using hx
    obtain h1 | h2 | h3 | h4 := hx'
    · rw [h1, conjHom_uGen_bvec k hk 1, (uGenWords_fixed k hk).1]
    · rw [h2, conjHom_uGen_bvec k hk 2, (uGenWords_fixed k hk).2.1]
    · rw [h3, conjHom_uGen_bvec k hk 12, (uGenWords_fixed k hk).2.2.1]
    · rw [h4, conjHom_uGen_bvec k hk 48, (uGenWords_fixed k hk).2.2.2]
  · simp
  · intro x y hx hy ihx ihy
    simp only [map_add, ihx, ihy]
  · intro c x hx ih
    simp only [map_smul, ih]

theorem uD_mem_PLam {k : ℕ} (hk : k < 10) : uD k ∈ PLam lam0 := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [uD_eq_wordD k]
    exact wordD_mem_Xgrp _
  · rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hfix := conjHom_uGen_fixed_on_lam0 k hk hv
    have e := aEquiv_conjHom ⟨wordD (uGenWords.getD k []), wordD_mem_NA8 _⟩ v
    rw [hfix] at e
    rw [uD_eq_wordD k]
    calc aEquiv (Multiplicative.ofAdd v) * wordD (uGenWords.getD k [])
        = (wordD (uGenWords.getD k []) * aEquiv (Multiplicative.ofAdd v) *
            (wordD (uGenWords.getD k []))⁻¹) * wordD (uGenWords.getD k []) := by rw [← e]
      _ = wordD (uGenWords.getD k []) * aEquiv (Multiplicative.ofAdd v) := by group

theorem lD_mul_lD {i j : ℕ} (hi : i < 16)
    (hj : j < 16) :
    lD (2 ^ i) * lD (2 ^ j) =
      lD (2 ^ j) * lD (2 ^ i) * tD ((lCommN.getD i []).getD j 0) := by
  have e := Certificates.certificate812461.1 i hi j hj
  simp only [wordX_append, wordX_lWord, wordX_tWord] at e
  simpa only [mul_assoc] using e

theorem lD_mul_self {i : ℕ} (hi : i < 16) :
    lD (2 ^ i) * lD (2 ^ i) = 1 := by
  have e := Certificates.certificate812461.2.1 i hi
  simpa only [wordX_append, wordX_lWord, wordX_nil] using e

theorem uD_mul_lD {k j : ℕ} (hk : k < 10) (hj : j < 16) :
    uD k * lD (2 ^ j) = lD ((uConjLN.getD k []).getD j (0, 0)).1 *
      tD ((uConjLN.getD k []).getD j (0, 0)).2 * uD k := by
  have e := Certificates.certificate812461.2.2.1 k hk j hj
  simp only [wordX_append, wordX_lWord, wordX_tWord, wordX_uWord] at e
  simpa only [mul_assoc] using e

theorem uD_mul_tD {k j : ℕ} (hk : k < 10) (hj : j < 9) :
    uD k * tD (2 ^ j) = tD ((uConjTN.getD k []).getD j 0) * uD k := by
  have e := Certificates.certificate812461.2.2.2.1 k hk j hj
  simp only [wordX_append, wordX_tWord, wordX_uWord] at e
  simpa only [mul_assoc] using e

theorem uD_mul_self {k : ℕ} (hk : k < 10) :
    uD k * uD k = lD (uSqN.getD k (0, 0)).1 * tD (uSqN.getD k (0, 0)).2 := by
  have e := Certificates.certificate812461.2.2.2.2.1 k hk
  simp only [wordX_append, wordX_lWord, wordX_tWord, wordX_uWord] at e
  simpa only [mul_assoc] using e

theorem uD_mul_uD {j k : ℕ} (hj : j < 10) (hk : k < 10) :
    uD j * uD k = lD ((uCommN.getD j []).getD k (0, 0)).1 *
      tD ((uCommN.getD j []).getD k (0, 0)).2 * uD k * uD j := by
  have e := Certificates.certificate812461.2.2.2.2.2.1 j hj k hk
  simp only [wordX_append, wordX_lWord, wordX_tWord, wordX_uWord] at e
  simpa only [mul_assoc] using e

theorem wordD_coGens {i : ℕ} (hi : i < 9) :
    wordD (coGens.getD i []) = lD (coDecN.getD i (0, 0)).1 * tD (coDecN.getD i (0, 0)).2 := by
  have e := Certificates.certificate812461.2.2.2.2.2.2.1 i hi
  simp only [wordX_append, wordX_lWord, wordX_tWord, wordX_map_lift] at e
  simpa only [mul_assoc] using e

theorem wordD_pauliWords {i : ℕ} (hi : i < 15) :
    wordD (pauliWords.getD i []) =
      lD (paDecN.getD i (0, 0)).1 * tD (paDecN.getD i (0, 0)).2 := by
  have e := Certificates.certificate812461.2.2.2.2.2.2.2 i hi
  simp only [wordX_append, wordX_lWord, wordX_tWord, wordX_map_lift] at e
  simpa only [mul_assoc] using e

end CFSG.Monster.B.TwoA.Sp8.WordRel
