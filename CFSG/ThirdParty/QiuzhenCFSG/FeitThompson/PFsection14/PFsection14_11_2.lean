module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_11_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.11.2)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

public theorem section14_eq_mul_of_pred_bounds {p q e : ℕ}
    (hepos : 0 < e)
    (hlower : p * q - 1 ≤ e - 1)
    (hupper : e ≤ p * q) :
    e = p * q := by
  omega

public theorem section14_scalarProduct_self_of_irreducibleCharacterOnGroup
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  rw [hchar]
  exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

public theorem section14_scalarProduct_irreducible_eq_zero_of_ne
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hne : χ ≠ ψ) :
    Section1.scalarProduct G χ ψ = 0 := by
  rcases hχ with ⟨nχ, ρχ, hρχ, hχchar⟩
  rcases hψ with ⟨nψ, ρψ, hρψ, hψchar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    χ ψ ρχ ρψ hχchar hψchar hρχ hρψ hne

public theorem section14_scalarProduct_self_signedIrreducible
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using section14_scalarProduct_self_of_irreducibleCharacterOnGroup hμ
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * star (-1 : ℂ) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by
              simp [section14_scalarProduct_self_of_irreducibleCharacterOnGroup hμ]

public theorem section14_signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ ≠ 0) :
    ψ = χ ∨ ψ = -χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hψ with ⟨δ, hδ, ν, hν, rfl⟩
  by_cases hμν : μ = ν
  · subst hμν
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · left
      simp
    · right
      simp
    · right
      simp
    · left
      simp
  · have horth : Section1.scalarProduct G μ ν = 0 :=
      section14_scalarProduct_irreducible_eq_zero_of_ne hμ hν hμν
    exfalso
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact hsp (by simpa using horth)
    · have hzero : Section1.scalarProduct G μ (-ν) = 0 := by
        rw [show (-ν : Section1.ClassFunction G) = (-1 : ℂ) • ν by
              ext g
              simp,
            Section1.scalarProduct_smul_right]
        simp [horth]
      exact hsp (by simpa using hzero)
    · have hzero : Section1.scalarProduct G (-μ) ν = 0 := by
        rw [show (-μ : Section1.ClassFunction G) = (-1 : ℂ) • μ by
              ext g
              simp,
            Section1.scalarProduct_smul_left]
        simp [horth]
      exact hsp (by simpa using hzero)
    · have hzero : Section1.scalarProduct G (-μ) (-ν) = 0 := by
        rw [show (-μ : Section1.ClassFunction G) = (-1 : ℂ) • μ by
              ext g
              simp,
            show (-ν : Section1.ClassFunction G) = (-1 : ℂ) • ν by
              ext g
              simp,
            Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
        simp [horth]
      exact hsp (by simpa using hzero)

public theorem section14_signedIrreducible_eq_of_scalarProduct_eq_one
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ = 1) :
    ψ = χ := by
  rcases section14_signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hχ hψ (by simp [hsp]) with hEq | hEq
  · exact hEq
  · have hcontra : (-1 : ℂ) = 1 := by
      calc
        (-1 : ℂ) = Section1.scalarProduct G χ (-χ) := by
            rw [show -χ = (-1 : ℂ) • χ by
              ext g
              simp]
            rw [Section1.scalarProduct_smul_right,
              section14_scalarProduct_self_signedIrreducible hχ]
            simp
        _ = 1 := by
            rw [← hEq]
            exact hsp
    norm_num at hcontra

public theorem section14_eq_neg_of_scalarProduct_eq_neg_one_signed
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ = -1) :
    ψ = -χ := by
  rcases section14_signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hχ hψ (by simp [hsp]) with hEq | hEq
  · have hself : Section1.scalarProduct G χ χ = 1 :=
      section14_scalarProduct_self_signedIrreducible hχ
    have hcontra : (1 : ℂ) = -1 := by
      simpa [hEq, hself] using hsp
    norm_num at hcontra
  · exact hEq

public theorem section14_signedIrreducible_conjugateCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section3.IsSignedIrreducibleCharacter (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  refine ⟨ε, hε, Section1.conjugateCharacter μ,
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hμ, ?_⟩
  rcases hε with rfl | rfl <;>
    ext g <;> simp [Section1.conjugateCharacter]

public theorem section14_scalarProduct_signedIrreducible_eq_neg_one_or_zero_or_one
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ) :
    Section1.scalarProduct G χ ψ = -1 ∨
      Section1.scalarProduct G χ ψ = 0 ∨
        Section1.scalarProduct G χ ψ = 1 := by
  by_cases hzero : Section1.scalarProduct G χ ψ = 0
  · exact Or.inr (Or.inl hzero)
  rcases section14_signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero
      hχ hψ hzero with hEq | hEq
  · right
    right
    rw [hEq]
    exact section14_scalarProduct_self_signedIrreducible hχ
  · left
    rw [hEq]
    rw [show (-χ : Section1.ClassFunction G) = (-1 : ℂ) • χ by
      ext g
      simp]
    rw [Section1.scalarProduct_smul_right,
      section14_scalarProduct_self_signedIrreducible hχ]
    simp

public theorem section14_scalarProduct_sign_of_diff_scalar_eq_one
    {G : Type u} [Group G] [Finite G]
    {χ ψτ : Section1.ClassFunction G}
    (hχVirt : Theory.Character.IsVirtualCharacter χ)
    (hχSelf : Section1.scalarProduct G χ χ = 1)
    (hψτ : Section3.IsSignedIrreducibleCharacter ψτ)
    (hdiff :
      Section1.scalarProduct G
        (ψτ - Section1.conjugateCharacter ψτ) χ = 1) :
    Section1.scalarProduct G χ ψτ = 1 ∨
      Section1.scalarProduct G χ (Section1.conjugateCharacter ψτ) = -1 := by
  have hχSigned : Section3.IsSignedIrreducibleCharacter χ :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hχVirt hχSelf
  have hconjSigned :
      Section3.IsSignedIrreducibleCharacter
        (Section1.conjugateCharacter ψτ) :=
    section14_signedIrreducible_conjugateCharacter hψτ
  let a : ℂ := Section1.scalarProduct G χ ψτ
  let b : ℂ :=
    Section1.scalarProduct G χ (Section1.conjugateCharacter ψτ)
  have ha :
      a = -1 ∨ a = 0 ∨ a = 1 := by
    simpa [a] using
      section14_scalarProduct_signedIrreducible_eq_neg_one_or_zero_or_one
        hχSigned hψτ
  have hb :
      b = -1 ∨ b = 0 ∨ b = 1 := by
    simpa [b] using
      section14_scalarProduct_signedIrreducible_eq_neg_one_or_zero_or_one
        hχSigned hconjSigned
  have hswap₁ :
      Section1.scalarProduct G ψτ χ =
        star (Section1.scalarProduct G χ ψτ) := by
    exact (Section1.scalarProduct_star_swap (G := G) ψτ χ).symm
  have hswap₂ :
      Section1.scalarProduct G (Section1.conjugateCharacter ψτ) χ =
        star (Section1.scalarProduct G χ (Section1.conjugateCharacter ψτ)) := by
    exact (Section1.scalarProduct_star_swap (G := G)
      (Section1.conjugateCharacter ψτ) χ).symm
  have hdiff' : star a - star b = 1 := by
    rw [Section5.scalarProduct_sub_left] at hdiff
    rw [hswap₁, hswap₂] at hdiff
    simpa [a, b] using hdiff
  rcases ha with ha | ha | ha
  · rcases hb with hb | hb | hb <;> rw [ha, hb] at hdiff' <;> norm_num at hdiff'
  · rcases hb with hb | hb | hb
    · right
      simpa [b] using hb
    · rw [ha, hb] at hdiff'
      norm_num at hdiff'
    · rw [ha, hb] at hdiff'
      norm_num at hdiff'
  · left
    simpa [a] using ha

public theorem section14_psiTau_signedIrreducible_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    {ψτ : Section1.ClassFunction G}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (hψτ : ψτ = τM₁ ψ) :
    Section3.IsSignedIrreducibleCharacter ψτ := by
  rcases h1410 with
    ⟨_hMmax, _hModd, _hVnorm, _hMF, _hTypeI, _hDade, _hMfam, _h52b, hExt,
      hψmem, hψirr, _hψdeg, _hβM⟩
  rcases hExt with ⟨hIso, hVirt, _hagrees⟩
  have hψspan : Section5.integerSpan Mfam ψ :=
    Section5.integerSpan_of_mem Mfam hψmem
  have hvirt : Theory.Character.IsVirtualCharacter (τM₁ ψ) :=
    hVirt ψ hψspan
  have hself : Section1.scalarProduct G (τM₁ ψ) (τM₁ ψ) = 1 := by
    calc
      Section1.scalarProduct G (τM₁ ψ) (τM₁ ψ)
          = Section1.scalarProduct M ψ ψ := hIso ψ ψ hψspan hψspan
      _ = 1 := section14_scalarProduct_self_of_irreducibleCharacterOnGroup hψirr
  have hsigned : Section3.IsSignedIrreducibleCharacter (τM₁ ψ) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself
  simpa [hψτ] using hsigned

public theorem section14_phiTau_signedIrreducible_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax L H P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {φτ : Section1.ClassFunction G}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (hφτ : φτ = τL₁ φ) :
    Section3.IsSignedIrreducibleCharacter φτ := by
  rcases h143 with
    ⟨_hLmax, _hUnorm, _hMF, _hTypeI, _hDade, _hLfam, _h52b, hExt,
      hφmem, hφirr, _hφdeg, _hβS, _hβT, _hβL⟩
  rcases hExt with ⟨hIso, hVirt, _hagrees⟩
  have hφspan : Section5.integerSpan Lfam φ :=
    Section5.integerSpan_of_mem Lfam hφmem
  have hvirt : Theory.Character.IsVirtualCharacter (τL₁ φ) :=
    hVirt φ hφspan
  have hself : Section1.scalarProduct G (τL₁ φ) (τL₁ φ) = 1 := by
    calc
      Section1.scalarProduct G (τL₁ φ) (τL₁ φ)
          = Section1.scalarProduct L φ φ := hIso φ φ hφspan hφspan
      _ = 1 := section14_scalarProduct_self_of_irreducibleCharacterOnGroup hφirr
  have hsigned : Section3.IsSignedIrreducibleCharacter (τL₁ φ) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt hself
  simpa [hφτ] using hsigned

public theorem section14_expansion_alternative_of_signed_remainder
    {G : Type u} [Group G] [Finite G]
    {sum β χ ψτ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψτ : Section3.IsSignedIrreducibleCharacter ψτ)
    (hβ : β = sum - χ)
    (hsp :
      Section1.scalarProduct G χ ψτ = 1 ∨
        Section1.scalarProduct G χ (Section1.conjugateCharacter ψτ) = -1) :
    β = sum - ψτ ∨ β = sum + Section1.conjugateCharacter ψτ := by
  rcases hsp with hsp | hsp
  · have hψeq : ψτ = χ :=
      section14_signedIrreducible_eq_of_scalarProduct_eq_one hχ hψτ hsp
    left
    simpa [hψeq] using hβ
  · have hconjSigned :
      Section3.IsSignedIrreducibleCharacter (Section1.conjugateCharacter ψτ) :=
      section14_signedIrreducible_conjugateCharacter hψτ
    have hconjEq : Section1.conjugateCharacter ψτ = -χ :=
      section14_eq_neg_of_scalarProduct_eq_neg_one_signed hχ hconjSigned hsp
    right
    rw [hβ, hconjEq]
    ext g
    ring_nf

public theorem section14_finset_forall_eq_one_of_one_le_sum_le_card
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hge : ∀ x ∈ s, (1 : ℝ) ≤ f x)
    (hsum : s.sum f ≤ (s.card : ℝ)) :
    ∀ x ∈ s, f x = 1 := by
  have hcard_le_sum : (s.card : ℝ) ≤ s.sum f := by
    calc
      (s.card : ℝ) = s.sum (fun _x => (1 : ℝ)) := by simp
      _ ≤ s.sum f := Finset.sum_le_sum hge
  have hsum_eq : s.sum f = (s.card : ℝ) :=
    le_antisymm hsum hcard_le_sum
  have hdiffsum : s.sum (fun x => f x - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsum_eq]
    simp
  have hdiff_nonneg : ∀ x ∈ s, 0 ≤ f x - 1 := by
    intro x hx
    exact sub_nonneg.mpr (hge x hx)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiffsum
  intro x hx
  have hxzero : f x - 1 = 0 := hzero x hx
  linarith

public theorem section14_int_eq_one_or_neg_one_of_normSq_intCast_eq_one
    (n : ℤ) (h : Complex.normSq (n : ℂ) = 1) :
    n = 1 ∨ n = -1 := by
  have hsquare : (n : ℝ) ^ 2 = 1 := by
    simpa [Complex.normSq_intCast, pow_two] using h
  have hsquare_int : n ^ 2 = 1 := by
    exact_mod_cast hsquare
  exact sq_eq_one_iff.mp hsquare_int

public theorem section14_normSq_ge_one_of_odd_intCast
    (n : ℤ) (hn : Odd n) :
    (1 : ℝ) ≤ Complex.normSq (n : ℂ) := by
  exact
    section14_normSq_ge_one_of_intCast_ne_zero_for_oddScalarProduct n
      (by
        intro hzero
        rw [hzero] at hn
        exact Int.not_odd_zero hn)

public theorem section14_odd_integer_coefficients_sign_of_normSq_sum_le_card
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (coeff : ι → κ → ℤ)
    (hodd : ∀ i j, Odd (coeff i j))
    (hsum :
      (Finset.univ : Finset (ι × κ)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        (Fintype.card (ι × κ) : ℝ)) :
    ∀ i j, coeff i j = 1 ∨ coeff i j = -1 := by
  let s : Finset (ι × κ) := Finset.univ
  have hterm :
      ∀ ij ∈ s, Complex.normSq (coeff ij.1 ij.2 : ℂ) = 1 := by
    refine section14_finset_forall_eq_one_of_one_le_sum_le_card
      s (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ?_ ?_
    · intro ij _hij
      exact section14_normSq_ge_one_of_odd_intCast
        (coeff ij.1 ij.2) (hodd ij.1 ij.2)
    · simpa [s] using hsum
  intro i j
  exact section14_int_eq_one_or_neg_one_of_normSq_intCast_eq_one
    (coeff i j) (by simpa [s] using hterm (i, j) (Finset.mem_univ (i, j)))

public theorem section14_odd_integer_coefficients_of_row_col_exchange
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (i0 : ι) (j0 : κ) (coeff : ι → κ → ℤ)
    (h00 : coeff i0 j0 = 1)
    (hrow : ∀ j, j ≠ j0 → Odd (coeff i0 j))
    (hcol : ∀ i, i ≠ i0 → Odd (coeff i j0))
    (hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0) :
    ∀ i j, Odd (coeff i j) := by
  intro i j
  by_cases hi : i = i0
  · subst i
    by_cases hj : j = j0
    · subst j
      rw [h00]
      norm_num
    · exact hrow j hj
  · by_cases hj : j = j0
    · subst j
      exact hcol i hi
    · rcases hcol i hi with ⟨a, ha⟩
      rcases hrow j hj with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rw [hexchange i j hi hj, ha, hb, h00]
      ring

public theorem section14_odd_int_of_intCast_oddScalarProduct
    {z : ℂ} {n : ℤ}
    (hz : z = (n : ℂ))
    (hodd : Section13.oddScalarProduct z) :
    Odd n := by
  rcases hodd with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hcast : (n : ℂ) = ((2 * m + 1 : ℤ) : ℂ) := by
    rw [← hz]
    simpa using hm.symm
  exact_mod_cast hcast

public theorem section14_int_eq_of_complex_cast_eq
    {a b c d : ℤ}
    (h : (a : ℂ) = (b : ℂ) + (c : ℂ) - (d : ℂ)) :
    a = b + c - d := by
  exact_mod_cast h

public theorem section14_pf36_coeff_eq_scalarProduct
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ β : Section1.ClassFunction G}
    {a : I → J → ℂ}
    {h31 : Section3.hypothesis_3_1_statement W1 W2 W}
    {hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (h36 : Section3.hypothesis_3_6_statement W1 W2 W I J i0 j0
      ω σ ψ β a h31 hω)
    (i : I) (j : J) :
    a i j = Section1.scalarProduct G ψ (σ (ω i j)) := by
  classical
  rcases h36 with ⟨h32, hβorth, hψ, _hβclass, _hψclass, _hvanish⟩
  have hcoeff :
      Section1.scalarProduct G
        (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2))
        (σ (ω i j)) = a i j := by
    have hsumfun :
        (∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) =
          (fun g : G => ∑ p : I × J, (a p.1 p.2 • σ (ω p.1 p.2)) g) := by
      ext g
      simp
    rw [hsumfun]
    rw [Section1.scalarProduct_fintype_sum_left]
    rw [Finset.sum_eq_single (i, j)]
    · rw [Section1.scalarProduct_smul_left]
      have hself :
          Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
        exact h32.1 (ω i j) (ω i j) (hω.is_class i j) (hω.is_class i j)
          |>.trans (by simpa using hω.orthonormal (i, j) (i, j))
      simp [hself]
    · intro p _hp hpne
      rw [Section1.scalarProduct_smul_left]
      have horth :
          Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω i j)) = 0 := by
        have hsp :=
          h32.1 (ω p.1 p.2) (ω i j) (hω.is_class p.1 p.2)
            (hω.is_class i j)
        have hpne' : p ≠ (i, j) := hpne
        simpa [hpne'] using hsp.trans
          (by simpa [hpne'] using hω.orthonormal p (i, j))
      simp [horth]
    · intro hnot
      exact False.elim (hnot (by simp))
  have hmain :
      Section1.scalarProduct G ψ (σ (ω i j)) =
        Section1.scalarProduct G
          ((∑ p : I × J, a p.1 p.2 • σ (ω p.1 p.2)) + β)
          (σ (ω i j)) := by
    rw [hψ]
  rw [hmain, Section1.scalarProduct_add_left, hcoeff,
    hβorth (ω i j) (hω.is_class i j)]
  simp

public theorem section14_hypothesis_3_6_of_projection
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ψ : Section1.ClassFunction G}
    {h31 : Section3.hypothesis_3_1_statement W1 W2 W}
    {hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω}
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (hψclass : Section1.IsClassFunction ψ)
    (hψvanish : Section3.VanishesOn ψ (Section3.cyclicTISet W1 W2 W)) :
    let coeff : I → J → ℂ := fun i j =>
      Section1.scalarProduct G ψ (σ (ω i j))
    let β : Section1.ClassFunction G :=
      ψ - ∑ p : I × J, coeff p.1 p.2 • σ (ω p.1 p.2)
    Section3.hypothesis_3_6_statement W1 W2 W I J i0 j0
      ω σ ψ β coeff h31 hω := by
  classical
  intro coeff β
  have hσorth :
      Section3.IsOrthonormalDoubleFamily (fun i j => σ (ω i j)) := by
    intro p q
    exact (hσ.1 (ω p.1 p.2) (ω q.1 q.2)
      (hω.is_class p.1 p.2) (hω.is_class q.1 q.2)).trans
        (hω.orthonormal p q)
  have hβorth_base :
      ∀ p : I × J,
        Section1.scalarProduct G β (σ (ω p.1 p.2)) = 0 := by
    intro p
    have hproj :
        Section1.scalarProduct G
            (∑ q : I × J, coeff q.1 q.2 • σ (ω q.1 q.2))
            (σ (ω p.1 p.2)) =
          coeff p.1 p.2 := by
      have hsumfun :
          (∑ q : I × J, coeff q.1 q.2 • σ (ω q.1 q.2)) =
            (fun g : G => ∑ q : I × J,
              (coeff q.1 q.2 • σ (ω q.1 q.2)) g) := by
        ext g
        simp
      rw [hsumfun]
      rw [Section1.scalarProduct_fintype_sum_left]
      rw [Finset.sum_eq_single p]
      · rw [Section1.scalarProduct_smul_left]
        have hself :
            Section1.scalarProduct G (σ (ω p.1 p.2)) (σ (ω p.1 p.2)) = 1 := by
          simpa using hσorth p p
        simp [hself]
      · intro q _hq hqne
        rw [Section1.scalarProduct_smul_left]
        have horth :
            Section1.scalarProduct G (σ (ω q.1 q.2)) (σ (ω p.1 p.2)) = 0 := by
          simpa [hqne] using hσorth q p
        simp [horth]
      · intro hp
        exact False.elim (hp (by simp))
    have hnegSum :
        (-(∑ q : I × J, coeff q.1 q.2 • σ (ω q.1 q.2)) :
            Section1.ClassFunction G) =
          (-1 : ℂ) • ∑ q : I × J, coeff q.1 q.2 • σ (ω q.1 q.2) := by
      ext g
      simp
    dsimp [β, coeff]
    rw [sub_eq_add_neg, Section1.scalarProduct_add_left, hnegSum,
      Section1.scalarProduct_smul_left, hproj]
    ring
  refine ⟨hσ, ?_, ?_, ?_, hψclass, hψvanish⟩
  · intro α hα
    have hαexp :
        σ α =
          Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => σ (ω p.1 p.2)) := by
      calc
        σ α =
            σ (Section1.weightedFamilySum
              (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
              (fun p : I × J => ω p.1 p.2)) := by
              rw [Section3.weightedFamilySum_eq_of_inner_omega_pf39
                (W1 := W1) (W2 := W2) (W := W) (I := I) (J := J)
                (i0 := i0) (j0 := j0) (ω := ω) h31 hω α]
        _ = Section1.weightedFamilySum
            (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
            (fun p : I × J => σ (ω p.1 p.2)) := by
              let s : Finset (I × J) :=
                @Finset.univ (I × J) (Fintype.ofFinite (I × J))
              have hdom :
                  Section1.weightedFamilySum
                    (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
                    (fun p : I × J => ω p.1 p.2) =
                    s.sum (fun p : I × J =>
                      Section1.scalarProduct W α (ω p.1 p.2) • ω p.1 p.2) := by
                ext g
                simp [s, Section1.weightedFamilySum, smul_eq_mul]
              have hcod :
                  Section1.weightedFamilySum
                    (fun p : I × J => Section1.scalarProduct W α (ω p.1 p.2))
                    (fun p : I × J => σ (ω p.1 p.2)) =
                    s.sum (fun p : I × J =>
                      Section1.scalarProduct W α (ω p.1 p.2) • σ (ω p.1 p.2)) := by
                ext g
                simp [s, Section1.weightedFamilySum, smul_eq_mul]
              rw [hdom, hcod, map_sum]
              refine Finset.sum_congr rfl ?_
              intro p _hp
              rw [map_smul]
    rw [hαexp, Section1.scalarProduct_weightedFamilySum_right]
    simp [hβorth_base]
  · ext g
    dsimp [β]
    simp [sub_eq_add_neg]
  · intro x g
    dsimp [β]
    rw [hψclass x g]
    congr 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro p _hp
    congr 1
    exact hσ.2.2.2.1 (ω p.1 p.2) (hω.is_class p.1 p.2) x g

public theorem section14_betaInput_CFOn_typeIASet
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {ψ : Section1.ClassFunction M}
    (hMF : section16MFSubgroup M K)
    (hPunct : Section7.puncturedInducedFamily (K.subgroupOf M) Mfam)
    (hψmem : ψ ∈ Mfam)
    (hψdeg : Section1.degree ψ = (K.relIndex M : ℂ)) :
    Section2.CFOn M (Section12.typeIASet M K)
      (Section7.theorem_7_8_betaInput M K ψ) := by
  classical
  have hKleM : K ≤ M := Section12.section16MFSubgroup_le hMF
  haveI : (K.subgroupOf M).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  rcases (hPunct ψ).mp hψmem with ⟨θψ, _hθψ, _hθψne, hψeq⟩
  have hprincipalClass :
      Section1.IsClassFunction (Section7.principalInducedCharacter M K) := by
    unfold Section7.principalInducedCharacter
    exact Section1.inducedCF_isClassFunction (K.subgroupOf M)
      (Section1.principalCharacter (K.subgroupOf M))
  have hψclass : Section1.IsClassFunction ψ := by
    rw [hψeq]
    exact Section1.inducedCF_isClassFunction (K.subgroupOf M) θψ
  constructor
  · intro x g
    simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
      hprincipalClass x g, hψclass x g]
  · intro l hlA
    have hprincipal_degree :
        Section1.degree (Section7.principalInducedCharacter M K) =
          (K.relIndex M : ℂ) := by
      unfold Section7.principalInducedCharacter
      rw [Section1.degree_inducedClassFunction]
      simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
    have hprincipal_one :
        Section7.principalInducedCharacter M K (1 : M) = (K.relIndex M : ℂ) := by
      simpa [Section1.degree_apply] using hprincipal_degree
    have hψ_one : ψ 1 = (K.relIndex M : ℂ) := by
      simpa [Section1.degree_apply] using hψdeg
    have hβ_one : Section7.theorem_7_8_betaInput M K ψ (1 : M) = 0 := by
      simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipal_one, hψ_one]
    by_cases hl_one : l = 1
    · simpa [hl_one] using hβ_one
    · have hl_ne_oneG : (l : G) ≠ 1 := by
        intro hG
        apply hl_one
        ext
        exact hG
      have hlnotK : (l : G) ∉ K := by
        intro hlK
        apply hlA
        exact Section12.nonidentity_kernel_subset_typeIASet M K hKleM
          ⟨hlK, hl_ne_oneG⟩
      have hlnotKsub : l ∉ K.subgroupOf M := by
        intro hlKsub
        exact hlnotK hlKsub
      have hprincipal_zero : Section7.principalInducedCharacter M K l = 0 := by
        unfold Section7.principalInducedCharacter
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (K.subgroupOf M) (Section1.principalCharacter (K.subgroupOf M)) hlnotKsub
      have hψ_zero : ψ l = 0 := by
        rw [hψeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (K.subgroupOf M) θψ hlnotKsub
      simp [Section7.theorem_7_8_betaInput, Pi.sub_apply,
        hprincipal_zero, hψ_zero]

public theorem section14_betaInput_tau_principal_scalar_typeIASet
    {G : Type u} [Group G] [Finite G]
    {M K : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {R : G → Subgroup G}
    {τM : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (hMF : section16MFSubgroup M K)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet M K R τM)
    (hPunct : Section7.puncturedInducedFamily (K.subgroupOf M) Mfam)
    (hψmem : ψ ∈ Mfam)
    (hψdeg : Section1.degree ψ = (K.relIndex M : ℂ))
    (hβM : βM = Section7.theorem_7_8_betaInput M K ψ) :
    Section1.scalarProduct G (τM βM) (Section1.principalCharacter G) = 1 := by
  classical
  let βinput : Section1.ClassFunction M := Section7.theorem_7_8_betaInput M K ψ
  have hβCFOn : Section2.CFOn M (Section12.typeIASet M K) βinput :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hψmem hψdeg
  rcases hDade with ⟨h22, hτM⟩
  rcases hτM with ⟨hAMG, hτM⟩
  have hτβ : τM βinput = Section2.dadeTransform R hAMG βinput :=
    hτM βinput hβCFOn
  have hprincipalG : Section1.IsClassFunction (Section1.principalCharacter G) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalM : Section1.IsClassFunction (Section1.principalCharacter M) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalAgree :
      ∀ ⦃a : G⦄, (ha : a ∈ Section12.typeIASet M K) →
        Section1.principalCharacter M ⟨a, hAMG a ha⟩ =
          Section2.dadeAveragingFunction M R (Section1.principalCharacter G)
            ⟨a, hAMG a ha⟩ := by
    intro a ha
    unfold Section2.dadeAveragingFunction
    simp only [Section1.principalCharacter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← (@Nat.card_eq_fintype_card
      (R (↑(⟨a, hAMG a ha⟩ : M)))
      (Fintype.ofFinite (R (↑(⟨a, hAMG a ha⟩ : M)))))]
    have hcard : (Nat.card (R a) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := R a)).ne'
    field_simp [hcard]
  have hDadeScalar :
      Section1.scalarProduct G (Section2.dadeTransform R hAMG βinput)
          (Section1.principalCharacter G) =
        Section1.scalarProduct M βinput (Section1.principalCharacter M) :=
    (Section2.proposition_2_7 (Section12.typeIASet M K) M R h22 hAMG
      βinput (Section1.principalCharacter G) hβCFOn hprincipalG
      (Section1.principalCharacter M) hprincipalM hprincipalAgree).1
  have hψ_principal :
      Section1.scalarProduct M ψ (Section1.principalCharacter M) = 0 :=
    Section7.theorem_7_8_punctured_member_principal_orthogonal
      (L := M) (H := K) (S := Mfam) hPunct hψmem
  have hβ_principal_M :
      Section1.scalarProduct M βinput (Section1.principalCharacter M) = 1 := by
    change Section1.scalarProduct M
      (Section7.principalInducedCharacter M K - ψ)
        (Section1.principalCharacter M) = 1
    rw [Section5.scalarProduct_sub_left,
      Section7.theorem_7_8_principalInduced_principal_scalar,
      hψ_principal]
    simp
  calc
    Section1.scalarProduct G (τM βM) (Section1.principalCharacter G)
        = Section1.scalarProduct G (τM βinput) (Section1.principalCharacter G) := by
          rw [hβM]
    _ = Section1.scalarProduct G (Section2.dadeTransform R hAMG βinput)
        (Section1.principalCharacter G) := by
          rw [hτβ]
    _ = Section1.scalarProduct M βinput (Section1.principalCharacter M) := hDadeScalar
    _ = 1 := hβ_principal_M

public theorem section14_betaM_tau_principal_scalar_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section1.scalarProduct G (τM βM) (Section1.principalCharacter G) = 1 := by
  rcases h1410 with
    ⟨_hMmax, _hModd, _hNormVleM, hKMF, _hTypeI, hDadeM, hPunctM,
      _h52M, _hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadeM with ⟨R, hDadeM, _hSupportM⟩
  exact section14_betaInput_tau_principal_scalar_typeIASet
    (R := R) hKMF hDadeM hPunctM hψmem hψdeg hβM

public theorem section14_betaM_tau_isClassFunction_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section1.IsClassFunction (τM βM) := by
  classical
  rcases h1410 with
    ⟨_hMmax, _hModd, _hNormVleM, hMF, _hTypeI, hDadePkg, hPunct,
      _h52M, _hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨R, hDadeM, _hSupportM⟩
  have hβinputCFOn :
      Section2.CFOn M (Section12.typeIASet M K)
        (Section7.theorem_7_8_betaInput M K ψ) :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hψmem hψdeg
  have hβCFOn :
      Section2.CFOn M (Section12.typeIASet M K) βM := by
    rw [hβM]
    exact hβinputCFOn
  rcases hDadeM with ⟨h22, hτpack⟩
  rcases hτpack with ⟨hAMG, hτeq⟩
  have hτβ : τM βM = Section2.dadeTransform R hAMG βM :=
    hτeq βM hβCFOn
  rw [hτβ]
  exact Section2.dadeTransform_isClassFunction_of_CFOn
    (Section12.typeIASet M K) M R h22 hAMG βM hβCFOn

public theorem section14_betaM_tau_isVirtualCharacter_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Theory.Character.IsVirtualCharacter (τM βM) := by
  classical
  rcases h1410 with
    ⟨_hMmax, _hModd, _hNormVleM, hMF, _hTypeI, hDadePkg, hPunct,
      _h52M, _hCoherM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨R, hDadeM, _hSupportM⟩
  have hβinputCFOn :
      Section2.CFOn M (Section12.typeIASet M K)
        (Section7.theorem_7_8_betaInput M K ψ) :=
    section14_betaInput_CFOn_typeIASet hMF hPunct hψmem hψdeg
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (Section7.principalInducedCharacter M K) := by
    unfold Section7.principalInducedCharacter
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (K.subgroupOf M) Section3.isVirtualCharacter_principalCharacter
  have hβinputVirt :
      Theory.Character.IsVirtualCharacter
        (Section7.theorem_7_8_betaInput M K ψ) := by
    exact Section3.isVirtualCharacter_sub hprincipalVirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hψirr)
  have hβCFOn :
      Section2.CFOn M (Section12.typeIASet M K) βM := by
    rw [hβM]
    exact hβinputCFOn
  have hβVirtOn :
      Section2.virtualCharacterOn M (Section12.typeIASet M K) βM := by
    constructor
    · rw [hβM]
      exact hβinputVirt
    · exact hβCFOn.2
  rcases hDadeM with ⟨h22, hτpack⟩
  rcases hτpack with ⟨hAMG, hτeq⟩
  have hτβ : τM βM = Section2.dadeTransform R hAMG βM :=
    hτeq βM hβCFOn
  have hDadeVirt :=
    (Section2.theorem_2_6 (Section12.typeIASet M K) M R h22 hAMG).2
      βM hβVirtOn
  simpa [Section2.virtualCharacterOfG, hτβ] using hDadeVirt

public theorem section14_inducedFamilyNotation_insert_principal_of_punctured
    {L : Type u} [Group L] [Finite L]
    {H : Subgroup L}
    {S : Finset (Section1.ClassFunction L)}
    (hS : Section7.puncturedInducedFamily H S) :
    Section7.inducedFamilyNotation H
      (insert (Section1.inducedCF H (Section1.principalCharacter H)) S) := by
  classical
  intro χ
  constructor
  · intro hχ
    rw [Finset.mem_insert] at hχ
    rcases hχ with hχ | hχ
    · refine ⟨Section1.principalCharacter H, ?_, ?_⟩
      · exact Section3.principalCharacter_isIrreducibleCharacterOnGroup
      · simp [hχ]
    · rcases (hS χ).mp hχ with ⟨θ, hθirr, _hθne, hχeq⟩
      exact ⟨θ, hθirr, hχeq⟩
  · intro hχ
    rcases hχ with ⟨θ, hθirr, hχeq⟩
    rw [Finset.mem_insert]
    by_cases hθ : θ = Section1.principalCharacter H
    · left
      rw [hχeq, hθ]
    · right
      exact (hS χ).mpr ⟨θ, hθirr, hθ, hχeq⟩

public theorem section14_hypothesis_7_6_typeI_typeIASet_of_dade
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L H : Subgroup G}
    {R : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    (hLmax : L ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (hDade : Section12.dadeIsometryRelativeToTypeIASet L H R τ)
    (hT : Section7.inducedFamilyNotation (H.subgroupOf L) T) :
    Section7.hypothesis_7_6_statement
      (Section12.typeIASet L H) L H R T := by
  classical
  have hHL : H ≤ L := Section12.section16MFSubgroup_le hMF
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  rcases hDade with ⟨h22, _hτ⟩
  have hfrob : Section7.frobeniusWithKernel L H :=
    Section12.theorem_12_7 L H hLmax hMF hTypeI
  have hA :
      Section12.typeIASet L H = Section7.puncturedSubgroupSet H := by
    calc
      Section12.typeIASet L H =
          section16NonidentityElements (H : Set G) :=
        Section12.typeIASet_eq_nonidentity_kernel_of_frobenius L H hfrob
      _ = Section7.puncturedSubgroupSet H := by
        ext g
        simp [Section7.puncturedSubgroupSet, section16NonidentityElements]
  exact ⟨hHL, hHnormal, h22, hA, hT⟩

public theorem section14_theorem_7_8_hypothesis_of_typeI_punctured
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {τ τ₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (hMF : section16MFSubgroup L H)
    (hTypeI : Section8.typeIDefinitionData L H)
    (hS : Section7.puncturedInducedFamily (H.subgroupOf L) S)
    (hExt : Section7.isCoherentExtension S τ τ₁)
    (hζmem : ζ ∈ S)
    (hζirr : Section1.IsIrreducibleCharacterOnGroup ζ)
    (hζdeg : Section1.degree ζ = (H.relIndex L : ℂ)) :
    Section7.theorem_7_8_hypothesis L H
      (insert (Section7.principalInducedCharacter L H) S) S τ τ₁ ζ := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  have hHL : H ≤ L := Section12.section16MFSubgroup_le hMF
  have hHnormal : (H.subgroupOf L).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hMF
  have hoddL : Odd (Nat.card L) :=
    Section12.odd_card_of_typeIDefinitionData L H hTypeI
  have hζbar : Section1.conjugateCharacter ζ ∈ S :=
    Section12.puncturedInducedFamily_conjugate_mem L H S hHnormal hS ζ hζmem
  have hζne : ζ ≠ Section1.conjugateCharacter ζ :=
    Section12.puncturedInducedFamily_ne_conjugate L H S hHnormal hoddL hS ζ hζmem
  have hζchar : Section1.IsCharacter ζ := by
    rcases (hS ζ).mp hζmem with ⟨θ, hθirr, _hθne, rfl⟩
    exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ
      (Section12.isCharacter_of_isIrreducibleCharacterOnGroup hθirr)
  have hnonempty : Section5.integerSpanOnNonempty S Section5.puncturedSet :=
    Section5.integerSpanOnNonempty_of_conjugate_pair hζmem hζbar hζne hζchar
  have hsrc : Section5.sourceVirtualCharacters S :=
    Section12.sourceVirtualCharacters_of_puncturedInducedFamily L H S hS
  rcases hExt with ⟨hIso, hVirt, hAgree⟩
  have hcoherent : Section6.coherentFamily S τ :=
    ⟨hsrc, hnonempty, τ₁, hIso, hVirt, hAgree⟩
  refine ⟨hHL, ?_, hS, hcoherent, ⟨hIso, hVirt, hAgree⟩,
    hζmem, hζirr, hζdeg⟩
  intro χ
  constructor
  · intro hχS
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_insert]
      exact Or.inr hχS
    · intro hχprincipal
      have hzero :
          Section1.scalarProduct L (Section7.principalInducedCharacter L H) χ = 0 :=
        Section7.theorem_7_8_principalInduced_punctured_member_scalar
          hHnormal hS hχS
      have hself :
          Section1.scalarProduct L (Section7.principalInducedCharacter L H)
              (Section7.principalInducedCharacter L H) = (H.relIndex L : ℂ) :=
        Section7.theorem_7_8_principalInduced_self_scalar hHnormal
      have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
        haveI : (H.subgroupOf L).FiniteIndex := inferInstance
        have hrel : H.relIndex L ≠ 0 := by
          simpa [Subgroup.relIndex] using
            (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
        exact_mod_cast hrel
      apply hrel_ne
      calc
        (H.relIndex L : ℂ) =
            Section1.scalarProduct L (Section7.principalInducedCharacter L H)
              (Section7.principalInducedCharacter L H) := hself.symm
        _ = Section1.scalarProduct L (Section7.principalInducedCharacter L H) χ := by
              rw [hχprincipal]
        _ = 0 := hzero
  · intro hχ
    rcases hχ with ⟨hχT, hχne⟩
    rw [Finset.mem_insert] at hχT
    rcases hχT with hχprincipal | hχS
    · exact False.elim (hχne hχprincipal)
    · exact hχS

public theorem section14_frobenius_relIndex_two_mul_le_kernel_pred
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hoddL : Odd (Nat.card L))
    (hfrob : Section7.frobeniusWithKernel L H) :
    2 * H.relIndex L ≤ Nat.card H - 1 := by
  rcases hfrob with ⟨hHL, hHnormal, R, hcomp, hHne, _hRne, hcent⟩
  let Hsub : Subgroup L := H.subgroupOf L
  haveI : Hsub.Normal := by
    simpa [Hsub] using hHnormal
  have hindex : H.relIndex L = Nat.card R := by
    rw [Subgroup.relIndex, hcomp.symm.index_eq_card]
  have hHsubcard : Nat.card Hsub = Nat.card H := by
    simpa [Hsub] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hdvdSub : Nat.card R ∣ Nat.card Hsub - 1 := by
    letI : MulDistribMulAction R Hsub :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := L) R Hsub
        (Subgroup.le_normalizer_of_normal (H := Hsub))
    have hfree : ∀ a : R, a ≠ 1 → ∀ g : Hsub, a • g = g → g = 1 := by
      intro r hr x hfix
      have hconj : (r : L) * (x : L) * (r : L)⁻¹ = (x : L) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfix
      have hcomm : (r : L) * (x : L) = (x : L) * (r : L) := by
        have h := congrArg (fun t : L => t * (r : L)) hconj
        simpa [mul_assoc] using h
      have hxcent : (x : L) ∈ Section2.centralizerIn Hsub (r : L) := by
        exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
      have hcent_eq : Section2.centralizerIn Hsub (r : L) = ⊥ := by
        simpa [Hsub] using hcent r hr
      have hxbot : (x : L) ∈ (⊥ : Subgroup L) := by
        simpa [hcent_eq] using hxcent
      exact Subtype.ext (by simpa using hxbot)
    exact section14_natCard_actor_dvd_group_card_sub_one hfree
  have hdvd : Nat.card R ∣ Nat.card H - 1 := by
    rw [hHsubcard] at hdvdSub
    exact hdvdSub
  have hHodd : Odd (Nat.card H) := by
    have hHsubOdd : Odd (Nat.card Hsub) :=
      Odd.of_dvd_nat hoddL (Subgroup.card_subgroup_dvd_card Hsub)
    rw [hHsubcard] at hHsubOdd
    exact hHsubOdd
  have hRodd : Odd (Nat.card R) :=
    Odd.of_dvd_nat hoddL (Subgroup.card_subgroup_dvd_card R)
  have hHsub_gt : 1 < Nat.card Hsub :=
    (Subgroup.one_lt_card_iff_ne_bot Hsub).2 (by simpa [Hsub] using hHne)
  have hHgt : 1 < Nat.card H := by
    rw [hHsubcard] at hHsub_gt
    exact hHsub_gt
  rcases hdvd with ⟨k, hk⟩
  have hHminus_pos : 0 < Nat.card H - 1 := Nat.sub_pos_of_lt hHgt
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : Nat.card H - 1 = 0 := by
      simpa [hk0] using hk
    exact (Nat.ne_of_gt hHminus_pos) hzero
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    rcases hHodd with ⟨m, hm⟩
    rcases hRodd with ⟨n, hn⟩
    subst k
    omega
  have hk_ge_two : 2 ≤ k := by omega
  have hleR : 2 * Nat.card R ≤ Nat.card R * k := by
    calc
      2 * Nat.card R = Nat.card R * 2 := by rw [Nat.mul_comm]
      _ ≤ Nat.card R * k := Nat.mul_le_mul_left (Nat.card R) hk_ge_two
  rw [hindex]
  exact hleR.trans_eq hk.symm

public theorem section14_frobenius_relIndex_le_kernel_pred_half
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hoddL : Odd (Nat.card L))
    (hfrob : Section7.frobeniusWithKernel L H) :
    H.relIndex L ≤ (Nat.card H - 1) / 2 := by
  have htwo :=
    section14_frobenius_relIndex_two_mul_le_kernel_pred
      (L := L) (H := H) hoddL hfrob
  omega

public theorem section14_betaM_CFOn_typeIASet_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section2.CFOn M (Section12.typeIASet M K) βM := by
  rcases h1410 with
    ⟨_hMmax, _hModd, _hNormVleM, hMF, _hTypeI, _hDadePkg, hPunct,
      _h52M, _hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rw [hβM]
  exact section14_betaInput_CFOn_typeIASet hMF hPunct hψmem hψdeg

public theorem section14_betaM_tau_vanishesOn_cyclicTISet_of_dadeSupport_nonmem
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (hsupport :
      ∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          ∀ g : G, g ∈ Section3.cyclicTISet W1 W2 W →
            g ∉ Section2.dadeSupport (Section12.typeIASet M K) R) :
    Section3.VanishesOn (τM βM) (Section3.cyclicTISet W1 W2 W) := by
  rcases hsupport with ⟨R, hDadeM, hnotSupport⟩
  have hβCFOn : Section2.CFOn M (Section12.typeIASet M K) βM :=
    section14_betaM_CFOn_typeIASet_of_hypothesis_14_10 h1410
  rcases hDadeM with ⟨_h22, hτM⟩
  rcases hτM with ⟨hAMG, hτM⟩
  intro g hg
  rw [hτM βM hβCFOn]
  exact Section2.dadeTransform_eq_zero_of_not_mem_support
    R hAMG βM (hnotSupport g hg)

public theorem section14_theorem_14_11_2_row_odd_of_pf13_19_source
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D M K : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (h111 : theorem_14_11_1_data M K p q u v) :
    ∀ j : ℕ, 0 < j → j < p →
      Section13.oddScalarProduct
        (Section1.scalarProduct G (τM βM) (ηNat 0 j)) := by
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadeM, hMfam,
      _h52M, hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadeM with ⟨RM, hDadeM, _hSupportM⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis M K Smax P W1 Mfam RM
        τS τM τM₁ ψ (τM₁ ψ) (μ 0 1) (τM βM)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hMfam, hCoherM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U V C D M K Sfam Tfam Mfam RM
    τS τT τM τM₁ ψ (τM βM)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τM₁ ψ) ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (K.relIndex M) hctx.1 hnotation hhyp
  rcases h111 with ⟨_hKgt, hratio, hupper⟩
  rcases h1319.2.2.2 with hfirst | hsecond
  · exfalso
    have hlt :
        ((u - 1 : ℕ) : ℝ) / (q : ℝ) <
          ((Nat.card K - 1 : ℕ) : ℝ) / ((K.relIndex M : ℕ) : ℝ) :=
      lt_trans hratio hupper
    exact (not_lt_of_ge hfirst.2) hlt
  · exact hsecond.1

public theorem section14_theorem_14_11_2_col_odd_of_pf13_19_source
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D M K : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (h111 : theorem_14_11_1_data M K p q u v) :
    ∀ i : ℕ, 0 < i → i < q →
      Section13.oddScalarProduct
        (Section1.scalarProduct G (τM βM) (ηNat i 0)) := by
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadeM, hMfam,
      _h52M, hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadeM with ⟨RM, hDadeM, _hSupportM⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis M K Tmax Q W2 Mfam RM
        τT τM τM₁ ψ (τM₁ ψ) (ν 1 0) (τM βM)
        (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν 1 0))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hMfam, hCoherM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Tmax Smax W W2 W1 Q P V U D C M K Tfam Sfam Mfam RM
    τT τS τM τM₁ ψ (τM βM)
    (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν 1 0))
    (τM₁ ψ) (fun i j => ωNat j i) (fun i j => ηNat j i)
    (fun i j => ν j i) (fun i j => μ j i)
    (fun i => νsum i) (fun i => μsum i) δ' δ σ q p v u d c
    (K.relIndex M)
    (section14_hypothesis_13_1_sourceData_swap hctx.1)
    (section14_hypothesis_13_1_characterNotationDataFor_swap hnotation)
    hhyp
  rcases h111 with ⟨_hKgt, _hratio, hupper⟩
  rcases h1319.2.2.2 with hfirst | hsecond
  · exfalso
    exact (not_lt_of_ge hfirst.2) hupper
  · intro i hi hlt
    simpa using hsecond.1 i hi hlt

public theorem section14_coefficients_pred_lower_of_row_col_exchange
    {p q e : ℕ}
    (i0 : Fin q) (j0 : Fin p)
    (coeff : Fin q → Fin p → ℤ)
    (h00 : coeff i0 j0 = 1)
    (hrow : ∀ j, j ≠ j0 → Odd (coeff i0 j))
    (hcol : ∀ i, i ≠ i0 → Odd (coeff i j0))
    (hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0)
    (hoff :
      (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        ((e - 1 : ℕ) : ℝ)) :
    p * q - 1 ≤ e - 1 := by
  classical
  let base : Fin q × Fin p := (i0, j0)
  let s : Finset (Fin q × Fin p) := Finset.univ.erase base
  have hodd : ∀ i j, Odd (coeff i j) :=
    section14_odd_integer_coefficients_of_row_col_exchange
      i0 j0 coeff h00 hrow hcol hexchange
  have hge :
      ∀ ij ∈ s, (1 : ℝ) ≤ Complex.normSq (coeff ij.1 ij.2 : ℂ) := by
    intro ij _hij
    exact section14_normSq_ge_one_of_odd_intCast
      (coeff ij.1 ij.2) (hodd ij.1 ij.2)
  have hcard_le :
      (s.card : ℝ) ≤
        s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
    calc
      (s.card : ℝ) = s.sum (fun _ij => (1 : ℝ)) := by simp
      _ ≤ s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) :=
        Finset.sum_le_sum hge
  have hcard : s.card = p * q - 1 := by
    simp [s, base, Fintype.card_prod, Nat.mul_comm]
  have hreal : ((p * q - 1 : ℕ) : ℝ) ≤ ((e - 1 : ℕ) : ℝ) := by
    calc
      ((p * q - 1 : ℕ) : ℝ) = (s.card : ℝ) := by rw [hcard]
      _ ≤ s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := hcard_le
      _ ≤ ((e - 1 : ℕ) : ℝ) := by
        simpa [s, base] using hoff
  exact_mod_cast hreal

public theorem section14_coefficients_normSq_sum_le_card_of_off_base_bound
    {p q e : ℕ}
    (i0 : Fin q) (j0 : Fin p)
    (coeff : Fin q → Fin p → ℤ)
    (h00 : (coeff i0 j0 : ℂ) = 1)
    (hepos : 0 < e)
    (hupper : e ≤ p * q)
    (hoff :
      (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        ((e - 1 : ℕ) : ℝ)) :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        (Fintype.card (Fin q × Fin p) : ℝ) := by
  classical
  let base : Fin q × Fin p := (i0, j0)
  let s : Finset (Fin q × Fin p) := Finset.univ.erase base
  have hbase_not_mem : base ∉ s := by
    simp [s]
  have hsum_univ :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
        Complex.normSq (coeff i0 j0 : ℂ) +
          s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
    rw [show (Finset.univ : Finset (Fin q × Fin p)) = insert base s by
      symm
      exact Finset.insert_erase (Finset.mem_univ base)]
    rw [Finset.sum_insert hbase_not_mem]
  have hbase_norm : Complex.normSq (coeff i0 j0 : ℂ) = 1 := by
    simpa using congrArg Complex.normSq h00
  have hoff_s :
      s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        ((e - 1 : ℕ) : ℝ) := by
    change (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
        (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
      ((e - 1 : ℕ) : ℝ)
    exact hoff
  have hsum_le_e :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤ (e : ℝ) := by
    calc
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ))
          = Complex.normSq (coeff i0 j0 : ℂ) +
              s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) :=
            hsum_univ
      _ = 1 + s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
            rw [hbase_norm]
      _ ≤ 1 + ((e - 1 : ℕ) : ℝ) := by
            nlinarith [hoff_s]
      _ = (e : ℝ) := by
            have hnat : 1 + (e - 1) = e := by omega
            exact_mod_cast hnat
  have hcard : Fintype.card (Fin q × Fin p) = p * q := by
    simp [Fintype.card_prod, Nat.mul_comm]
  have hupperR : (e : ℝ) ≤ (Fintype.card (Fin q × Fin p) : ℝ) := by
    rw [hcard]
    exact_mod_cast hupper
  exact hsum_le_e.trans hupperR

public theorem section14_theorem_14_11_2_cyclicTI_dadeSupport_nonmem_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U Vctx C D M K V : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U Vctx C D
      Sfam Tfam τS τT p q u v c d)
  (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM)
  (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ) :
    ∃ R : G → Subgroup G,
      Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
        ∀ g : G, g ∈ Section3.cyclicTISet W1 W2 W →
          g ∉ Section2.dadeSupport (Section12.typeIASet M K) R := by
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hMfam,
      _h52M, hCoherM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨R, hDadeM, _hSupportM⟩
  refine ⟨R, hDadeM, ?_⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis M K Smax P W1 Mfam R
        τS τM τM₁ ψ (τM₁ ψ) (μ 0 1) (τM βM)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hMfam, hCoherM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U Vctx C D M K Sfam Tfam Mfam R
    τS τT τM τM₁ ψ (τM βM)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τM₁ ψ) ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (K.relIndex M) hctx.1 hnotation hhyp
  intro g hg hgSupport
  have hgWconj :
      g ∈ section16ConjugatesOfSetBySet (W : Set G) Set.univ := by
    refine ⟨g, Section3.cyclicTISet_subset W1 W2 W hg, 1, Set.mem_univ _, ?_⟩
    simp
  exact (Set.disjoint_left.mp h1319.1 hgSupport) (Or.inr hgWconj)

public theorem section14_tauM1_mfam_sigma_orthogonal_of_pf13_19_source
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U Vctx C D M K V : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (Mfam : Finset (Section1.ClassFunction M))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U Vctx C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
          ∀ i : Fin q, ∀ j : Fin p,
            Section1.scalarProduct G (τM₁ χ) (σ (ω i j)) = 0 := by
  intro hctx h1410 χ hχ i j
  classical
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, _hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  have hhyp13 :
      Section13.theorem_13_19_hypothesis M K Smax P W1 Mfam RM
        τS τM τM₁ ψ (τM₁ ψ) (μ 0 1) (τM βM)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hPunctM, hExtM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U Vctx C D M K Sfam Tfam Mfam RM
    τS τT τM τM₁ ψ (τM βM)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τM₁ ψ) ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (K.relIndex M) hctx.1 hnotation hhyp13
  rcases hnotation with
    ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  have hωNat_eq : ωNat (i : ℕ) (j : ℕ) = ω i j :=
    hωNat_eq_ω (i : ℕ) (j : ℕ) i.isLt j.isLt
  have hησ : ηNat (i : ℕ) (j : ℕ) = σ (ω i j) := by
    rw [hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt, hωNat_eq]
  simpa [hησ] using h1319.2.1 χ hχ (i : ℕ) (j : ℕ) i.isLt j.isLt

public theorem section14_theorem_14_11_2_off_base_bound_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (_ : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        K ≠ V →
          theorem_14_11_1_data M K p q u v →
            e = K.relIndex M →
              (Finset.univ.erase (i0, j0) :
                  Finset (Fin q × Fin p)).sum
                    (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                  ((e - 1 : ℕ) : ℝ) := by
  intro hctx _h143 h1410 _hKV _h111 heq
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  rcases hσ with
    ⟨hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
  let MfullFam : Finset (Section1.ClassFunction M) :=
    insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM) (T := MfullFam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  have _hpf78_setup :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
          M K RM MfullFam ∧
        Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM ∧
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ :=
    ⟨h76M, hDadeAgreeM, h78M⟩
  have hβMτ_eq : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have hhyp13 :
      Section13.theorem_13_19_hypothesis M K Smax P W1 Mfam RM
        τS τM τM₁ ψ (τM₁ ψ) (μ 0 1) (τM βM)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hPunctM, hExtM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U V C D M K Sfam Tfam Mfam RM
    τS τT τM τM₁ ψ (τM βM)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τM₁ ψ) ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (K.relIndex M) hctx.1 hnotation hhyp13
  rcases hnotation with
    ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  have hMfam_orth :
      ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
        ∀ i : Fin q, ∀ j : Fin p,
          Section1.scalarProduct G (τM₁ χ) (σ (ω i j)) = 0 := by
    intro χ hχ i j
    have hωNat_eq : ωNat (i : ℕ) (j : ℕ) = ω i j :=
      hωNat_eq_ω (i : ℕ) (j : ℕ) i.isLt j.isLt
    have hησ : ηNat (i : ℕ) (j : ℕ) = σ (ω i j) := by
      rw [hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt, hωNat_eq]
    simpa [hησ] using h1319.2.1 χ hχ (i : ℕ) (j : ℕ) i.isLt j.isLt
  rcases Section7.theorem_7_8_a (Section12.typeIASet M K) M K RM
      MfullFam Mfam τM τM₁ ψ h76M hDadeAgreeM h78M with
    ⟨a, r, hdecomp⟩
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI
  have hhalf :
      K.relIndex M ≤ (Nat.card K - 1) / 2 :=
    section14_frobenius_relIndex_le_kernel_pred_half
      (L := M) (H := K)
      (Section12.odd_card_of_typeIDefinitionData M K hTypeI) hfrobM
  have hr_bound : Section5.cfNormSq r ≤ (K.relIndex M : ℝ) - 1 :=
    Section7.theorem_7_8_b_remainder_bound
      (Section12.typeIASet M K) M K RM MfullFam Mfam τM τM₁ ψ
      h76M hDadeAgreeM h78M hhalf a r hdecomp
  rcases hdecomp with ⟨_hpImg, _hrImg, _hrp, hβraw⟩
  have hβdecomp :
      τM βM =
        Section1.principalCharacter G - τM₁ ψ +
          ((a : ℂ) • Section7.theorem_7_8_weightedSum Mfam τM₁
            (K.relIndex M)) + r := by
    exact hβMτ_eq.trans hβraw
  have hweighted_orth : ∀ ij : Fin q × Fin p,
      Section1.scalarProduct G
        (Section7.theorem_7_8_weightedSum Mfam τM₁ (K.relIndex M))
        (σ (ω ij.1 ij.2)) = 0 := by
    intro ij
    dsimp [Section7.theorem_7_8_weightedSum]
    rw [section14_scalarProduct_finset_sum_left]
    refine Finset.sum_eq_zero ?_
    intro χ hχ
    rw [Section1.scalarProduct_smul_left]
    rw [hMfam_orth χ hχ ij.1 ij.2]
    simp
  let base : Fin q × Fin p := (i0, j0)
  let s : Finset (Fin q × Fin p) := (Finset.univ : Finset (Fin q × Fin p)).erase base
  have hprincipal_off : ∀ ij ∈ s,
      Section1.scalarProduct G (Section1.principalCharacter G)
        (σ (ω ij.1 ij.2)) = 0 := by
    intro ij hij
    have hij_ne : ij ≠ base := by
      simpa [s] using hij
    calc
      Section1.scalarProduct G (Section1.principalCharacter G)
          (σ (ω ij.1 ij.2)) =
        Section1.scalarProduct G (σ (Section1.principalCharacter W))
          (σ (ω ij.1 ij.2)) := by
          rw [hσprincipal]
      _ = Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω ij.1 ij.2)) := by
          rw [hω.principal]
      _ = Section1.scalarProduct W (ω i0 j0) (ω ij.1 ij.2) := by
          exact hσIso (ω i0 j0) (ω ij.1 ij.2)
            (hω.is_class i0 j0) (hω.is_class ij.1 ij.2)
      _ = 0 := by
          simpa [base, (Ne.symm hij_ne)] using hω.orthonormal base ij
  have hcoeff_r : ∀ ij ∈ s,
      (coeff ij.1 ij.2 : ℂ) =
        Section1.scalarProduct G r (σ (ω ij.1 ij.2)) := by
    intro ij hij
    have hmain :
        Section1.scalarProduct G (τM βM) (σ (ω ij.1 ij.2)) =
          Section1.scalarProduct G r (σ (ω ij.1 ij.2)) := by
      rw [hβdecomp]
      rw [Section1.scalarProduct_add_left]
      have hleft :
          Section1.scalarProduct G
            (Section1.principalCharacter G - τM₁ ψ +
              ((a : ℂ) • Section7.theorem_7_8_weightedSum Mfam τM₁
                (K.relIndex M)))
            (σ (ω ij.1 ij.2)) = 0 := by
        rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
          Section1.scalarProduct_smul_left]
        rw [hprincipal_off ij hij, hMfam_orth ψ hψmem ij.1 ij.2,
          hweighted_orth ij]
        simp
      rw [hleft]
      simp
    exact (hcoeffEq ij.1 ij.2).trans hmain
  have horth_sigma : ∀ x y : Fin q × Fin p,
      Section1.scalarProduct G (σ (ω x.1 x.2)) (σ (ω y.1 y.2)) =
        if x = y then 1 else 0 := by
    intro x y
    exact (hσIso (ω x.1 x.2) (ω y.1 y.2)
      (hω.is_class x.1 x.2) (hω.is_class y.1 y.2)).trans
        (hω.orthonormal x y)
  have htotal_le :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
        Section5.cfNormSq r := by
    have htotal_le' :
        (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij =>
              Complex.normSq
                (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
          Section5.cfNormSq r := by
      simpa using
        section14_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
          (fun ij : Fin q × Fin p => σ (ω ij.1 ij.2)) horth_sigma r
    have huniv :
        (Finset.univ : Finset (Fin q × Fin p)) =
          @Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p)) := by
      ext ij
      simp
    rw [huniv]
    exact htotal_le'
  have hsum_eq :
      s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
        s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := by
    refine Finset.sum_congr rfl ?_
    intro ij hij
    rw [hcoeff_r ij hij]
  have hsum_subset :
      s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
        (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ij hij
      simp
    · intro ij _hij _hnot
      exact Complex.normSq_nonneg _
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hr_bound_e : Section5.cfNormSq r ≤ ((e - 1 : ℕ) : ℝ) := by
    have hrel_one : 1 ≤ K.relIndex M := Nat.succ_le_of_lt hrel_pos
    calc
      Section5.cfNormSq r ≤ (K.relIndex M : ℝ) - 1 := hr_bound
      _ = ((K.relIndex M - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub hrel_one]
            norm_num
      _ = ((e - 1 : ℕ) : ℝ) := by
            simp [heq]
  calc
    (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
        (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
      s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
        rfl
    _ = s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := hsum_eq
    _ ≤ (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := hsum_subset
    _ ≤ Section5.cfNormSq r := htotal_le
    _ ≤ ((e - 1 : ℕ) : ℝ) := hr_bound_e

public theorem section14_theorem_14_11_2_off_base_bound_without_111_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U Vctx C D M K V : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (Mfam : Finset (Section1.ClassFunction M))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (_h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U Vctx C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        e = K.relIndex M →
          (Finset.univ.erase (i0, j0) :
              Finset (Fin q × Fin p)).sum
                (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
              ((e - 1 : ℕ) : ℝ) := by
  intro hctx h1410 heq
  classical
  letI : Fintype M := Fintype.ofFinite M
  have h1410_saved := h1410
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  rcases hσ with
    ⟨hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
  let MfullFam : Finset (Section1.ClassFunction M) :=
    insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM) (T := MfullFam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  have hβMτ_eq : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have hhyp13 :
      Section13.theorem_13_19_hypothesis M K Smax P W1 Mfam RM
        τS τM τM₁ ψ (τM₁ ψ) (μ 0 1) (τM βM)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (K.relIndex M) := by
    refine ⟨hMmax, hKMF, hTypeI, rfl, hDadeM, hPunctM, hExtM,
      hψmem, hψdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τM hβM
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U Vctx C D M K Sfam Tfam Mfam RM
    τS τT τM τM₁ ψ (τM βM)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
    (τM₁ ψ) ωNat ηNat μ ν μsum νsum δ δ' σ p q u v c d
    (K.relIndex M) hctx.1 hnotation hhyp13
  rcases hnotation with
    ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  have hMfam_orth :
      ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
        ∀ i : Fin q, ∀ j : Fin p,
          Section1.scalarProduct G (τM₁ χ) (σ (ω i j)) = 0 := by
    intro χ hχ i j
    have hωNat_eq : ωNat (i : ℕ) (j : ℕ) = ω i j :=
      hωNat_eq_ω (i : ℕ) (j : ℕ) i.isLt j.isLt
    have hησ : ηNat (i : ℕ) (j : ℕ) = σ (ω i j) := by
      rw [hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt, hωNat_eq]
    simpa [hησ] using h1319.2.1 χ hχ (i : ℕ) (j : ℕ) i.isLt j.isLt
  rcases Section7.theorem_7_8_a (Section12.typeIASet M K) M K RM
      MfullFam Mfam τM τM₁ ψ h76M hDadeAgreeM h78M with
    ⟨a, r, hdecomp⟩
  have hfrobM : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI
  have hhalf :
      K.relIndex M ≤ (Nat.card K - 1) / 2 :=
    section14_frobenius_relIndex_le_kernel_pred_half
      (L := M) (H := K)
      (Section12.odd_card_of_typeIDefinitionData M K hTypeI) hfrobM
  have hr_bound : Section5.cfNormSq r ≤ (K.relIndex M : ℝ) - 1 :=
    Section7.theorem_7_8_b_remainder_bound
      (Section12.typeIASet M K) M K RM MfullFam Mfam τM τM₁ ψ
      h76M hDadeAgreeM h78M hhalf a r hdecomp
  rcases hdecomp with ⟨_hpImg, _hrImg, _hrp, hβraw⟩
  have hβdecomp :
      τM βM =
        Section1.principalCharacter G - τM₁ ψ +
          ((a : ℂ) • Section7.theorem_7_8_weightedSum Mfam τM₁
            (K.relIndex M)) + r := by
    exact hβMτ_eq.trans hβraw
  have hweighted_orth : ∀ ij : Fin q × Fin p,
      Section1.scalarProduct G
        (Section7.theorem_7_8_weightedSum Mfam τM₁ (K.relIndex M))
        (σ (ω ij.1 ij.2)) = 0 := by
    intro ij
    dsimp [Section7.theorem_7_8_weightedSum]
    rw [section14_scalarProduct_finset_sum_left]
    refine Finset.sum_eq_zero ?_
    intro χ hχ
    rw [Section1.scalarProduct_smul_left]
    rw [hMfam_orth χ hχ ij.1 ij.2]
    simp
  let base : Fin q × Fin p := (i0, j0)
  let s : Finset (Fin q × Fin p) := (Finset.univ : Finset (Fin q × Fin p)).erase base
  have hprincipal_off : ∀ ij ∈ s,
      Section1.scalarProduct G (Section1.principalCharacter G)
        (σ (ω ij.1 ij.2)) = 0 := by
    intro ij hij
    have hij_ne : ij ≠ base := by
      simpa [s] using hij
    calc
      Section1.scalarProduct G (Section1.principalCharacter G)
          (σ (ω ij.1 ij.2)) =
        Section1.scalarProduct G (σ (Section1.principalCharacter W))
          (σ (ω ij.1 ij.2)) := by
          rw [hσprincipal]
      _ = Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω ij.1 ij.2)) := by
          rw [hω.principal]
      _ = Section1.scalarProduct W (ω i0 j0) (ω ij.1 ij.2) := by
          exact hσIso (ω i0 j0) (ω ij.1 ij.2)
            (hω.is_class i0 j0) (hω.is_class ij.1 ij.2)
      _ = 0 := by
          simpa [base, (Ne.symm hij_ne)] using hω.orthonormal base ij
  have hcoeff_r : ∀ ij ∈ s,
      (coeff ij.1 ij.2 : ℂ) =
        Section1.scalarProduct G r (σ (ω ij.1 ij.2)) := by
    intro ij hij
    have hmain :
        Section1.scalarProduct G (τM βM) (σ (ω ij.1 ij.2)) =
          Section1.scalarProduct G r (σ (ω ij.1 ij.2)) := by
      rw [hβdecomp]
      rw [Section1.scalarProduct_add_left]
      have hleft :
          Section1.scalarProduct G
            (Section1.principalCharacter G - τM₁ ψ +
              ((a : ℂ) • Section7.theorem_7_8_weightedSum Mfam τM₁
                (K.relIndex M)))
            (σ (ω ij.1 ij.2)) = 0 := by
        rw [Section1.scalarProduct_add_left, Section5.scalarProduct_sub_left,
          Section1.scalarProduct_smul_left]
        rw [hprincipal_off ij hij, hMfam_orth ψ hψmem ij.1 ij.2,
          hweighted_orth ij]
        simp
      rw [hleft]
      simp
    exact (hcoeffEq ij.1 ij.2).trans hmain
  have horth_sigma : ∀ x y : Fin q × Fin p,
      Section1.scalarProduct G (σ (ω x.1 x.2)) (σ (ω y.1 y.2)) =
        if x = y then 1 else 0 := by
    intro x y
    exact (hσIso (ω x.1 x.2) (ω y.1 y.2)
      (hω.is_class x.1 x.2) (hω.is_class y.1 y.2)).trans
        (hω.orthonormal x y)
  have htotal_le :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
        Section5.cfNormSq r := by
    have htotal_le' :
        (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij =>
              Complex.normSq
                (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
          Section5.cfNormSq r := by
      simpa using
        section14_finite_orthonormal_coeff_normSq_sum_le_cfNormSq
          (fun ij : Fin q × Fin p => σ (ω ij.1 ij.2)) horth_sigma r
    have huniv :
        (Finset.univ : Finset (Fin q × Fin p)) =
          @Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p)) := by
      ext ij
      simp
    rw [huniv]
    exact htotal_le'
  have hsum_eq :
      s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
        s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := by
    refine Finset.sum_congr rfl ?_
    intro ij hij
    rw [hcoeff_r ij hij]
  have hsum_subset :
      s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) ≤
        (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ij hij
      simp
    · intro ij _hij _hnot
      exact Complex.normSq_nonneg _
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hr_bound_e : Section5.cfNormSq r ≤ ((e - 1 : ℕ) : ℝ) := by
    have hrel_one : 1 ≤ K.relIndex M := Nat.succ_le_of_lt hrel_pos
    calc
      Section5.cfNormSq r ≤ (K.relIndex M : ℝ) - 1 := hr_bound
      _ = ((K.relIndex M - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub hrel_one]
            norm_num
      _ = ((e - 1 : ℕ) : ℝ) := by
            simp [heq]
  calc
    (Finset.univ.erase (i0, j0) : Finset (Fin q × Fin p)).sum
        (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
      s.sum (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
        rfl
    _ = s.sum (fun ij =>
          Complex.normSq
            (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := hsum_eq
    _ ≤ (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij =>
            Complex.normSq
              (Section1.scalarProduct G r (σ (ω ij.1 ij.2)))) := hsum_subset
    _ ≤ Section5.cfNormSq r := htotal_le
    _ ≤ ((e - 1 : ℕ) : ℝ) := hr_bound_e

public theorem section14_int_weighted_sigma_double_sum_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 : Subgroup G}
    {p q : ℕ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ω : Fin q → Fin p → Section1.ClassFunction W}
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (hωirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (ω i j))
    (coeff : Fin q → Fin p → ℤ) :
    Theory.Character.IsVirtualCharacter
      (∑ i : Fin q, ∑ j : Fin p,
        ((coeff i j : ℂ) • σ (ω i j))) := by
  classical
  refine Section12.isVirtualCharacter_finset_sum
    (G := G) (s := (Finset.univ : Finset (Fin q)))
    (Φ := fun i : Fin q =>
      ∑ j : Fin p, ((coeff i j : ℂ) • σ (ω i j))) ?_
  intro i _hi
  refine Section12.isVirtualCharacter_finset_sum
    (G := G) (s := (Finset.univ : Finset (Fin p)))
    (Φ := fun j : Fin p => ((coeff i j : ℂ) • σ (ω i j))) ?_
  intro j _hj
  have hbase : Theory.Character.IsVirtualCharacter (σ (ω i j)) :=
    hσ.2.1 (ω i j)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hωirr i j))
  rw [Int.cast_smul_eq_zsmul ℂ]
  exact Section12.isVirtualCharacter_zsmul (coeff i j) hbase

public theorem section14_scalarProduct_self_eq_of_virtual_cfNormSq_nat
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} {n : ℕ}
    (hχVirt : Theory.Character.IsVirtualCharacter χ)
    (hχNorm : Section5.cfNormSq χ = (n : ℝ)) :
    Section1.scalarProduct G χ χ = (n : ℂ) := by
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hχVirt hχVirt with
    ⟨z, hz⟩
  have hz_real : (z : ℝ) = (n : ℝ) := by
    unfold Section5.cfNormSq at hχNorm
    rw [hz] at hχNorm
    simpa using hχNorm
  have hz_nat : z = (n : ℤ) := by
    exact_mod_cast hz_real
  rw [hz, hz_nat]
  norm_num

public theorem section14_betaM_tau_self_scalar_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section1.scalarProduct G (τM βM) (τM βM) =
      (K.relIndex M : ℂ) + 1 := by
  classical
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  letI : Fintype M := Fintype.ofFinite M
  let MfullFam : Finset (Section1.ClassFunction M) :=
    insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM) (T := MfullFam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  have hβMτ_eq : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have hβNorm :
      Section5.cfNormSq (τM βM) =
        ((K.relIndex M + 1 : ℕ) : ℝ) := by
    rw [hβMτ_eq]
    have hnorm := Section7.theorem_7_8_beta_norm
      (A := Section12.typeIASet M K) (L := M) (H := K) (K := RM)
      (T := MfullFam) (S := Mfam) (τ := τM) (ν := τM₁) (ζ := ψ)
      h76M hDadeAgreeM h78M
    rw [hnorm]
    norm_num
  have hβVirt : Theory.Character.IsVirtualCharacter (τM βM) := by
    exact section14_betaM_tau_isVirtualCharacter_of_hypothesis_14_10
      (M := M) (K := K) (V := V) (Mfam := Mfam)
      (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM)
      ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, ⟨RM, hDadeM, _hSupportM⟩,
        hPunctM, _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  have hself :=
    section14_scalarProduct_self_eq_of_virtual_cfNormSq_nat
      (G := G) (χ := τM βM) (n := K.relIndex M + 1) hβVirt hβNorm
  norm_num at hself ⊢
  exact hself

public theorem section14_tauM1_psi_diff_conjugate_betaM_tau_scalar_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section1.scalarProduct G
        ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) (τM βM) =
      -1 := by
  classical
  rcases h1410 with
    ⟨hMmax, hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  letI : Fintype M := Fintype.ofFinite M
  let MfullFam : Finset (Section1.ClassFunction M) :=
    insert (Section7.principalInducedCharacter M K) Mfam
  have hMfullNotation :
      Section7.inducedFamilyNotation (K.subgroupOf M) MfullFam := by
    dsimp [MfullFam]
    simpa [Section7.principalInducedCharacter] using
      (section14_inducedFamilyNotation_insert_principal_of_punctured
        (H := K.subgroupOf M) (S := Mfam) hPunctM)
  have h76M :
      Section7.hypothesis_7_6_statement (Section12.typeIASet M K)
        M K RM MfullFam :=
    section14_hypothesis_7_6_typeI_typeIASet_of_dade
      (L := M) (H := K) (R := RM) (T := MfullFam) (τ := τM)
      hMmax hKMF hTypeI hDadeM hMfullNotation
  have h78M :
      Section7.theorem_7_8_hypothesis M K MfullFam Mfam τM τM₁ ψ := by
    dsimp [MfullFam]
    exact section14_theorem_7_8_hypothesis_of_typeI_punctured
      hKMF hTypeI hPunctM hExtM hψmem hψirr hψdeg
  have hDadeAgreeM :
      Section7.agreesWithDadeTransform (Section12.typeIASet M K) M RM τM := by
    rcases hDadeM with ⟨_h22, hτpack⟩
    rcases hτpack with ⟨hAMG, hτeq⟩
    exact ⟨hAMG, hτeq⟩
  have hβMτ_eq : τM βM = Section7.theorem_7_8_beta M K τM ψ := by
    simp [Section7.theorem_7_8_beta, hβM]
  have hKnormal : (K.subgroupOf M).Normal :=
    Section12.section16MFSubgroup_subgroupOf_normal hKMF
  have hψbar_mem : Section1.conjugateCharacter ψ ∈ Mfam :=
    Section12.puncturedInducedFamily_conjugate_mem M K Mfam hKnormal
      hPunctM ψ hψmem
  have hψ_ne_bar : ψ ≠ Section1.conjugateCharacter ψ :=
    Section12.puncturedInducedFamily_ne_conjugate M K Mfam hKnormal
      hModd hPunctM ψ hψmem
  rcases Section7.theorem_7_8_beta_zeta_coeff_int h76M hDadeAgreeM h78M with
    ⟨a, hβψ⟩
  have hψchar : Section1.IsCharacter ψ :=
    Section12.isCharacter_of_isIrreducibleCharacterOnGroup hψirr
  have hrel_ne : (K.relIndex M : ℂ) ≠ 0 := by
    haveI : (K.subgroupOf M).FiniteIndex := inferInstance
    have hrel : K.relIndex M ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := K.subgroupOf M))
    exact_mod_cast hrel
  have hψbar_one_div :
      Section1.conjugateCharacter ψ 1 / (K.relIndex M : ℂ) = 1 := by
    have hdegbar :
        Section1.degree (Section1.conjugateCharacter ψ) =
          (K.relIndex M : ℂ) := by
      rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hψchar, hψdeg]
    have hval : Section1.conjugateCharacter ψ 1 = (K.relIndex M : ℂ) := by
      simpa [Section1.degree_apply] using hdegbar
    rw [hval]
    field_simp [hrel_ne]
  have hβψbar :
      Section1.scalarProduct G (Section7.theorem_7_8_beta M K τM ψ)
          (τM₁ (Section1.conjugateCharacter ψ)) = (a : ℂ) := by
    have hraw :=
      Section7.theorem_7_8_beta_scalarProduct_of_mem
        h76M hDadeAgreeM h78M hβψ hψbar_mem
    have hne : Section1.conjugateCharacter ψ ≠ ψ := by
      intro h
      exact hψ_ne_bar h.symm
    rw [if_neg hne] at hraw
    simpa [hψbar_one_div] using hraw
  have hβdiff_right :
      Section1.scalarProduct G (τM βM)
          ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) = -1 := by
    calc
      Section1.scalarProduct G (τM βM)
          ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) =
          Section1.scalarProduct G (Section7.theorem_7_8_beta M K τM ψ)
            ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) := by
            rw [hβMτ_eq]
      _ = Section1.scalarProduct G (Section7.theorem_7_8_beta M K τM ψ)
            (τM₁ ψ) -
          Section1.scalarProduct G (Section7.theorem_7_8_beta M K τM ψ)
            (τM₁ (Section1.conjugateCharacter ψ)) := by
            rw [Section5.scalarProduct_sub_right]
      _ = ((a : ℂ) - 1) - (a : ℂ) := by
            rw [hβψ, hβψbar]
      _ = -1 := by ring
  have hswap :=
    Section1.scalarProduct_star_swap (G := G) (τM βM)
      ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ))
  have hstar :
      star (Section1.scalarProduct G
        ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) (τM βM)) = -1 :=
    hswap.trans hβdiff_right
  have h := congrArg star hstar
  simpa using h

public theorem section14_tauM1_conjugate_psi_of_hypothesis_14_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M K V : Subgroup G}
    {Mfam : Finset (Section1.ClassFunction M)}
    {τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ψ βM : Section1.ClassFunction M}
    (h1410 : hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM) :
    Section1.conjugateCharacter (τM₁ ψ) =
      τM₁ (Section1.conjugateCharacter ψ) := by
  classical
  rcases h1410 with
    ⟨hMmax, _hModd, _hNormVleM, hKMF, hTypeI, hDadePkg, hPunctM,
      _h52M, hExtM, hψmem, hψirr, hψdeg, hβM⟩
  rcases hDadePkg with ⟨RM, hDadeM, _hSupportM⟩
  have h12 :
      Section12.hypothesis_12_1_data M K Mfam RM τM :=
    ⟨hMmax, hKMF, hTypeI, hPunctM, hDadeM⟩
  rcases Section12.theorem_12_2_a M K Mfam RM τM h12 with
    ⟨SX, hdata⟩
  rcases Section12.theorem_12_2_b M K Mfam SX RM τM h12 hdata with
    ⟨_R1, R, _hRdata, h52R⟩
  have h52 : Section5.hypothesis_5_2_statement Mfam τM := by
    rcases h52R with ⟨hsetup, h52a, h52b, h52c, h52d, h52e⟩
    exact ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hcoh : Section6.coherentExtension Mfam τM τM₁ := by
    rcases hExtM with ⟨hIso, hVirt, hAgree⟩
    exact ⟨hIso, hVirt, hAgree⟩
  have hfrob : Section7.frobeniusWithKernel M K :=
    Section12.theorem_12_7 M K hMmax hKMF hTypeI
  have hIrr : ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
      Section1.IsIrreducibleCharacterOnGroup χ :=
    Section12.theorem_12_6_irreducible_of_frobenius M K Mfam RM τM h12 hfrob
  have hskew :
      Section1.conjugateCharacter
          (τM (ψ - Section1.conjugateCharacter ψ)) =
        -(τM (ψ - Section1.conjugateCharacter ψ)) :=
    Section12.conjugateCharacter_tau_sub_conjugate_of_hypothesis12
      M K Mfam SX RM τM h12 hdata hψmem
  exact
    section14_theorem_14_9_late_type_T1_tauT1_conjugate_source_bridge
      (Tmax := M) (T1T := Mfam) (τT := τM) (τT1 := τM₁)
      h52 hcoh hIrr hψmem hskew

public theorem section14_double_sum_eq_weightedFamilySum
    {G : Type u} [Group G] [Finite G]
    {W : Type v}
    {p q : ℕ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (coeff : Fin q → Fin p → ℤ) :
    (∑ i : Fin q, ∑ j : Fin p,
        ((coeff i j : ℂ) • σ (ω i j))) =
      Section1.weightedFamilySum
        (fun ij : Fin q × Fin p => (coeff ij.1 ij.2 : ℂ))
        (fun ij : Fin q × Fin p => σ (ω ij.1 ij.2)) := by
  classical
  ext g
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Section1.weightedFamilySum]
  have huniv :
      (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))) =
        (Finset.univ : Finset (Fin q)).product
          (Finset.univ : Finset (Fin p)) := by
    ext ij
    simp
  rw [huniv]
  simpa using
    (Finset.sum_product
      (s := (Finset.univ : Finset (Fin q)))
      (t := (Finset.univ : Finset (Fin p)))
      (f := fun ij : Fin q × Fin p =>
        (coeff ij.1 ij.2 : ℂ) * σ (ω ij.1 ij.2) g)).symm

public theorem section14_scalarProduct_weightedFamilySum_self_orthonormal_eq_sum_normSq
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0) :
    Section1.scalarProduct G (Section1.weightedFamilySum w χ)
        (Section1.weightedFamilySum w χ) =
      ((∑ i : ι, Complex.normSq (w i) : ℝ) : ℂ) := by
  classical
  have hself :
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
        ∑ i : ι, star (w i) * w i := by
    calc
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ)
          = ∑ i : ι, star (w i) *
              Section1.scalarProduct G (Section1.weightedFamilySum w χ) (χ i) := by
            simpa using
              Section1.scalarProduct_weightedFamilySum_right
                (Section1.weightedFamilySum w χ) w χ
      _ = ∑ i : ι, star (w i) * w i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i]
  rw [hself]
  trans ∑ i : ι, ((Complex.normSq (w i) : ℝ) : ℂ)
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [Complex.normSq_eq_conj_mul_self]
  · simp

public theorem section14_scalarProduct_right_weightedFamilySum_int_eq_sum_normSq
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Finite ι]
    (β : Section1.ClassFunction G)
    (χ : ι → Section1.ClassFunction G)
    (coeff : ι → ℤ)
    (hcoeff : ∀ i : ι,
      (coeff i : ℂ) = Section1.scalarProduct G β (χ i)) :
    Section1.scalarProduct G β
        (Section1.weightedFamilySum (fun i : ι => (coeff i : ℂ)) χ) =
      ((∑ i : ι, Complex.normSq (coeff i : ℂ) : ℝ) : ℂ) := by
  classical
  rw [Section1.scalarProduct_weightedFamilySum_right]
  trans ∑ i : ι, ((Complex.normSq (coeff i : ℂ) : ℝ) : ℂ)
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [← hcoeff i]
    simp
  · simp

public theorem section14_scalarProduct_left_weightedFamilySum_int_eq_sum_normSq
    {G : Type u} {ι : Type v} [Group G] [Finite G] [Finite ι]
    (β : Section1.ClassFunction G)
    (χ : ι → Section1.ClassFunction G)
    (coeff : ι → ℤ)
    (hcoeff : ∀ i : ι,
      (coeff i : ℂ) = Section1.scalarProduct G β (χ i)) :
    Section1.scalarProduct G
        (Section1.weightedFamilySum (fun i : ι => (coeff i : ℂ)) χ) β =
      ((∑ i : ι, Complex.normSq (coeff i : ℂ) : ℝ) : ℂ) := by
  classical
  have hright :=
    section14_scalarProduct_right_weightedFamilySum_int_eq_sum_normSq
      β χ coeff hcoeff
  calc
    Section1.scalarProduct G
        (Section1.weightedFamilySum (fun i : ι => (coeff i : ℂ)) χ) β =
        star (Section1.scalarProduct G β
          (Section1.weightedFamilySum (fun i : ι => (coeff i : ℂ)) χ)) := by
          exact (Section1.scalarProduct_star_swap (G := G)
            (Section1.weightedFamilySum (fun i : ι => (coeff i : ℂ)) χ) β).symm
    _ = star (((∑ i : ι, Complex.normSq (coeff i : ℂ) : ℝ) : ℂ)) := by
          rw [hright]
    _ = ((∑ i : ι, Complex.normSq (coeff i : ℂ) : ℝ) : ℂ) := by
          simp

public theorem section14_base_indices_eq_zero_of_characterNotation
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 : Subgroup G}
    {p q : ℕ}
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ω : Fin q → Fin p → Section1.ClassFunction W}
    {i0 : Fin q} {j0 : Fin p}
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω) :
    (i0 : ℕ) = 0 ∧ (j0 : ℕ) = 0 := by
  classical
  rcases hnotation.1 with ⟨_h31, hqpos, hppos, ωFin, hωFin, hωNat_eq_fin⟩
  let i00 : Fin q := ⟨0, hqpos⟩
  let j00 : Fin p := ⟨0, hppos⟩
  have hprincipal00 : ω i00 j00 = Section1.principalCharacter W := by
    calc
      ω i00 j00 = ωNat 0 0 := by
        exact (hωNat_eq_ω 0 0 hqpos hppos).symm
      _ = ωFin i00 j00 := hωNat_eq_fin 0 0 hqpos hppos
      _ = Section1.principalCharacter W := hωFin.principal
  have hpair : i0 = i00 ∧ j0 = j00 := by
    apply hω.pairwise_eq
    rw [hω.principal, hprincipal00]
  constructor
  · simpa [i00] using congrArg Fin.val hpair.1
  · simpa [j00] using congrArg Fin.val hpair.2

public theorem section14_coefficients_normSq_sum_eq_relIndex_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            theorem_14_11_1_data M K p q u v →
              e = K.relIndex M →
                (Finset.univ : Finset (Fin q × Fin p)).sum
                    (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
                  (e : ℝ) := by
  intro hctx h143 h1410 hKV h111 heq
  classical
  rcases section14_base_indices_eq_zero_of_characterNotation
      (hnotation := hnotation) (hωNat_eq_ω := hωNat_eq_ω) hω with
    ⟨hi0, hj0⟩
  have hsumOff :=
    section14_theorem_14_11_2_off_base_bound_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ coeff hcoeffEq
      hctx h143 h1410 hKV h111 heq
  have hsupportNonmem :
      ∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          ∀ g : G, g ∈ Section3.cyclicTISet W1 W2 W →
            g ∉ Section2.dadeSupport (Section12.typeIASet M K) R :=
    section14_theorem_14_11_2_cyclicTI_dadeSupport_nonmem_source_bridge
      Smax Tmax W W1 W2 P Q U V C D M K V Sfam Tfam τS τT
      Mfam τM τM₁ ψ βM p q u v c d σ hctx h1410 hnotation
  have hvanish :
      Section3.VanishesOn (τM βM) (Section3.cyclicTISet W1 W2 W) :=
    section14_betaM_tau_vanishesOn_cyclicTISet_of_dadeSupport_nonmem
      h1410 hsupportNonmem
  let β : Section1.ClassFunction G :=
    τM βM -
      ∑ p : Fin q × Fin p, ((coeff p.1 p.2 : ℂ) • σ (ω p.1 p.2))
  have hβMτClass : Section1.IsClassFunction (τM βM) :=
    section14_betaM_tau_isClassFunction_of_hypothesis_14_10 h1410
  have h36projection :
      let coeffC : Fin q → Fin p → ℂ := fun i j =>
        Section1.scalarProduct G (τM βM) (σ (ω i j))
      let βC : Section1.ClassFunction G :=
        τM βM - ∑ p : Fin q × Fin p,
          coeffC p.1 p.2 • σ (ω p.1 p.2)
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ω σ (τM βM) βC coeffC h31 hω :=
    section14_hypothesis_3_6_of_projection
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := τM βM)
      (h31 := h31) (hω := hω) hσ hβMτClass hvanish
  have h36 :
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ω σ (τM βM) β
        (fun i j => (coeff i j : ℂ)) h31 hω := by
    simpa [β, hcoeffEq] using h36projection
  rcases hnotation with
    ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  have hβprincipal :
      Section1.scalarProduct G (τM βM) (Section1.principalCharacter G) = 1 :=
    section14_betaM_tau_principal_scalar_of_hypothesis_14_10 h1410
  rcases hσ with
    ⟨_hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
  have hσ00 : σ (ω i0 j0) = Section1.principalCharacter G := by
    calc
      σ (ω i0 j0) = σ (Section1.principalCharacter W) := by
        rw [hω.principal]
      _ = Section1.principalCharacter G := hσprincipal
  have h00c : (coeff i0 j0 : ℂ) = 1 := by
    rw [hcoeffEq i0 j0, hσ00, hβprincipal]
  have hrowScalar :
      ∀ j : ℕ, 0 < j → j < p →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τM βM) (ηNat 0 j)) :=
    section14_theorem_14_11_2_row_odd_of_pf13_19_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (M := M) (K := K) (Sfam := Sfam) (Tfam := Tfam) (τS := τS)
      (τT := τT) (Mfam := Mfam) (τM := τM) (τM₁ := τM₁)
      (ψ := ψ) (βM := βM) (ωNat := ωNat) (ηNat := ηNat)
      (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) hctx h1410
      ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal,
        _hμind, _hνind, _hμsum, _hνsum⟩ h111
  have hrowc : ∀ j, j ≠ j0 →
      Section13.oddScalarProduct (coeff i0 j : ℂ) := by
    intro j hj
    have hj_ne_zero : (j : ℕ) ≠ 0 := by
      intro hjzero
      apply hj
      ext
      simpa [hj0] using hjzero
    have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj_ne_zero
    have hqpos : 0 < q := by
      simpa [hi0] using i0.isLt
    have hωNat_eq : ωNat 0 (j : ℕ) = ω i0 j := by
      have h := hωNat_eq_ω 0 (j : ℕ) hqpos j.isLt
      have hi0_fin : (⟨0, hqpos⟩ : Fin q) = i0 := by
        ext
        simp [hi0]
      simpa [hi0_fin] using h
    have hησ : ηNat 0 (j : ℕ) = σ (ω i0 j) := by
      rw [hηNat 0 (j : ℕ) hqpos j.isLt, hωNat_eq]
    have hcoeff :
        (coeff i0 j : ℂ) =
          Section1.scalarProduct G (τM βM) (ηNat 0 (j : ℕ)) := by
      rw [hcoeffEq i0 j, ← hησ]
    simpa [hcoeff] using hrowScalar (j : ℕ) hjpos j.isLt
  have hcolScalar :
      ∀ i : ℕ, 0 < i → i < q →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τM βM) (ηNat i 0)) :=
    section14_theorem_14_11_2_col_odd_of_pf13_19_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (M := M) (K := K) (Sfam := Sfam) (Tfam := Tfam) (τS := τS)
      (τT := τT) (Mfam := Mfam) (τM := τM) (τM₁ := τM₁)
      (ψ := ψ) (βM := βM) (ωNat := ωNat) (ηNat := ηNat)
      (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d)
      hctx h1410
      ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal,
        _hμind, _hνind, _hμsum, _hνsum⟩ h111
  have hcolc : ∀ i, i ≠ i0 →
      Section13.oddScalarProduct (coeff i j0 : ℂ) := by
    intro i hi
    have hi_ne_zero : (i : ℕ) ≠ 0 := by
      intro hizero
      apply hi
      ext
      simpa [hi0] using hizero
    have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi_ne_zero
    have hppos : 0 < p := by
      simpa [hj0] using j0.isLt
    have hωNat_eq : ωNat (i : ℕ) 0 = ω i j0 := by
      have h := hωNat_eq_ω (i : ℕ) 0 i.isLt hppos
      have hj0_fin : (⟨0, hppos⟩ : Fin p) = j0 := by
        ext
        simp [hj0]
      simpa [hj0_fin] using h
    have hησ : ηNat (i : ℕ) 0 = σ (ω i j0) := by
      rw [hηNat (i : ℕ) 0 i.isLt hppos, hωNat_eq]
    have hcoeff :
        (coeff i j0 : ℂ) =
          Section1.scalarProduct G (τM βM) (ηNat (i : ℕ) 0) := by
      rw [hcoeffEq i j0, ← hησ]
    simpa [hcoeff] using hcolScalar (i : ℕ) hipos i.isLt
  have h00 : coeff i0 j0 = 1 := by
    exact_mod_cast h00c
  have hrow : ∀ j, j ≠ j0 → Odd (coeff i0 j) := by
    intro j hj
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i0 j : ℂ)) rfl (hrowc j hj)
  have hcol : ∀ i, i ≠ i0 → Odd (coeff i j0) := by
    intro i hi
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i j0 : ℂ)) rfl (hcolc i hi)
  have hexchangec : ∀ i j, i ≠ i0 → j ≠ j0 →
      (coeff i j : ℂ) =
        (coeff i j0 : ℂ) + (coeff i0 j : ℂ) - (coeff i0 j0 : ℂ) := by
    intro i j hi hj
    exact Section3.proposition_3_7_particular
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := τM βM) (β := β)
      (a := fun i j => (coeff i j : ℂ)) h36 i j
  have hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0 := by
    intro i j hi hj
    exact section14_int_eq_of_complex_cast_eq (hexchangec i j hi hj)
  have hodd : ∀ i j, Odd (coeff i j) :=
    section14_odd_integer_coefficients_of_row_col_exchange
      i0 j0 coeff h00 hrow hcol hexchange
  have hlower : p * q - 1 ≤ e - 1 :=
    section14_coefficients_pred_lower_of_row_col_exchange
      i0 j0 coeff h00 hrow hcol hexchange hsumOff
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases section14_theorem_14_11_1_K_index_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨_h2q, _hKgt, hrel_le⟩
  have hupper : e ≤ p * q := by
    simpa [heq] using hrel_le
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hepos : 0 < e := by
    simpa [heq] using hrel_pos
  have hindex_eq_card : e = p * q :=
    section14_eq_mul_of_pred_bounds hepos hlower hupper
  have hcoeffSumLeCard :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        (Fintype.card (Fin q × Fin p) : ℝ) :=
    section14_coefficients_normSq_sum_le_card_of_off_base_bound
      i0 j0 coeff h00c hepos hupper hsumOff
  have hcardLeCoeffSum :
      (Fintype.card (Fin q × Fin p) : ℝ) ≤
        (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
    calc
      (Fintype.card (Fin q × Fin p) : ℝ) =
          (Finset.univ : Finset (Fin q × Fin p)).sum (fun _ij => (1 : ℝ)) := by
            simp
      _ ≤ (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) := by
            refine Finset.sum_le_sum ?_
            intro ij _hij
            exact section14_normSq_ge_one_of_odd_intCast
              (coeff ij.1 ij.2) (hodd ij.1 ij.2)
  have hsumEqCard :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
        (Fintype.card (Fin q × Fin p) : ℝ) :=
    le_antisymm hcoeffSumLeCard hcardLeCoeffSum
  have hcard : Fintype.card (Fin q × Fin p) = p * q := by
    simp [Fintype.card_prod, Nat.mul_comm]
  calc
    (Finset.univ : Finset (Fin q × Fin p)).sum
        (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) =
        (Fintype.card (Fin q × Fin p) : ℝ) := hsumEqCard
    _ = (e : ℝ) := by
        rw [hcard, ← hindex_eq_card]

public theorem section14_theorem_14_11_2_norm_one_remainder_self_diff_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (_h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        K ≠ V →
          theorem_14_11_1_data M K p q u v →
            e = K.relIndex M →
              Section1.scalarProduct G
                  ((∑ i : Fin q, ∑ j : Fin p,
                    ((coeff i j : ℂ) • σ (ω i j))) - τM βM)
                  ((∑ i : Fin q, ∑ j : Fin p,
                    ((coeff i j : ℂ) • σ (ω i j))) - τM βM) = 1 ∧
                Section1.scalarProduct G
                  ((τM₁ ψ) - Section1.conjugateCharacter (τM₁ ψ))
                  ((∑ i : Fin q, ∑ j : Fin p,
                    ((coeff i j : ℂ) • σ (ω i j))) - τM βM) = 1 := by
  intro hctx h143 h1410 hKV h111 heq
  classical
  let Sigma : Section1.ClassFunction G :=
    ∑ i : Fin q, ∑ j : Fin p,
      ((coeff i j : ℂ) • σ (ω i j))
  let sigmaFamily : Fin q × Fin p → Section1.ClassFunction G := fun ij =>
    σ (ω ij.1 ij.2)
  let coeffPair : Fin q × Fin p → ℤ := fun ij => coeff ij.1 ij.2
  have hSigmaWeighted :
      Sigma =
        Section1.weightedFamilySum
          (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily := by
    dsimp [Sigma, coeffPair, sigmaFamily]
    exact section14_double_sum_eq_weightedFamilySum
      (G := G) (W := W) σ ω coeff
  have horth : ∀ ij kl : Fin q × Fin p,
      Section1.scalarProduct G (sigmaFamily ij) (sigmaFamily kl) =
        if ij = kl then 1 else 0 := by
    intro ij kl
    exact
      (hσ.1 (ω ij.1 ij.2) (ω kl.1 kl.2)
        (hω.is_class ij.1 ij.2) (hω.is_class kl.1 kl.2)).trans
        (by simpa [sigmaFamily] using hω.orthonormal ij kl)
  have hcoeffSum :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
        (e : ℝ) := by
    dsimp [coeffPair]
    exact
      section14_coefficients_normSq_sum_eq_relIndex_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM p q u v c d e
        σ ω i0 j0 hnotation hωNat_eq_ω _h31 hω hσ coeff hcoeffEq
        hctx h143 h1410 hKV h111 heq
  have hcoeffSumFinite :
      (@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
          (fun ij => Complex.normSq (coeffPair ij : ℂ)) =
        (e : ℝ) := by
    have huniv :
        @Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p)) =
          (Finset.univ : Finset (Fin q × Fin p)) := by
      ext ij
      simp
    rw [huniv]
    exact hcoeffSum
  have hcoeffPairEq : ∀ ij : Fin q × Fin p,
      (coeffPair ij : ℂ) =
        Section1.scalarProduct G (τM βM) (sigmaFamily ij) := by
    intro ij
    dsimp [coeffPair, sigmaFamily]
    exact hcoeffEq ij.1 ij.2
  have hSigmaSelf : Section1.scalarProduct G Sigma Sigma = (e : ℂ) := by
    have hweighted :=
      section14_scalarProduct_weightedFamilySum_self_orthonormal_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p)
        (w := fun ij : Fin q × Fin p => (coeffPair ij : ℂ))
        (χ := sigmaFamily) horth
    calc
      Section1.scalarProduct G Sigma Sigma =
          Section1.scalarProduct G
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily)
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily) := by
            rw [hSigmaWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((e : ℝ) : ℂ) := by rw [hcoeffSumFinite]
      _ = (e : ℂ) := by norm_num
  have hBetaSigma : Section1.scalarProduct G (τM βM) Sigma = (e : ℂ) := by
    have hweighted :=
      section14_scalarProduct_right_weightedFamilySum_int_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p) (β := τM βM)
        (χ := sigmaFamily) (coeff := coeffPair) hcoeffPairEq
    calc
      Section1.scalarProduct G (τM βM) Sigma =
          Section1.scalarProduct G (τM βM)
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily) := by
            rw [hSigmaWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((e : ℝ) : ℂ) := by rw [hcoeffSumFinite]
      _ = (e : ℂ) := by norm_num
  have hSigmaBeta : Section1.scalarProduct G Sigma (τM βM) = (e : ℂ) := by
    have hweighted :=
      section14_scalarProduct_left_weightedFamilySum_int_eq_sum_normSq
        (G := G) (ι := Fin q × Fin p) (β := τM βM)
        (χ := sigmaFamily) (coeff := coeffPair) hcoeffPairEq
    calc
      Section1.scalarProduct G Sigma (τM βM) =
          Section1.scalarProduct G
            (Section1.weightedFamilySum
              (fun ij : Fin q × Fin p => (coeffPair ij : ℂ)) sigmaFamily)
            (τM βM) := by
            rw [hSigmaWeighted]
      _ = (((@Finset.univ (Fin q × Fin p) (Fintype.ofFinite (Fin q × Fin p))).sum
            (fun ij => Complex.normSq (coeffPair ij : ℂ)) : ℝ) : ℂ) :=
            by simpa using hweighted
      _ = ((e : ℝ) : ℂ) := by rw [hcoeffSumFinite]
      _ = (e : ℂ) := by norm_num
  constructor
  · have hMin : IsMinCE G := by
      rcases hctx.1 with
        ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
          _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
          _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
          _hChoice, hMin, _hFourSixS, _hFourSixT⟩
      exact hMin
    haveI : IsMinCE G := hMin
    have hBetaSelf :
        Section1.scalarProduct G (τM βM) (τM βM) = (e : ℂ) + 1 := by
      simpa [heq] using
        section14_betaM_tau_self_scalar_of_hypothesis_14_10
          (G := G) (M := M) (K := K) (V := V) (Mfam := Mfam)
          (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM) h1410
    change Section1.scalarProduct G (Sigma - τM βM) (Sigma - τM βM) = 1
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [hSigmaSelf, hSigmaBeta, hBetaSigma, hBetaSelf]
    ring
  ·
    -- `⟨τM₁ψ - (τM₁ψ)^*, χ⟩ = 1` using Dade isometry and coherent
    -- conjugation for the punctured induced family.
    change Section1.scalarProduct G
      ((τM₁ ψ) - Section1.conjugateCharacter (τM₁ ψ)) (Sigma - τM βM) = 1
    have hMin : IsMinCE G := by
      rcases hctx.1 with
        ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
          _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
          _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
          _hChoice, hMin, _hFourSixS, _hFourSixT⟩
      exact hMin
    haveI : IsMinCE G := hMin
    have h1410Saved := h1410
    rcases h1410 with
      ⟨_hMmax, _hModd, _hNormVleM, hKMF, _hTypeI, _hDadePkg, hPunctM,
        _h52M, _hExtM, hψmem, _hψirr, _hψdeg, _hβM⟩
    have hKnormal : (K.subgroupOf M).Normal :=
      Section12.section16MFSubgroup_subgroupOf_normal hKMF
    have hψbar_mem : Section1.conjugateCharacter ψ ∈ Mfam :=
      Section12.puncturedInducedFamily_conjugate_mem M K Mfam hKnormal
        hPunctM ψ hψmem
    have hMfam_orth :
        ∀ χ : Section1.ClassFunction M, χ ∈ Mfam →
          ∀ i : Fin q, ∀ j : Fin p,
            Section1.scalarProduct G (τM₁ χ) (σ (ω i j)) = 0 :=
      section14_tauM1_mfam_sigma_orthogonal_of_pf13_19_source
        (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
        (P := P) (Q := Q) (U := U) (Vctx := V) (V := V) (C := C) (D := D)
        (M := M) (K := K) (Sfam := Sfam) (Tfam := Tfam) (Mfam := Mfam)
        (τS := τS) (τT := τT) (τM := τM) (τM₁ := τM₁)
        (ψ := ψ) (βM := βM) (p := p) (q := q)
        (u := u) (v := v) (c := c) (d := d)
        (σ := σ) (ω := ω) (hnotation := hnotation)
        (hωNat_eq_ω := hωNat_eq_ω) hctx h1410Saved
    have hψSigma :
        Section1.scalarProduct G (τM₁ ψ) Sigma = 0 := by
      rw [hSigmaWeighted]
      rw [Section1.scalarProduct_weightedFamilySum_right]
      refine Finset.sum_eq_zero ?_
      intro ij _hij
      rw [hMfam_orth ψ hψmem ij.1 ij.2]
      simp
    have hψbarSigma :
        Section1.scalarProduct G
            (τM₁ (Section1.conjugateCharacter ψ)) Sigma = 0 := by
      rw [hSigmaWeighted]
      rw [Section1.scalarProduct_weightedFamilySum_right]
      refine Finset.sum_eq_zero ?_
      intro ij _hij
      rw [hMfam_orth (Section1.conjugateCharacter ψ) hψbar_mem ij.1 ij.2]
      simp
    have hDiffSigma :
        Section1.scalarProduct G
            ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) Sigma = 0 := by
      rw [Section5.scalarProduct_sub_left, hψSigma, hψbarSigma]
      ring
    have hConjTau :
        Section1.conjugateCharacter (τM₁ ψ) =
          τM₁ (Section1.conjugateCharacter ψ) :=
      section14_tauM1_conjugate_psi_of_hypothesis_14_10
        (M := M) (K := K) (V := V) (Mfam := Mfam)
        (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM) h1410Saved
    have hDiffBeta :
        Section1.scalarProduct G
          ((τM₁ ψ) - τM₁ (Section1.conjugateCharacter ψ)) (τM βM) = -1 :=
      section14_tauM1_psi_diff_conjugate_betaM_tau_scalar_of_hypothesis_14_10
        (M := M) (K := K) (V := V) (Mfam := Mfam)
        (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM) h1410Saved
    rw [hConjTau]
    rw [Section5.scalarProduct_sub_right, hDiffSigma, hDiffBeta]
    ring

public theorem section14_theorem_14_11_2_norm_one_remainder_norm_sign_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        K ≠ V →
          theorem_14_11_1_data M K p q u v →
            e = K.relIndex M →
              let χ : Section1.ClassFunction G :=
                (∑ i : Fin q, ∑ j : Fin p,
                  ((coeff i j : ℂ) • σ (ω i j))) - τM βM
              Section1.scalarProduct G χ χ = 1 ∧
                (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                  Section1.scalarProduct G χ
                    (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 hKV h111 heq
  let χ : Section1.ClassFunction G :=
    (∑ i : Fin q, ∑ j : Fin p,
      ((coeff i j : ℂ) • σ (ω i j))) - τM βM
  have hχSelfAndDiff :
      Section1.scalarProduct G χ χ = 1 ∧
        Section1.scalarProduct G
          ((τM₁ ψ) - Section1.conjugateCharacter (τM₁ ψ)) χ = 1 := by
    simpa [χ] using
      section14_theorem_14_11_2_norm_one_remainder_self_diff_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM p q u v c d e
        σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ coeff hcoeffEq
        hctx h143 h1410 hKV h111 heq
  have hSigmaVirt :
      Theory.Character.IsVirtualCharacter
        (∑ i : Fin q, ∑ j : Fin p,
          ((coeff i j : ℂ) • σ (ω i j))) :=
    section14_int_weighted_sigma_double_sum_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W) hσ
      (fun i j => hω.irreducible i j) coeff
  have hβVirt : Theory.Character.IsVirtualCharacter (τM βM) :=
    section14_betaM_tau_isVirtualCharacter_of_hypothesis_14_10 h1410
  have hχVirt : Theory.Character.IsVirtualCharacter χ := by
    dsimp [χ]
    exact Section3.isVirtualCharacter_sub hSigmaVirt hβVirt
  have hψSigned :
      Section3.IsSignedIrreducibleCharacter (τM₁ ψ) :=
    section14_psiTau_signedIrreducible_of_hypothesis_14_10
      (M := M) (K := K) (V := V) (Mfam := Mfam)
      (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM)
      h1410 rfl
  exact ⟨hχSelfAndDiff.1,
    section14_scalarProduct_sign_of_diff_scalar_eq_one
      hχVirt hχSelfAndDiff.1 hψSigned hχSelfAndDiff.2⟩

public theorem section14_theorem_14_11_2_norm_one_remainder_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        K ≠ V →
          theorem_14_11_1_data M K p q u v →
            e = K.relIndex M →
              ∃ χ : Section1.ClassFunction G,
                Theory.Character.IsVirtualCharacter χ ∧
                  Section1.scalarProduct G χ χ = 1 ∧
                  τM βM =
                    (∑ i : Fin q, ∑ j : Fin p,
                      ((coeff i j : ℂ) • σ (ω i j))) - χ ∧
                  (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                    Section1.scalarProduct G χ
                      (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 hKV h111 heq
  have _h31_use := h31
  let Sigma : Section1.ClassFunction G :=
    ∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • σ (ω i j))
  let χ : Section1.ClassFunction G := Sigma - τM βM
  have hnormSign :
      Section1.scalarProduct G χ χ = 1 ∧
        (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
          Section1.scalarProduct G χ
            (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
    simpa [χ, Sigma] using
      section14_theorem_14_11_2_norm_one_remainder_norm_sign_source_bridge
        Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
        M K V Mfam τM τM₁ ψ βM p q u v c d e
        σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ coeff hcoeffEq
        hctx h143 h1410 hKV h111 heq
  have hSigmaVirt : Theory.Character.IsVirtualCharacter Sigma := by
    dsimp [Sigma]
    exact section14_int_weighted_sigma_double_sum_isVirtualCharacter
      (W1 := W1) (W2 := W2) (W := W) hσ
      (fun i j => hω.irreducible i j) coeff
  have hβVirt : Theory.Character.IsVirtualCharacter (τM βM) :=
    section14_betaM_tau_isVirtualCharacter_of_hypothesis_14_10 h1410
  have hχVirt : Theory.Character.IsVirtualCharacter χ := by
    dsimp [χ]
    exact Section3.isVirtualCharacter_sub hSigmaVirt hβVirt
  refine ⟨χ, hχVirt, hnormSign.1, ?_, hnormSign.2⟩
  dsimp [χ, Sigma]
  ext g
  simp

public theorem section14_theorem_14_11_2_raw_source_inputs_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ)
    (coeff : Fin q → Fin p → ℤ)
    (hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j))) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
      hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        K ≠ V →
          theorem_14_11_1_data M K p q u v →
            e = K.relIndex M →
                (Finset.univ.erase (i0, j0) :
                    Finset (Fin q × Fin p)).sum
                      (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                    ((e - 1 : ℕ) : ℝ) ∧
                  ∃ χ : Section1.ClassFunction G,
                    Theory.Character.IsVirtualCharacter χ ∧
                      Section1.scalarProduct G χ χ = 1 ∧
                      τM βM =
                        (∑ i : Fin q, ∑ j : Fin p,
                          ((coeff i j : ℂ) • σ (ω i j))) - χ ∧
                      (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                        Section1.scalarProduct G χ
                          (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 hKV h111 heq
  have hsumOff :=
    section14_theorem_14_11_2_off_base_bound_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ coeff hcoeffEq
      hctx h143 h1410 hKV h111 heq
  rcases section14_theorem_14_11_2_norm_one_remainder_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ coeff hcoeffEq
      hctx h143 h1410 hKV h111 heq with
    ⟨χ, hχVirt, hχSelf, hβremSigma, hχψ⟩
  exact ⟨hsumOff, χ, hχVirt, hχSelf, hβremSigma, hχψ⟩

public theorem section14_theorem_14_11_2_raw_coefficients_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            theorem_14_11_1_data M K p q u v →
              e = K.relIndex M →
                ∃ coeff : Fin q → Fin p → ℤ,
                  ∃ β : Section1.ClassFunction G,
                        Section3.hypothesis_3_6_statement W1 W2 W
                        (Fin q) (Fin p) i0 j0 ω σ (τM βM) β
                        (fun i j => (coeff i j : ℂ)) h31 hω ∧
                        (Finset.univ.erase (i0, j0) :
                            Finset (Fin q × Fin p)).sum
                              (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                            ((e - 1 : ℕ) : ℝ) ∧
                          ∃ χ : Section1.ClassFunction G,
                            Theory.Character.IsVirtualCharacter χ ∧
                              Section1.scalarProduct G χ χ = 1 ∧
                              τM βM =
                                (∑ i : Fin q, ∑ j : Fin p,
                                  ((coeff i j : ℂ) • σ (ω i j))) - χ ∧
                              (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                                Section1.scalarProduct G χ
                                  (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 hKV h111 heq
  have hβVirt : Theory.Character.IsVirtualCharacter (τM βM) :=
    section14_betaM_tau_isVirtualCharacter_of_hypothesis_14_10 h1410
  have hσωVirt :
      ∀ i j, Theory.Character.IsVirtualCharacter (σ (ω i j)) := by
    intro i j
    exact hσ.2.1 (ω i j)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible i j))
  have hcoeffInt :
      ∀ i j, ∃ z : ℤ,
        Section1.scalarProduct G (τM βM) (σ (ω i j)) = (z : ℂ) := by
    intro i j
    exact Section3.scalarProduct_isVirtualCharacter_eq_int hβVirt
      (hσωVirt i j)
  let coeff : Fin q → Fin p → ℤ := fun i j =>
    Classical.choose (hcoeffInt i j)
  have hcoeffEq : ∀ i j,
      (coeff i j : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i j)) := by
    intro i j
    exact (Classical.choose_spec (hcoeffInt i j)).symm
  have hsupportNonmem :
      ∃ R : G → Subgroup G,
        Section12.dadeIsometryRelativeToTypeIASet M K R τM ∧
          ∀ g : G, g ∈ Section3.cyclicTISet W1 W2 W →
            g ∉ Section2.dadeSupport (Section12.typeIASet M K) R :=
    section14_theorem_14_11_2_cyclicTI_dadeSupport_nonmem_source_bridge
      Smax Tmax W W1 W2 P Q U V C D M K V Sfam Tfam τS τT
      Mfam τM τM₁ ψ βM p q u v c d σ hctx h1410 hnotation
  have hvanish :
      Section3.VanishesOn (τM βM) (Section3.cyclicTISet W1 W2 W) :=
    section14_betaM_tau_vanishesOn_cyclicTISet_of_dadeSupport_nonmem
      h1410 hsupportNonmem
  rcases section14_theorem_14_11_2_raw_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ
      coeff hcoeffEq
      hctx h143 h1410 hKV h111 heq with
    ⟨hsumOff, χ, hχVirt, hχSelf, hβremSigma, hχψ⟩
  let β : Section1.ClassFunction G :=
    τM βM -
      ∑ p : Fin q × Fin p, ((coeff p.1 p.2 : ℂ) • σ (ω p.1 p.2))
  have hβMτClass : Section1.IsClassFunction (τM βM) :=
    section14_betaM_tau_isClassFunction_of_hypothesis_14_10 h1410
  have h36projection :
      let coeffC : Fin q → Fin p → ℂ := fun i j =>
        Section1.scalarProduct G (τM βM) (σ (ω i j))
      let βC : Section1.ClassFunction G :=
        τM βM - ∑ p : Fin q × Fin p,
          coeffC p.1 p.2 • σ (ω p.1 p.2)
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ω σ (τM βM) βC coeffC h31 hω :=
    section14_hypothesis_3_6_of_projection
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := τM βM)
      (h31 := h31) (hω := hω) hσ hβMτClass hvanish
  have h36 :
      Section3.hypothesis_3_6_statement W1 W2 W
        (Fin q) (Fin p) i0 j0 ω σ (τM βM) β
        (fun i j => (coeff i j : ℂ)) h31 hω := by
    simpa [β, hcoeffEq] using h36projection
  exact ⟨coeff, β, h36, hsumOff, χ, hχVirt, hχSelf, hβremSigma, hχψ⟩

public theorem section14_theorem_14_11_2_pf36_coefficients_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    {ωNat : ℕ → ℕ → Section1.ClassFunction W}
    {ηNat : ℕ → ℕ → Section1.ClassFunction G}
    {μ : ℕ → ℕ → Section1.ClassFunction Smax}
    {ν : ℕ → ℕ → Section1.ClassFunction Tmax}
    {μsum : ℕ → Section1.ClassFunction Smax}
    {νsum : ℕ → Section1.ClassFunction Tmax}
    {δ δ' : ℕ → ℤ}
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (ω : Fin q → Fin p → Section1.ClassFunction W)
    (i0 : Fin q) (j0 : Fin p)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2
        p q ωNat ηNat μ ν μsum νsum δ δ' σ)
    (hωNat_eq_ω : ∀ i j, ∀ hi : i < q, ∀ hj : j < p,
      ωNat i j = ω ⟨i, hi⟩ ⟨j, hj⟩)
    (hi0 : (i0 : ℕ) = 0)
    (hj0 : (j0 : ℕ) = 0)
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W (Fin q) (Fin p) i0 j0 ω)
    (hσ : Section3.theorem_3_2_map_statement W1 W2 W σ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          K ≠ V →
            theorem_14_11_1_data M K p q u v →
              e = K.relIndex M →
                p * q - 1 ≤ e - 1 ∧
                  ∃ coeff : Fin q → Fin p → ℤ,
                    ∃ β : Section1.ClassFunction G,
                        Section3.hypothesis_3_6_statement W1 W2 W
                        (Fin q) (Fin p) i0 j0 ω σ (τM βM) β
                        (fun i j => (coeff i j : ℂ)) h31 hω ∧
                        (coeff i0 j0 : ℂ) = 1 ∧
                          (∀ j, j ≠ j0 →
                            Section13.oddScalarProduct (coeff i0 j : ℂ)) ∧
                          (∀ i, i ≠ i0 →
                            Section13.oddScalarProduct (coeff i j0 : ℂ)) ∧
                          (Finset.univ : Finset (Fin q × Fin p)).sum
                              (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                            (Fintype.card (Fin q × Fin p) : ℝ) ∧
                          ∃ χ : Section1.ClassFunction G,
                            Theory.Character.IsVirtualCharacter χ ∧
                              Section1.scalarProduct G χ χ = 1 ∧
                              τM βM =
                                (∑ i : Fin q, ∑ j : Fin p,
                                  ((coeff i j : ℂ) • σ (ω i j))) - χ ∧
                              (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                                Section1.scalarProduct G χ
                                  (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 hKV h111 heq
  rcases section14_theorem_14_11_2_raw_coefficients_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ω i0 j0 hnotation hωNat_eq_ω h31 hω hσ
      hctx h143 h1410 hKV h111 heq with
    ⟨coeff, β, h36, hsumOff,
      χ, hχVirt, hχSelf, hβremSigma, hχψ⟩
  rcases hnotation with
    ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩
  have hβprincipal :
      Section1.scalarProduct G (τM βM) (Section1.principalCharacter G) = 1 :=
    section14_betaM_tau_principal_scalar_of_hypothesis_14_10 h1410
  rcases hσ with
    ⟨_hσIso, _hσVirt, _hσInd, _hσClass, hσprincipal, _hσAgree, _hσVanish⟩
  have hσ00 : σ (ω i0 j0) = Section1.principalCharacter G := by
    calc
      σ (ω i0 j0) = σ (Section1.principalCharacter W) := by
        rw [hω.principal]
      _ = Section1.principalCharacter G := hσprincipal
  have hcoeff00 :
      (coeff i0 j0 : ℂ) =
        Section1.scalarProduct G (τM βM) (σ (ω i0 j0)) :=
    section14_pf36_coeff_eq_scalarProduct
      (W1 := W1) (W2 := W2) (W := W) (I := Fin q) (J := Fin p)
      (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
      (ψ := τM βM) (β := β) (a := fun i j => (coeff i j : ℂ))
      (h31 := h31) (hω := hω) h36 i0 j0
  have h00c : (coeff i0 j0 : ℂ) = 1 := by
    rw [hcoeff00, hσ00, hβprincipal]
  have hrowScalar :
      ∀ j : ℕ, 0 < j → j < p →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τM βM) (ηNat 0 j)) :=
    section14_theorem_14_11_2_row_odd_of_pf13_19_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (M := M) (K := K) (Sfam := Sfam) (Tfam := Tfam) (τS := τS)
      (τT := τT) (Mfam := Mfam) (τM := τM) (τM₁ := τM₁)
      (ψ := ψ) (βM := βM) (ωNat := ωNat) (ηNat := ηNat)
      (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d) hctx h1410
      ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩ h111
  have hrowc : ∀ j, j ≠ j0 →
      Section13.oddScalarProduct (coeff i0 j : ℂ) := by
    intro j hj
    have hj_ne_zero : (j : ℕ) ≠ 0 := by
      intro hjzero
      apply hj
      ext
      simpa [hj0] using hjzero
    have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj_ne_zero
    have hqpos : 0 < q := by
      simpa [hi0] using i0.isLt
    have hωNat_eq : ωNat 0 (j : ℕ) = ω i0 j := by
      have h := hωNat_eq_ω 0 (j : ℕ) hqpos j.isLt
      have hi0_fin : (⟨0, hqpos⟩ : Fin q) = i0 := by
        ext
        simp [hi0]
      simpa [hi0_fin] using h
    have hησ : ηNat 0 (j : ℕ) = σ (ω i0 j) := by
      rw [hηNat 0 (j : ℕ) hqpos j.isLt, hωNat_eq]
    have hcoeff :
        (coeff i0 j : ℂ) =
          Section1.scalarProduct G (τM βM) (ηNat 0 (j : ℕ)) := by
      rw [section14_pf36_coeff_eq_scalarProduct
        (W1 := W1) (W2 := W2) (W := W) (I := Fin q) (J := Fin p)
        (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
        (ψ := τM βM) (β := β) (a := fun i j => (coeff i j : ℂ))
        (h31 := h31) (hω := hω) h36 i0 j, ← hησ]
    simpa [hcoeff] using hrowScalar (j : ℕ) hjpos j.isLt
  have hcolScalar :
      ∀ i : ℕ, 0 < i → i < q →
        Section13.oddScalarProduct
          (Section1.scalarProduct G (τM βM) (ηNat i 0)) :=
    section14_theorem_14_11_2_col_odd_of_pf13_19_source
      (Smax := Smax) (Tmax := Tmax) (W := W) (W1 := W1) (W2 := W2)
      (P := P) (Q := Q) (U := U) (V := V) (C := C) (D := D)
      (M := M) (K := K) (Sfam := Sfam) (Tfam := Tfam) (τS := τS)
      (τT := τT) (Mfam := Mfam) (τM := τM) (τM₁ := τM₁)
      (ψ := ψ) (βM := βM) (ωNat := ωNat) (ηNat := ηNat)
      (μ := μ) (ν := ν) (μsum := μsum) (νsum := νsum)
      (δ := δ) (δ' := δ') (σ := σ) (p := p) (q := q)
      (u := u) (v := v) (c := c) (d := d)
      hctx h1410
      ⟨_hωNatData, _hσNotation, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind, _hμsum, _hνsum⟩ h111
  have hcolc : ∀ i, i ≠ i0 →
      Section13.oddScalarProduct (coeff i j0 : ℂ) := by
    intro i hi
    have hi_ne_zero : (i : ℕ) ≠ 0 := by
      intro hizero
      apply hi
      ext
      simpa [hi0] using hizero
    have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi_ne_zero
    have hppos : 0 < p := by
      simpa [hj0] using j0.isLt
    have hωNat_eq : ωNat (i : ℕ) 0 = ω i j0 := by
      have h := hωNat_eq_ω (i : ℕ) 0 i.isLt hppos
      have hj0_fin : (⟨0, hppos⟩ : Fin p) = j0 := by
        ext
        simp [hj0]
      simpa [hj0_fin] using h
    have hησ : ηNat (i : ℕ) 0 = σ (ω i j0) := by
      rw [hηNat (i : ℕ) 0 i.isLt hppos, hωNat_eq]
    have hcoeff :
        (coeff i j0 : ℂ) =
          Section1.scalarProduct G (τM βM) (ηNat (i : ℕ) 0) := by
      rw [section14_pf36_coeff_eq_scalarProduct
        (W1 := W1) (W2 := W2) (W := W) (I := Fin q) (J := Fin p)
        (i0 := i0) (j0 := j0) (ω := ω) (σ := σ)
        (ψ := τM βM) (β := β) (a := fun i j => (coeff i j : ℂ))
        (h31 := h31) (hω := hω) h36 i j0, ← hησ]
    simpa [hcoeff] using hcolScalar (i : ℕ) hipos i.isLt
  have h00 : coeff i0 j0 = 1 := by
    exact_mod_cast h00c
  have hrow : ∀ j, j ≠ j0 → Odd (coeff i0 j) := by
    intro j hj
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i0 j : ℂ)) rfl (hrowc j hj)
  have hcol : ∀ i, i ≠ i0 → Odd (coeff i j0) := by
    intro i hi
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i j0 : ℂ)) rfl (hcolc i hi)
  have hexchangec : ∀ i j, i ≠ i0 → j ≠ j0 →
      (coeff i j : ℂ) =
        (coeff i j0 : ℂ) + (coeff i0 j : ℂ) - (coeff i0 j0 : ℂ) := by
    intro i j hi hj
    exact Section3.proposition_3_7_particular
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σ) (ψ := τM βM) (β := β)
      (a := fun i j => (coeff i j : ℂ)) h36 i j
  have hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0 := by
    intro i j hi hj
    exact section14_int_eq_of_complex_cast_eq (hexchangec i j hi hj)
  have hlower : p * q - 1 ≤ e - 1 :=
    section14_coefficients_pred_lower_of_row_col_exchange
      i0 j0 coeff h00 hrow hcol hexchange hsumOff
  rcases hctx.1 with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, hMin, _hFourSixS, _hFourSixT⟩
  haveI : IsMinCE G := hMin
  rcases section14_theorem_14_11_1_K_index_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨_h2q, _hKgt, hrel_le⟩
  have hupper : e ≤ p * q := by
    simpa [heq] using hrel_le
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hepos : 0 < e := by
    simpa [heq] using hrel_pos
  have hcoeffSum :
      (Finset.univ : Finset (Fin q × Fin p)).sum
          (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
        (Fintype.card (Fin q × Fin p) : ℝ) :=
    section14_coefficients_normSq_sum_le_card_of_off_base_bound
      i0 j0 coeff h00c hepos hupper hsumOff
  exact ⟨hlower, coeff, β, h36, h00c, hrowc, hcolc, hcoeffSum,
    χ, hχVirt, hχSelf, hβremSigma, hχψ⟩

public theorem section14_theorem_14_11_2_complex_coefficients_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              theorem_14_11_1_data M K p q u v →
                e = K.relIndex M →
                  p * q - 1 ≤ e - 1 ∧
                    ∃ coeff : Fin q → Fin p → ℤ,
                      ∃ i0 : Fin q, ∃ j0 : Fin p,
                        (coeff i0 j0 : ℂ) = 1 ∧
                          (∀ j, j ≠ j0 →
                            Section13.oddScalarProduct (coeff i0 j : ℂ)) ∧
                          (∀ i, i ≠ i0 →
                            Section13.oddScalarProduct (coeff i j0 : ℂ)) ∧
                          (∀ i j, i ≠ i0 → j ≠ j0 →
                            (coeff i j : ℂ) =
                              (coeff i j0 : ℂ) + (coeff i0 j : ℂ) -
                                (coeff i0 j0 : ℂ)) ∧
                          (Finset.univ : Finset (Fin q × Fin p)).sum
                              (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                            (Fintype.card (Fin q × Fin p) : ℝ) ∧
                          ∃ χ : Section1.ClassFunction G,
                            Theory.Character.IsVirtualCharacter χ ∧
                              Section1.scalarProduct G χ χ = 1 ∧
                              τM βM =
                                (∑ i : Fin q, ∑ j : Fin p,
                                  ((coeff i j : ℂ) • η i j)) - χ ∧
                              (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                                Section1.scalarProduct G χ
                                  (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 heta hKV h111 heq
  rcases heta with
    ⟨ωNat, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hnotation, _hη⟩
  have hnotation_full := hnotation
  rcases hnotation with
    ⟨hωNat, hσ, hηNat, _hδ, _hδ', _hμirr, _hνirr, _hμzero_nonprincipal, _hνzero_nonprincipal,
      _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNat with ⟨h31, hqpos, hppos, ωFin, hωFin, hωeq⟩
  let i0 : Fin q := ⟨0, hqpos⟩
  let j0 : Fin p := ⟨0, hppos⟩
  have hησ : ∀ i j, η i j = σ (ωFin i j) := by
    intro i j
    calc
      η i j = ηNat (i : ℕ) (j : ℕ) := _hη i j
      _ = σ (ωNat (i : ℕ) (j : ℕ)) :=
        hηNat (i : ℕ) (j : ℕ) i.isLt j.isLt
      _ = σ (ωFin i j) := by
        simpa using congrArg σ (hωeq (i : ℕ) (j : ℕ) i.isLt j.isLt)
  rcases section14_theorem_14_11_2_pf36_coefficients_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e
      σ ωFin i0 j0 hnotation_full hωeq
      (by simp [i0]) (by simp [j0]) h31 (by simpa [i0, j0] using hωFin) hσ
      hctx h143 h1410 hKV h111 heq with
    ⟨hlower, coeff, β, h36, h00c, hrowc, hcolc, hcoeffSum,
      χ, hχVirt, hχSelf, hβremSigma, hχψ⟩
  have hexchangec : ∀ i j, i ≠ i0 → j ≠ j0 →
      (coeff i j : ℂ) =
        (coeff i j0 : ℂ) + (coeff i0 j : ℂ) - (coeff i0 j0 : ℂ) := by
    intro i j _hi _hj
    exact Section3.proposition_3_7_particular
      (W1 := W1) (W2 := W2) (W := W)
      (I := Fin q) (J := Fin p) (i0 := i0) (j0 := j0)
      (ω := ωFin) (σ := σ) (ψ := τM βM) (β := β)
      (a := fun i j => (coeff i j : ℂ)) h36 i j
  have hsum_eta_sigma :
      (∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • η i j)) =
        (∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • σ (ωFin i j))) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [hησ i j]
  have hβrem : τM βM =
      (∑ i : Fin q, ∑ j : Fin p, ((coeff i j : ℂ) • η i j)) - χ := by
    rw [hsum_eta_sigma]
    exact hβremSigma
  exact ⟨hlower, coeff, i0, j0, h00c, hrowc, hcolc, hexchangec, hcoeffSum,
    χ, hχVirt, hχSelf, hβrem, hχψ⟩

public theorem section14_theorem_14_11_2_coefficient_parity_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              theorem_14_11_1_data M K p q u v →
                e = K.relIndex M →
                  p * q - 1 ≤ e - 1 ∧
                    ∃ coeff : Fin q → Fin p → ℤ,
                      ∃ i0 : Fin q, ∃ j0 : Fin p,
                        coeff i0 j0 = 1 ∧
                          (∀ j, j ≠ j0 → Odd (coeff i0 j)) ∧
                          (∀ i, i ≠ i0 → Odd (coeff i j0)) ∧
                          (∀ i j, i ≠ i0 → j ≠ j0 →
                            coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0) ∧
                          (Finset.univ : Finset (Fin q × Fin p)).sum
                              (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                            (Fintype.card (Fin q × Fin p) : ℝ) ∧
                          ∃ χ : Section1.ClassFunction G,
                            Theory.Character.IsVirtualCharacter χ ∧
                              Section1.scalarProduct G χ χ = 1 ∧
                              τM βM =
                                (∑ i : Fin q, ∑ j : Fin p,
                                  ((coeff i j : ℂ) • η i j)) - χ ∧
                              (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                                Section1.scalarProduct G χ
                                  (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 heta hKV h111 heq
  rcases section14_theorem_14_11_2_complex_coefficients_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η
      hctx h143 h1410 heta hKV h111 heq with
    ⟨hlower, coeff, i0, j0, h00c, hrowc, hcolc, hexchangec, hcoeffSum,
      χ, hχVirt, hχSelf, hβrem, hχψ⟩
  have h00 : coeff i0 j0 = 1 := by
    exact_mod_cast h00c
  have hrow : ∀ j, j ≠ j0 → Odd (coeff i0 j) := by
    intro j hj
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i0 j : ℂ)) rfl (hrowc j hj)
  have hcol : ∀ i, i ≠ i0 → Odd (coeff i j0) := by
    intro i hi
    exact section14_odd_int_of_intCast_oddScalarProduct
      (z := (coeff i j0 : ℂ)) rfl (hcolc i hi)
  have hexchange : ∀ i j, i ≠ i0 → j ≠ j0 →
      coeff i j = coeff i j0 + coeff i0 j - coeff i0 j0 := by
    intro i j hi hj
    exact section14_int_eq_of_complex_cast_eq (hexchangec i j hi hj)
  exact ⟨hlower, coeff, i0, j0, h00, hrow, hcol, hexchange, hcoeffSum,
    χ, hχVirt, hχSelf, hβrem, hχψ⟩

public theorem section14_theorem_14_11_2_integer_coefficients_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              theorem_14_11_1_data M K p q u v →
                e = K.relIndex M →
                  p * q - 1 ≤ e - 1 ∧
                    ∃ coeff : Fin q → Fin p → ℤ,
                      (∀ i j, Odd (coeff i j)) ∧
                        (Finset.univ : Finset (Fin q × Fin p)).sum
                            (fun ij => Complex.normSq (coeff ij.1 ij.2 : ℂ)) ≤
                          (Fintype.card (Fin q × Fin p) : ℝ) ∧
                        ∃ χ : Section1.ClassFunction G,
                          Theory.Character.IsVirtualCharacter χ ∧
                            Section1.scalarProduct G χ χ = 1 ∧
                            τM βM =
                              (∑ i : Fin q, ∑ j : Fin p,
                                ((coeff i j : ℂ) • η i j)) - χ ∧
                            (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                              Section1.scalarProduct G χ
                                (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 heta hKV h111 heq
  rcases section14_theorem_14_11_2_coefficient_parity_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η
      hctx h143 h1410 heta hKV h111 heq with
    ⟨hlower, coeff, i0, j0, h00, hrow, hcol, hexchange, hcoeffSum,
      χ, hχVirt, hχSelf, hβrem, hχψ⟩
  have hcoeffOdd : ∀ i j, Odd (coeff i j) :=
    section14_odd_integer_coefficients_of_row_col_exchange
      i0 j0 coeff h00 hrow hcol hexchange
  exact ⟨hlower, coeff, hcoeffOdd, hcoeffSum, χ, hχVirt, hχSelf, hβrem, hχψ⟩

public theorem section14_theorem_14_11_2_remainder_core_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              theorem_14_11_1_data M K p q u v →
                e = K.relIndex M →
                  p * q - 1 ≤ e - 1 ∧
                  ∃ ε : Fin q → Fin p → ℤ,
                    (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
                      ∃ χ : Section1.ClassFunction G,
                        Theory.Character.IsVirtualCharacter χ ∧
                          Section1.scalarProduct G χ χ = 1 ∧
                          τM βM =
                            (∑ i : Fin q, ∑ j : Fin p,
                              ((ε i j : ℂ) • η i j)) - χ ∧
                          (Section1.scalarProduct G χ (τM₁ ψ) = 1 ∨
                            Section1.scalarProduct G χ
                              (Section1.conjugateCharacter (τM₁ ψ)) = -1) := by
  intro hctx h143 h1410 heta hKV h111 heq
  rcases section14_theorem_14_11_2_integer_coefficients_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η
      hctx h143 h1410 heta hKV h111 heq with
    ⟨hlower, coeff, hcoeffOdd, hcoeffSum, χ, hχVirt, hχSelf, hβrem, hχψ⟩
  have hcoeffSign : ∀ i j, coeff i j = 1 ∨ coeff i j = -1 :=
    section14_odd_integer_coefficients_sign_of_normSq_sum_le_card
      coeff hcoeffOdd hcoeffSum
  exact ⟨hlower, coeff, hcoeffSign, χ, hχVirt, hχSelf, hβrem, hχψ⟩

public theorem section14_theorem_14_11_2_remainder_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  theorem_14_11_1_data M K p q u v →
                    e = K.relIndex M →
                      p * q - 1 ≤ e - 1 ∧
                      ∃ ε : Fin q → Fin p → ℤ,
                        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
                          ∃ χ : Section1.ClassFunction G,
                            Theory.Character.IsVirtualCharacter χ ∧
                              Section1.scalarProduct G χ χ = 1 ∧
                              βMτ =
                                (∑ i : Fin q, ∑ j : Fin p,
                                  ((ε i j : ℂ) • η i j)) - χ ∧
                              (Section1.scalarProduct G χ ψτ = 1 ∨
                                Section1.scalarProduct G χ
                                  (Section1.conjugateCharacter ψτ) = -1) := by
  intro hctx h143 h1410 heta hKV hβMτ hψτ h111 heq
  rcases section14_theorem_14_11_2_remainder_core_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η
      hctx h143 h1410 heta hKV h111 heq with
    ⟨hle, ε, hε, χ, hχvirt, hχnorm, hβ, hχψ⟩
  refine ⟨hle, ε, hε, χ, hχvirt, hχnorm, ?_, ?_⟩
  · rw [hβMτ, hβ]
  · simpa [hψτ] using hχψ

public theorem section14_theorem_14_11_2_signed_expansion_source_bridge
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  theorem_14_11_1_data M K p q u v →
                    e = K.relIndex M →
                      p * q - 1 ≤ e - 1 ∧
                      ∃ ε : Fin q → Fin p → ℤ,
                        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
                          (βMτ =
                            (∑ i : Fin q, ∑ j : Fin p,
                              ((ε i j : ℂ) • η i j)) - ψτ ∨
                            βMτ =
                              (∑ i : Fin q, ∑ j : Fin p,
                                ((ε i j : ℂ) • η i j)) +
                                  Section1.conjugateCharacter ψτ) := by
  intro hctx h143 h1410 heta hKV hβMτ hψτ h111 heq
  have hψτSigned :
      Section3.IsSignedIrreducibleCharacter ψτ :=
    section14_psiTau_signedIrreducible_of_hypothesis_14_10
      (M := M) (K := K) (V := V) (Mfam := Mfam)
      (τM := τM) (τM₁ := τM₁) (ψ := ψ) (βM := βM)
      h1410 hψτ
  rcases section14_theorem_14_11_2_remainder_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
      hctx h143 h1410 heta hKV hβMτ hψτ h111 heq with
    ⟨hlower, ε, hεsign, χ, hχVirt, hχSelf, hβrem, hsp⟩
  have hχSigned : Section3.IsSignedIrreducibleCharacter χ :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hχVirt hχSelf
  exact ⟨hlower, ε, hεsign,
    section14_expansion_alternative_of_signed_remainder
      hχSigned hψτSigned hβrem hsp⟩

public theorem section14_theorem_14_11_2_source_inputs_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  theorem_14_11_1_data M K p q u v →
                    e = K.relIndex M →
                      p * q - 1 ≤ e - 1 ∧
                      e ≤ p * q ∧
                      ∃ ε : Fin q → Fin p → ℤ,
                        (∀ i j, ε i j = 1 ∨ ε i j = -1) ∧
                          (βMτ =
                            (∑ i : Fin q, ∑ j : Fin p,
                              ((ε i j : ℂ) • η i j)) - ψτ ∨
                            βMτ =
                              (∑ i : Fin q, ∑ j : Fin p,
                                ((ε i j : ℂ) • η i j)) +
                                  Section1.conjugateCharacter ψτ) := by
  intro hctx h143 h1410 heta hKV hβMτ hψτ h111 heq
  rcases section14_theorem_14_11_2_signed_expansion_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
      hctx h143 h1410 heta hKV hβMτ hψτ h111 heq with
    ⟨hlower, hexp⟩
  rcases section14_theorem_14_11_1_K_index_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K Mfam τM τM₁ ψ βM p q u v c d hctx h143 h1410 hKV with
    ⟨_h2q, _hKgt, hrel_le⟩
  have hupper : e ≤ p * q := by
    simpa [heq] using hrel_le
  exact ⟨hlower, hupper, hexp⟩

public theorem section14_theorem_14_11_2_with_14_11_1_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  theorem_14_11_1_data M K p q u v →
                    e = K.relIndex M →
                      theorem_14_11_2_data M K η βMτ ψτ e := by
  intro hctx h143 h1410 heta hKV hβMτ hψτ h111 heq
  rcases section14_theorem_14_11_2_source_inputs_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
      hctx h143 h1410 heta hKV hβMτ hψτ h111 heq with
    ⟨hlower, hupper, hexp⟩
  have hrel_pos : 0 < K.relIndex M := by
    have hne : (K.subgroupOf M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite (G := M) (H := K.subgroupOf M)
    exact Nat.pos_of_ne_zero (by simpa [Subgroup.relIndex] using hne)
  have hepos : 0 < e := by
    simpa [heq] using hrel_pos
  exact ⟨heq, section14_eq_mul_of_pred_bounds hepos hlower hupper, hexp⟩

public theorem section14_theorem_14_11_2_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U C D L H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (M K V : Subgroup G)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d e : ℕ)
    (η : Fin q → Fin p → Section1.ClassFunction G)
    (βMτ ψτ : Section1.ClassFunction G) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          section14EtaData Smax Tmax W W1 W2 p q η →
            K ≠ V →
              βMτ = τM βM →
                ψτ = τM₁ ψ →
                  e = K.relIndex M →
                    theorem_14_11_2_data M K η βMτ ψτ e := by
  intro hctx h143 h1410 heta hKV hβMτ hψτ heq
  have h111 : theorem_14_11_1_data M K p q u v :=
    section14_theorem_14_11_1_source_bridge
      Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
      M K V Mfam τM τM₁ ψ βM p q u v c d
      hctx h143 h1410 hKV
  exact section14_theorem_14_11_2_with_14_11_1_source_bridge
    Smax Tmax W W1 W2 P Q U C D L H Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL
    M K V Mfam τM τM₁ ψ βM p q u v c d e η βMτ ψτ
    hctx h143 h1410 heta hKV hβMτ hψτ h111 heq


end CFSG.Section14
