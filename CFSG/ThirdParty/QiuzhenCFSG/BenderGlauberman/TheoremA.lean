module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.MainTheoremInfra

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman Theorem A

The proof follows the paper's two cases.  When `|S| ≠ 4`, Lemma 2.5 and the
exceptional index-four use of Lemma 3.4 give the bounds.  When `|S| = 4`, the
principal `deltaNu` component is a four-term signed-irreducible sum and Lemma
2.2 identifies its reciprocal-degree sum with `2k² / |G:H|`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

/-- Theorem A: `1/3 < 2k²·|G:H|⁻¹ < 3`. -/
public theorem theorem_A {G : Type u} [Group G] [Finite G] (c : Hyp11 G) :
    (1 / 3 : ℚ) < (2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) ∧
      (2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) < 3 := by
  classical
  let h12 : Hyp12 c := hyp12_of_hyp11 c
  by_cases hS4 : Nat.card (↥(c.S : Subgroup G)) = 4
  · have hS4' : Section4Hyp c := hS4
    have hSC : Section3Hyp c := main_section3Hyp_of_section4 c hS4'
    rcases main_principal_delta_decomposition_of_section4 c h12 hSC hS4' with
      ⟨psi, hpsi, _horth, hdeltasum, _hpair, hpsit, hdegree⟩
    have hprincipalSum :
        scalarProduct G (1 : ClassFunction G) (∑ i, psi i) = 1 := by
      rw [← hdeltasum]
      exact main_delta_trivial_principal_pairing c h12
    rcases main_exists_principal_in_four_sum psi hpsi hprincipalSum with
      ⟨iPrincipal, hiPrincipal⟩
    choose n hn using hdegree
    have hnPrincipal : n iPrincipal = 1 := by
      have hcast : (n iPrincipal : ℂ) = 1 := by
        rw [(hn iPrincipal).1, hiPrincipal]
        simp
      exact_mod_cast hcast
    have hnne : ∀ i, n i ≠ -1 := by
      intro i
      exact main_signed_degree_ne_neg_one c hS4' (hpsi i) (hpsit i)
        (hn i).1 (hn i).2
    have hpsiSum : (∑ i, psi i 1) = 0 := by
      have hfun := congrFun hdeltasum (1 : G)
      rw [main_deltaNu_one_eq_zero c h12 (main_principalIrr c)] at hfun
      simpa using hfun.symm
    have hnSumC : (∑ i, (n i : ℂ)) = 0 := by
      calc
        (∑ i, (n i : ℂ)) = ∑ i, psi i 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hn i).1
        _ = 0 := hpsiSum
    have hnSum : ∑ i, n i = 0 := by exact_mod_cast hnSumC
    have hbounds := main_four_odd_reciprocal_bounds n
      (fun i => (hn i).2) hnne hnPrincipal hnSum
    have hExpand := main_four_reciprocal_sum c psi hpsi hdeltasum hpsit
    have hEquation := main_principal_delta_equation c h12
      (main_k1_eq_k2_of_section4 c hS4')
    rw [hExpand] at hEquation
    have hdegreeReciprocal : (∑ i, (psi i 1)⁻¹) =
        ∑ i, ((n i : ℤ) : ℂ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← (hn i).1]
    rw [hdegreeReciprocal] at hEquation
    have hratio := main_ratio_eq_reciprocal_sum c n hEquation
    rw [hratio]
    exact hbounds
  · have hm : 4 ≤ (c.U.subgroupOf c.H0).index :=
      main_H0_index_ge_four_of_S_ne_four c h12 hS4
    rcases main_exists_lambda_sq_ne_one c h12 hm with ⟨l3, hl3⟩
    let nu : Irr (↥c.H0) :=
      ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩
    have hnus : conjChar c.H0 (s_normalizes_H0 c h12) nu.1 ≠ nu.1 := by
      simpa [nu] using main_lambda_not_fixed_by_s c h12 hl3
    have hchi : IsPMIrr G (tildeNu c h12 nu) := by
      have hgen : IsGeneralizedCharacter (tildeNu c h12 nu) :=
        tildeNu_isGeneralized c h12 nu
      have hnorm : scalarProduct G (tildeNu c h12 nu) (tildeNu c h12 nu) = 1 := by
        have h := tildeNu_norm c h12 nu
        simp [hnus] at h
        simpa [normSq] using h
      rcases norm_one_signed_irreducible hgen hnorm with ⟨psi, hpsi, hcase⟩
      rcases hcase with hcase | hcase
      · exact Or.inl (by simpa [hcase] using hpsi)
      · exact Or.inr (by simpa [hcase] using hpsi)
    have hnuB : nu ∈ BOf c h12 (tildeNu c h12 nu) := by
      rw [BOf_mem_iff]
      have h := tildeNu_norm c h12 nu
      simp [hnus] at h
      have hself : scalarProduct G (tildeNu c h12 nu)
          (tildeNu c h12 nu) = 1 := by
        simpa [normSq] using h
      rw [hself]
      norm_num
    have horbit : (orbit c.H0 c.U nu.1).card =
        (c.U.subgroupOf c.H0).index := by
      apply main_linear_orbit_card c h12
      change IsLinearCharacter (fun x : ↥c.H0 => (l3.1 x : ℂ))
      exact isLinearCharacter_of_hom l3.1
    have hnut : tildeNu c h12 nu c.t = 2 * nu.1 (tH0 c) := by
      by_cases hfour : (orbit c.H0 c.U nu.1).card = 4
      · have hindex : (c.U.subgroupOf c.H0).index = 4 := by
          rw [← horbit]
          exact hfour
        have hSC : Section3Hyp c :=
          main_section3Hyp_of_H0_index_four c h12 hindex
        exact (lemma_3_4 c h12 hSC hchi hnuB hnus (Or.inr horbit)).2
      · exact tildeNu_at_t c h12 hnus (by
          intro hexception
          exact hfour hexception.1)
    have hnut' : tildeNu c h12
        ⟨LambdaChar l3.1, (isLinearCharacter_of_hom l3.1).1⟩ c.t =
          2 * (l3.1 (tH0 c) : ℂ) := by
      simpa [nu, LambdaChar] using hnut
    rcases lemma_2_5 c h12 hm hl3 hnut' with
      ⟨phi, _hphi, _hphiNe, _hphit, hlower, hmiddle, hupper⟩
    constructor
    · have hreal : (1 / 3 : ℝ) <
          ↑((2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) : ℚ) := by
        nlinarith
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa using hreal
    · have hreal :
          ↑((2 * (c.k : ℚ) ^ 2) / (c.H.index : ℚ) : ℚ) < (3 : ℝ) := by
        linarith
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa using hreal

end CFSG.BenderGlauberman
