module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE8Gen
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UEig
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UComb
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGram
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4C3

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open Polynomial
open scoped Matrix

section Glue13

theorem tc_thirteen_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hc : orderOf ((2 : ZMod p) ^ f) = 4) : 13 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (2 : ZMod p) ^ f ≠ 0 := by
    refine pow_ne_zero _ fun h2 => hp2 ?_
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  have hdvd : orderOf ((2 : ZMod p) ^ f) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one hq0
  rw [hc] at hdvd
  by_contra hlt
  push Not at hlt
  have h1 := hp.two_le
  obtain ⟨k, hk⟩ := hdvd
  have h59 : p = 5 ∨ p = 9 := by omega
  rcases h59 with h | h
  · exact hp5 h
  · subst h
    norm_num at hp

theorem tc_dvd_two_pow_four_sub_one {p f : ℕ} (hp : p.Prime)
    (hc : orderOf ((2 : ZMod p) ^ f) = 4) : p ∣ (2 ^ (f * 2)) ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h4 : ((2 : ZMod p) ^ f) ^ 4 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one _
  have h1 : 1 ≤ (2 ^ (f * 2)) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_two_pow)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  have : (((2 ^ (f * 2)) ^ 2 : ℕ) : ZMod p) = ((2 : ZMod p) ^ f) ^ 4 := by
    push_cast
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [this, h4]
  simp

theorem exists_adjacent_of_two_le_finrank
    {Ψ : Set (Fin Tag.E8.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (h2 : 2 ≤ Module.finrank ℤ (Submodule.span ℤ Ψ)) :
    ∃ a ∈ Ψ, ∃ b ∈ Ψ, iform a b = -1 := by
  obtain ⟨α, hα, β, hβ, hβα, hβnα, hne⟩ := exists_pair_ne_of_two_le_finrank_span hΨ h2
  have hαα : iform α α = 2 := iform_self_eq_two_of_mem_e8 α (mem_rootFinset.2 (hΨ.isRoot α hα))
  have hββ : iform β β = 2 := iform_self_eq_two_of_mem_e8 β (mem_rootFinset.2 (hΨ.isRoot β hβ))
  have hb := abs_iform_le_one hαα hββ hβα hβnα
  rcases (by omega : iform α β = -1 ∨ iform α β = 1) with h | h
  · exact ⟨α, hα, β, hβ, h⟩
  · exact ⟨α, hα, -β, hΨ.neg_mem β hβ, by rw [iform_neg_right_eq_neg, h]⟩

end Glue13

section Rho

private theorem tc_cyclotomic_aeval_zero {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) {c : ℕ}
    (hcφ : Nat.totient c = 2) (hcp : ¬ p ∣ c) (hc0 : 0 < c) {q : ZMod p} (hq : orderOf q = c)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (hι : Fintype.card ι = 8)
    (R : Matrix ι ι ℤ) {N : ℕ} (hN : 0 < N) (hR : R ^ N = 1)
    (hdim : 4 ≤ Module.finrank (ZMod p)
      (Module.End.eigenspace (Matrix.mulVecLin ((R.map (Int.castRingHom (ZMod p)))ᵀ)) q)) :
    aeval R (cyclotomic c ℤ) = 0 := by
  classical
  have hdeg8 : R.charpoly.natDegree = 8 := by
    rw [Matrix.charpoly_natDegree_eq_dim, hι]
  obtain ⟨l, hl0, hl⟩ := exists_cyclotomic_list hN 8 R.charpoly (Matrix.charpoly_monic R) hdeg8
    (fun z hz => pow_eq_one_of_aeval_charpoly R hR z hz)
  have hdegl : (l.map Nat.totient).sum = 8 := by
    rw [← natDegree_prod_cyclotomic, ← hl, hdeg8]
  have hmodp : (R.map (Int.castRingHom (ZMod p))).charpoly =
      (l.map fun d => cyclotomic d (ZMod p)).prod := by
    rw [Matrix.charpoly_map, hl, Polynomial.map_list_prod]
    simp [List.map_map, Function.comp_def, map_cyclotomic]
  have hmult : 4 ≤ rootMultiplicity q (R.map (Int.castRingHom (ZMod p))).charpoly := by
    refine hdim.trans ?_
    have := LinearMap.finrank_eigenspace_le
      (Matrix.mulVecLin ((R.map (Int.castRingHom (ZMod p)))ᵀ)) q
    rwa [Matrix.charpoly_mulVecLin, Matrix.charpoly_transpose] at this
  rw [hmodp, rootMultiplicity_prod_cyclotomic hp7 hcφ hcp hq l hl0 (by omega)] at hmult
  have hdvd : cyclotomic c ℤ ^ 4 ∣ R.charpoly := by
    rw [hl]
    exact (pow_dvd_pow _ hmult).trans (pow_count_dvd_prod_cyclotomic c l)
  have hχ : R.charpoly = cyclotomic c ℤ ^ 4 := by
    refine eq_of_monic_of_dvd_of_natDegree_le ((cyclotomic.monic c ℤ).pow 4)
      (Matrix.charpoly_monic R) hdvd ?_
    rw [natDegree_pow, natDegree_cyclotomic, hcφ, hdeg8]
  set Rq : Matrix ι ι ℚ := R.map (Int.castRingHom ℚ) with hRq
  have hRqN : Rq ^ N = 1 := by
    have h := map_pow ((Int.castRingHom ℚ).mapMatrix : Matrix ι ι ℤ →+* _) R N
    rw [hR, map_one] at h
    exact h.symm
  have hm1 : minpoly ℚ Rq ∣ X ^ N - 1 :=
    minpoly.dvd ℚ Rq (by simp [hRqN, map_sub, map_pow, aeval_X])
  have hm2 : minpoly ℚ Rq ∣ cyclotomic c ℚ ^ 4 := by
    have := Matrix.minpoly_dvd_charpoly Rq
    rwa [hRq, Matrix.charpoly_map, hχ, Polynomial.map_pow, map_cyclotomic] at this
  have hirr : Irreducible (cyclotomic c ℚ) := cyclotomic.irreducible_rat hc0
  obtain ⟨i, hi4, hassoc⟩ := (dvd_prime_pow hirr.prime 4).1 hm2
  have hmin : minpoly ℚ Rq = cyclotomic c ℚ ^ i :=
    eq_of_monic_of_associated (minpoly.monic (Matrix.isIntegral Rq)) ((cyclotomic.monic c ℚ).pow i)
      hassoc
  have hi1 : i = 1 := by
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · exfalso
        have := minpoly.aeval ℚ Rq
        rw [hmin, pow_zero, map_one] at this
        exact one_ne_zero this
      · rfl
    · exfalso
      have hsq : Squarefree (X ^ N - 1 : ℚ[X]) := by
        have := (separable_X_pow_sub_C (1 : ℚ) (Nat.pos_iff_ne_zero.1 hN |> fun h => by
          exact_mod_cast h) one_ne_zero).squarefree
        simpa using this
      have hdv : cyclotomic c ℚ * cyclotomic c ℚ ∣ X ^ N - 1 := by
        have h2 : cyclotomic c ℚ ^ 2 ∣ cyclotomic c ℚ ^ i := pow_dvd_pow _ h
        rw [← hmin, sq] at h2
        exact h2.trans hm1
      exact hirr.not_isUnit (hsq _ hdv)
  have hphi : aeval Rq (cyclotomic c ℚ) = 0 := by
    have := minpoly.aeval ℚ Rq
    rwa [hmin, hi1, pow_one] at this
  have hphiZ : aeval Rq (cyclotomic c ℤ) = 0 := by
    have h1 : aeval Rq ((cyclotomic c ℤ).map (algebraMap ℤ ℚ)) = 0 := by
      rw [algebraMap_int_eq, map_cyclotomic_int]
      exact hphi
    rwa [aeval_map_algebraMap] at h1
  have hinj : Function.Injective (fun A : Matrix ι ι ℤ => A.map (Int.castRingHom ℚ)) :=
    Matrix.map_injective (RingHom.injective_int _)
  apply hinj
  have hmap : (aeval R (cyclotomic c ℤ)).map (Int.castRingHom ℚ) = aeval Rq (cyclotomic c ℤ) := by
    have := Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (Int.castRingHom ℚ).toIntAlgHom) R (cyclotomic c ℤ)
    exact this.symm
  beta_reduce
  rw [hmap, hphiZ]
  ext i j
  simp

private theorem tc_cyclotomic_four : cyclotomic 4 ℤ = (X : ℤ[X]) ^ 2 + 1 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at h
  rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at h
  rw [h]
  ring

theorem tc_rho_sq_neg_one_E8
    {K : Type} [Field K] [Finite K] [CharP K 2] {p₀ f p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hp7 : 7 ≤ p) (S : LangSetup .E8 (AlgebraicClosure K) p₀) (hq : S.D.q = 2 ^ f)
    (hc : orderOf ((2 : ZMod p) ^ f) = 4) {B₁ : Subgroup (ModGL .E8 (AlgebraicClosure K))}
    (hB₁T : B₁ ≤ S.D.torus) (hB₁el : CFSG.Open.IsElemAbelian p B₁) (hcard : p ^ 4 ≤ Nat.card B₁) :
    ∀ γ, S.ρ (S.ρ γ) = -γ := by
  classical
  have : NeZero Tag.E8.rank := ⟨by decide⟩
  have hdim := le_finrank_eigenspace_of_subgroup S hp2 hq hB₁T hB₁el hcard
  obtain ⟨N, hN, hRN⟩ := rhoMatrixOfSetup_pow_eq_one S
  have hι : Fintype.card (Fin Tag.E8.rank) = 8 := by
    rw [Fintype.card_fin]
    rfl
  have hcp : ¬ p ∣ 4 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hcyc := tc_cyclotomic_aeval_zero hp7 (by decide) hcp (by norm_num) hc hι
    (rhoMatrixOfSetup S) hN hRN hdim
  rw [tc_cyclotomic_four] at hcyc
  have h1 : rhoMatrixOfSetup S ^ 2 + 1 = 0 := by simpa using hcyc
  intro γ
  have h2 : (rhoMatrixOfSetup S ^ 2 + 1) *ᵥ γ = 0 := by rw [h1]; exact Matrix.zero_mulVec _
  have hR2 : (rhoMatrixOfSetup S ^ 2) *ᵥ γ = S.ρ (S.ρ γ) := by
    rw [pow_two, ← Matrix.mulVec_mulVec, rhoMatrixOfSetup_mulVec, rhoMatrixOfSetup_mulVec]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hR2] at h2
  exact eq_neg_of_add_eq_zero_left h2

end Rho

end CFSG.StandardType.TableCRes

end
