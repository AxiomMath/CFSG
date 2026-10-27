module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Block
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

namespace OrthTorus

open Module CFSG.LieType.BorelTits Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] {c : D ≃ₗ[K] D} {p : ℕ}

theorem Rk1Block.exists_algebra_linearEquiv (hc : Rk1Block c p) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hpq : p ∣ Nat.card K + 1) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) :
    ∃ (_ : Algebra K K') (ψ : K' ≃ₗ[K] D) (ζ : K') (t : K), t ≠ 0 ∧
      (∀ x, ψ (ζ * x) = c (ψ x)) ∧
      (∀ x : K', ∃ a b : K, x = algebraMap K K' a + algebraMap K K' b * ζ) ∧
      ζ ^ 2 + algebraMap K K' t * ζ + 1 = 0 ∧
      unitaryInvolution K' 2 f ζ * ζ = 1 ∧
      ∀ a : K, unitaryInvolution K' 2 f (algebraMap K K' a) = algebraMap K K' a := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype K' := Fintype.ofFinite K'
  let t : K := LinearMap.trace K D (c : D →ₗ[K] D)
  have ht_def : t = LinearMap.trace K D (c : D →ₗ[K] D) := rfl
  have ht : t ≠ 0 := by rw [ht_def]; exact Rk1Block.trace_ne_zero hc
  let m : K[X] := X ^ 2 + C t * X + 1
  have hm_def : m = X ^ 2 + C t * X + 1 := rfl
  have hcc : ∀ x : D, c (c x) = t • c x + x := by
    intro x
    have hadd := congrArg (fun g : D →ₗ[K] D => g (c x)) (Rk1Block.add_inv hc)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at hadd
    have hcinv : ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) (c x) = x := by
      change c.symm (c x) = x
      exact c.symm_apply_apply x
    rw [hcinv] at hadd
    have hadd' : c (c x) + x = t • c x := by simpa [ht_def] using hadd
    have hxx : x + x = (0 : D) := by rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
    calc c (c x) = (c (c x) + x) + x := by rw [add_assoc, hxx, add_zero]
      _ = t • c x + x := by rw [hadd']
  have hc2p : (c : Module.End K D) ^ 2 + 1 = t • (c : Module.End K D) := by
    ext x
    simp only [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_eq_id,
      LinearMap.id_apply, LinearMap.smul_apply]
    rw [show (c : D →ₗ[K] D) ((c : D →ₗ[K] D) x) = t • (c : D →ₗ[K] D) x + x
        from hcc x,
      add_assoc,
      show x + x = (0 : D) by rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul],
      add_zero]
  have hc_aeval : aeval (c : Module.End K D) m = 0 := by
    rw [hm_def]
    simp only [map_add, map_mul, map_pow, map_one, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
    rw [show (c : Module.End K D) ^ 2 + t • (c : Module.End K D) + 1 =
        ((c : Module.End K D) ^ 2 + 1) + t • (c : Module.End K D) by abel,
      hc2p, ← two_smul K (t • (c : Module.End K D)), CharTwo.two_eq_zero, zero_smul]
  have hno : ∀ lam : K, ¬ m.IsRoot lam := by
    intro lam hlam
    rw [Polynomial.IsRoot] at hlam
    have hlameq : lam ^ 2 + t * lam + 1 = 0 := by simpa [hm_def] using hlam
    let lam' : K := t + lam
    have hlam'_def : lam' = t + lam := rfl
    clear_value lam'
    have hsum : lam + lam' = t := by
      rw [hlam'_def]
      calc lam + (t + lam) = (lam + lam) + t := by abel
        _ = t := by rw [CharTwo.add_self_eq_zero, zero_add]
    have hprod : lam * lam' = 1 := by
      have h : lam ^ 2 + t * lam = 1 := by
        have := congrArg (fun z : K => z + 1) hlameq
        simpa [add_assoc, CharTwo.add_self_eq_zero] using this
      rw [hlam'_def]
      calc lam * (t + lam) = lam * t + lam * lam := by rw [mul_add]
        _ = lam ^ 2 + t * lam := by ring
        _ = 1 := h
    have hlam'eq : lam' ^ 2 + t * lam' + 1 = 0 := by
      rw [← hsum, add_mul, hprod, ← pow_two]
      have h : lam' ^ 2 + (1 + lam' ^ 2) + 1 = (lam' ^ 2 + lam' ^ 2) + (1 + 1) := by abel
      rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have hprod_poly : (X - C lam) * (X - C lam') = m := by
      rw [hm_def]
      rw [show (X - C lam : K[X]) = X + C lam by rw [sub_eq_add_neg, CharTwo.neg_eq],
        show (X - C lam' : K[X]) = X + C lam' by rw [sub_eq_add_neg, CharTwo.neg_eq]]
      calc (X + C lam) * (X + C lam')
          = X ^ 2 + (C lam + C lam') * X + C lam * C lam' := by ring
        _ = X ^ 2 + C (lam + lam') * X + C (lam * lam') := by rw [map_add, map_mul]
        _ = X ^ 2 + C t * X + 1 := by rw [hsum, hprod, map_one]
    have hfac : aeval (c : Module.End K D) (X - C lam) *
        aeval (c : Module.End K D) (X - C lam') = 0 := by
      have h := hc_aeval
      rw [← hprod_poly, map_mul] at h
      exact h
    let f : Module.End K D := aeval (c : Module.End K D) (X - C lam)
    let g : Module.End K D := aeval (c : Module.End K D) (X - C lam')
    have hf0 : f = (c : Module.End K D) - lam • 1 := by
      simp only [f, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]
    have hg0 : g = (c : Module.End K D) - lam' • 1 := by
      simp only [g, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]
    have hfg : f * g = 0 := by simpa only [← hf0, ← hg0] using hfac
    haveI : Nontrivial D := Module.nontrivial_of_finrank_pos (by rw [hc.finrank_eq]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have heigen : ∃ u : D, u ≠ 0 ∧ ∃ μ : K, μ ^ 2 + t * μ + 1 = 0 ∧ c u = μ • u := by
      by_cases hy : g x = 0
      · refine ⟨x, hx, lam', hlam'eq, ?_⟩
        rw [hg0] at hy
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_eq_id,
          LinearMap.id_apply] at hy
        exact sub_eq_zero.mp hy
      · refine ⟨g x, hy, lam, hlameq, ?_⟩
        have hx0 : (f * g) x = 0 := by rw [hfg, LinearMap.zero_apply]
        rw [Module.End.mul_apply, hf0, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_eq_id, LinearMap.id_apply] at hx0
        exact sub_eq_zero.mp hx0
    obtain ⟨u, hu, μ, hμroot, heig⟩ := heigen
    have hμne : μ ≠ 0 := by
      intro h
      have h1 : (1 : K) = 0 := by simpa [h] using hμroot
      exact one_ne_zero h1
    have hμpow : μ ^ p = 1 := by
      have hcp : ((c ^ p : D ≃ₗ[K] D) : D → D) u = u := by rw [hc.pow_eq]; rfl
      have hpow : ∀ n : ℕ, ((c ^ n : D ≃ₗ[K] D) : D → D) u = μ ^ n • u := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, heig, smul_smul,
            ← pow_succ]
      rw [hpow p] at hcp
      have h : (μ ^ p - 1) • u = 0 := by rw [sub_smul, hcp, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hu)
    have hcop : Nat.Coprime p (Nat.card K - 1) := by
      rw [hc.prime.coprime_iff_not_dvd]
      intro hdiv
      have hq1 : 0 < Nat.card K := by rw [hf]; positivity
      have hd : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hdiv
      have heq : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
      rw [heq] at hd
      exact hc.ne_two ((Nat.prime_dvd_prime_iff_eq hc.prime Nat.prime_two).mp hd)
    have hμcard : μ ^ (Nat.card K - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one μ hμne
    have hμ1 : μ = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hμpow, hμcard⟩
    exact hu (hc.fix u (by rw [heig, hμ1, one_smul]))
  have hm_nat : m.natDegree = 2 := by
    have hlt2 : (C t * X : K[X]).natDegree < (X ^ 2 : K[X]).natDegree := by
      calc (C t * X : K[X]).natDegree = (C t * X ^ 1 : K[X]).natDegree := by rw [pow_one]
        _ ≤ 1 := natDegree_C_mul_X_pow_le t 1
        _ < 2 := by norm_num
        _ = (X ^ 2 : K[X]).natDegree := by rw [natDegree_X_pow]
    have h1 : (X ^ 2 + C t * X : K[X]).natDegree = 2 := by
      rw [natDegree_add_eq_left_of_natDegree_lt hlt2, natDegree_X_pow]
    have hlt1 : (1 : K[X]).natDegree < (X ^ 2 + C t * X : K[X]).natDegree := by
      rw [h1]; simp
    have hpq' : (X ^ 2 + C t * X + 1 : K[X]).natDegree =
        (X ^ 2 + C t * X : K[X]).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt hlt1
    rw [hm_def, hpq', h1]
  have hm_ne : m ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hm_nat
    exact two_ne_zero hm_nat.symm
  have hm_irr : Irreducible m :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hm_nat]; norm_num) hno
  haveI : Fact (Irreducible m) := ⟨hm_irr⟩
  let pb₀ : PowerBasis K (AdjoinRoot m) := AdjoinRoot.powerBasis hm_ne
  haveI : Module.Finite K (AdjoinRoot m) := pb₀.finite
  have hA_dim : Module.finrank K (AdjoinRoot m) = 2 := by
    rw [pb₀.finrank, show pb₀.dim = m.natDegree from rfl, hm_nat]
  have hA_card : Nat.card (AdjoinRoot m) = Nat.card K' := by
    rw [Module.natCard_eq_pow_finrank (K := K), hA_dim, hf, hK']
  haveI : Fintype (AdjoinRoot m) :=
    Fintype.ofEquiv (Fin pb₀.dim → K) pb₀.basis.equivFun.toEquiv.symm
  have hcardA : Fintype.card (AdjoinRoot m) = Fintype.card K' := by
    rw [Fintype.card_eq_nat_card, hA_card, Fintype.card_eq_nat_card]
  let e : AdjoinRoot m ≃+* K' := FiniteField.ringEquivOfCardEq hcardA
  let alg : Algebra K K' :=
    (e.toRingHom.comp (algebraMap K (AdjoinRoot m))).toAlgebra
  letI : Algebra K K' := alg
  have he_alg : ∀ a : K, e (algebraMap K (AdjoinRoot m) a) = algebraMap K K' a :=
    fun _ => rfl
  let eA : AdjoinRoot m ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := e) he_alg
  let ζ : K' := e (AdjoinRoot.root m)
  let pb : PowerBasis K K' := pb₀.map eA
  have hpb_dim : pb.dim = 2 := by
    rw [show pb.dim = pb₀.dim from PowerBasis.map_dim pb₀ eA,
      show pb₀.dim = m.natDegree from rfl, hm_nat]
  have hpb_gen : pb.gen = ζ := by
    rw [show pb.gen = eA pb₀.gen from PowerBasis.map_gen pb₀ eA,
      show pb₀.gen = AdjoinRoot.root m from rfl]
    rfl
  haveI : NeZero pb.dim := ⟨by rw [hpb_dim]; norm_num⟩
  let b' : Basis (Fin 2) K K' := pb.basis.reindex (finCongr hpb_dim)
  have hb'0 : b' 0 = 1 := by
    dsimp only [b']
    rw [Module.Basis.reindex_apply]
    have h0 : (finCongr hpb_dim).symm (0 : Fin 2) = 0 := Fin.ext rfl
    rw [h0, pb.basis_eq_pow]
    simp [hpb_gen]
  have hb'1 : b' 1 = ζ := by
    dsimp only [b']
    rw [Module.Basis.reindex_apply]
    have h1 : (finCongr hpb_dim).symm (1 : Fin 2) = 1 := by
      apply Fin.ext
      rw [finCongr_symm, finCongr_apply_coe]
      exact (Nat.mod_eq_of_lt (by rw [hpb_dim]; norm_num)).symm
    rw [h1, pb.basis_eq_pow]
    have hone : ((1 : Fin pb.dim) : ℕ) = 1 :=
      Nat.mod_eq_of_lt (by rw [hpb_dim]; norm_num)
    rw [hone, pow_one, hpb_gen]
  obtain ⟨d₀, hd₀⟩ := hc.exists_linearIndependent
  let b : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank hd₀ (by simp [hc.finrank_eq])
  have hb0 : b 0 = d₀ := by simp [b]
  have hb1 : b 1 = c d₀ := by simp [b]
  let ψ : K' ≃ₗ[K] D := b'.equiv b (Equiv.refl (Fin 2))
  have hψ1 : ψ 1 = d₀ := by
    rw [← hb'0]
    simp only [ψ, Module.Basis.equiv_apply, Equiv.refl_apply, hb0]
  have hψζ : ψ ζ = c d₀ := by
    rw [← hb'1]
    simp only [ψ, Module.Basis.equiv_apply, Equiv.refl_apply, hb1]
  have hζroot : ζ ^ 2 + algebraMap K K' t * ζ + 1 = 0 := by
    have hroot : aeval (AdjoinRoot.root m) m = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have haeval_root : aeval (AdjoinRoot.root m) m =
        (AdjoinRoot.root m) ^ 2 + algebraMap K (AdjoinRoot m) t * AdjoinRoot.root m + 1 := by
      change aeval (AdjoinRoot.root m) (X ^ 2 + C t * X + 1) =
        (AdjoinRoot.root m) ^ 2 + algebraMap K (AdjoinRoot m) t * AdjoinRoot.root m + 1
      rw [Polynomial.aeval_def]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
    rw [haeval_root] at hroot
    have h := congrArg e hroot
    simpa only [ζ, map_add, map_mul, map_pow, map_one, map_zero, he_alg] using h
  have hζsq : ζ * ζ = t • ζ + 1 := by
    have h := hζroot
    rw [← Algebra.smul_def t ζ] at h
    have h1 : ζ ^ 2 + t • ζ = 1 := by
      have := congrArg (fun z : K' => z + 1) h
      simpa [add_assoc, CharTwo.add_self_eq_zero] using this
    have h2 : ζ ^ 2 = t • ζ + 1 := by
      have hxx : t • ζ + t • ζ = (0 : K') := by
        rw [← two_smul K' (t • ζ), CharTwo.two_eq_zero, zero_smul]
      calc ζ ^ 2 = (ζ ^ 2 + t • ζ) + t • ζ := by rw [add_assoc, hxx, add_zero]
        _ = 1 + t • ζ := by rw [h1]
        _ = t • ζ + 1 := by rw [add_comm]
    rw [← pow_two, h2]
  have hψmul : ∀ x, ψ (ζ * x) = c (ψ x) := by
    have hf : (ψ.toLinearMap.comp (LinearMap.mulLeft K ζ)) =
        (c.toLinearMap.comp ψ.toLinearMap) := by
      apply b'.ext
      intro i
      fin_cases i
      · simp only [Fin.reduceFinMk, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        change ψ (ζ * b' 0) = c (ψ (b' 0))
        rw [hb'0, mul_one, hψζ, hψ1]
      · simp only [Fin.reduceFinMk, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        change ψ (ζ * b' 1) = c (ψ (b' 1))
        rw [hb'1, hζsq, hψζ, hcc d₀]
        simp only [map_add, map_smul, hψζ, hψ1]
    intro x
    exact congrArg (fun g : K' →ₗ[K] D => g x) hf
  have hspan : ∀ x : K', ∃ a b : K, x = algebraMap K K' a + algebraMap K K' b * ζ := by
    intro x
    refine ⟨b'.repr x 0, b'.repr x 1, ?_⟩
    have hsum := b'.sum_repr x
    rw [Fin.sum_univ_two] at hsum
    rw [hb'0, hb'1] at hsum
    conv_lhs => rw [← hsum]
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  have hζpow : ζ ^ p = 1 := by
    have hpow : ∀ n : ℕ, ψ (ζ ^ n * 1) = ((c ^ n : D ≃ₗ[K] D) : D → D) (ψ 1) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_assoc, hψmul, ih, pow_succ', LinearEquiv.mul_apply]
    have h := hpow p
    rw [mul_one, hc.pow_eq] at h
    exact ψ.injective (by simpa using h)
  have hnorm : unitaryInvolution K' 2 f ζ * ζ = 1 := by
    rw [unitaryInvolution_apply]
    have hpow : ζ ^ (2 ^ f + 1) = 1 := by
      obtain ⟨s, hs⟩ := hpq
      have hs' : 2 ^ f + 1 = p * s := by rw [← hf]; exact hs
      rw [hs', pow_mul, hζpow, one_pow]
    rw [← pow_succ]
    exact hpow
  have hfix : ∀ a : K, unitaryInvolution K' 2 f (algebraMap K K' a) = algebraMap K K' a := by
    intro a
    rw [unitaryInvolution_apply]
    have ha : a ^ (2 ^ f) = a := by
      rw [← hf, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card a
    have h1 : algebraMap K K' a = e (algebraMap K (AdjoinRoot m) a) := rfl
    have h2 : (algebraMap K K' a) ^ 2 ^ f = e ((algebraMap K (AdjoinRoot m) a) ^ 2 ^ f) := by
      rw [h1, map_pow]
    rw [h2, ← map_pow (algebraMap K (AdjoinRoot m)) a (2 ^ f), ha]
    exact h1.symm
  exact ⟨alg, ψ, ζ, t, ht, hψmul, hspan, hζroot, hnorm, hfix⟩

end OrthTorus

end CFSG.StandardType

end
