module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private lemma omorb_map_pow {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (φ : M →ₗ[K] N) {a : Module.End K M} {b : Module.End K N}
    (h : ∀ m, φ (a m) = b (φ m)) (n : ℕ) (m : M) :
    φ ((a ^ n) m) = (b ^ n) (φ m) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

private lemma omorb_aeval_map_eq {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (φ : M →ₗ[K] N) (a : Module.End K M) (b : Module.End K N)
    (h : ∀ m, φ (a m) = b (φ m)) (g : K[X]) (m : M) :
    φ (aeval a g m) = aeval b g (φ m) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    simp only [LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply]
    rw [map_smul, omorb_map_pow φ h n m]

private lemma omorb_coeff_zero_ne_of_dvd_X_pow_sub_one {f : K[X]} {n : ℕ} (hn : n ≠ 0)
    (hf : f ∣ (X ^ n - 1 : K[X])) : f.coeff 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := hf
  intro h0
  have h := congrArg (fun q : K[X] => q.coeff 0) hg
  simp only [coeff_sub, coeff_X_pow, coeff_one, mul_coeff_zero, h0] at h
  simp [hn.symm] at h

private lemma omorb_reciprocalPolynomial_X_add_C {a : K} (ha : a ≠ 0) :
    reciprocalPolynomial (X + C a : K[X]) = X + C a⁻¹ := by
  have h0 : (X + C a : K[X]).coeff 0 = a := by simp
  have hX : (X : K[X]).reverse = 1 := by
    have := reverse_mul_X (1 : K[X])
    rw [one_mul] at this
    rw [this, show (1 : K[X]) = C 1 from C_1.symm, reverse_C]
  have h1 : (X + C a : K[X]).reverse = 1 + C a * X := by
    rw [reverse_add_C, hX, natDegree_X, pow_one]
  unfold reciprocalPolynomial
  rw [h0, h1, mul_add, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul, mul_one]
  ring

private theorem omorb_block_decomp {D : Type} [AddCommGroup D] [Module K D]
    [FiniteDimensional K D] (hD : finrank K D = 2) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (y : D ≃ₗ[K] D) (hyp : y ^ p = 1) (hfix : ∀ d, y d = d → d = 0)
    (T : D ≃ₗ[K] D) (hT : T * y * T⁻¹ = y⁻¹) :
    ∃ h ∈ primaryFactors y.toLinearMap, h ≠ X - 1 ∧
      Squarefree (minpoly K y.toLinearMap) ∧
      (∀ d : D, d ∈ primaryComponent y.toLinearMap h ⊔
        primaryComponent y.toLinearMap (reciprocalPolynomial h)) := by
  classical
  haveI : Nontrivial D :=
    Module.nontrivial_of_finrank_pos (R := K) (M := D) (by rw [hD]; norm_num)
  have haeval : aeval y.toLinearMap (X ^ p - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero, ← toLinearMap_pow, hyp]
    rfl
  have hdvd : minpoly K y.toLinearMap ∣ (X ^ p - 1 : K[X]) :=
    minpoly.dvd K y.toLinearMap haeval
  have hsqX : Squarefree (X ^ p - 1 : K[X]) := by
    have h := Polynomial.separable_X_pow_sub_C (1 : K) hpK one_ne_zero
    simpa using h.squarefree
  have hsqm : Squarefree (minpoly K y.toLinearMap) :=
    squarefree_minpoly_of_aeval_eq_zero hsqX haeval
  have hmdeg : (minpoly K y.toLinearMap).natDegree ≤ 2 := by
    calc (minpoly K y.toLinearMap).natDegree
        ≤ (LinearMap.charpoly y.toLinearMap).natDegree :=
          natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly _)
            (LinearMap.charpoly_monic _).ne_zero
      _ = finrank K D := LinearMap.charpoly_natDegree _
      _ = 2 := hD
  have hnonempty : (primaryFactors y.toLinearMap).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have h := prod_primaryFactors (x := y.toLinearMap) hsqm
    rw [hempty, Finset.prod_empty] at h
    exact (minpoly.ne_one K y.toLinearMap) h.symm
  obtain ⟨h, hh⟩ := hnonempty
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hhdvd : h ∣ minpoly K y.toLinearMap := (mem_primaryFactors.mp hh).2.2
  have hh0 : h.coeff 0 ≠ 0 :=
    omorb_coeff_zero_ne_of_dvd_X_pow_sub_one hp.pos.ne' (hhdvd.trans hdvd)
  have hne1 : h ≠ X - 1 := by
    intro he
    obtain ⟨d, hd, hd0⟩ :=
      (Submodule.ne_bot_iff _).mp (primaryComponent_ne_bot hsqm (he ▸ hh))
    have hdf : d ∈ fixedSpace y := by rwa [fixedSpace_eq_primaryComponent]
    exact hd0 (hfix d (mem_fixedSpace.mp hdf))
  have hcomm : ∀ e : D, T.toLinearMap (y.toLinearMap e) = y.symm.toLinearMap (T.toLinearMap e) := by
    intro e
    have h1 := congrArg (fun z : D ≃ₗ[K] D => z (T e)) hT
    simpa [LinearEquiv.mul_apply] using h1
  have hTrans : ∀ (g : K[X]) (d : D),
      T (aeval y.toLinearMap g d) = aeval y.symm.toLinearMap g (T d) := by
    intro g d
    exact omorb_aeval_map_eq T.toLinearMap y.toLinearMap y.symm.toLinearMap hcomm g d
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp (primaryComponent_ne_bot hsqm hh)
  have hTd : aeval y.symm.toLinearMap h (T d) = 0 := by
    rw [← hTrans h d, mem_primaryComponent.mp hd, map_zero]
  have hTd_mem : T d ∈ primaryComponent y.toLinearMap (reciprocalPolynomial h) :=
    (mem_primaryComponent_reciprocalPolynomial (x := y) hh0).mpr hTd
  have hstar_mem : reciprocalPolynomial h ∈ primaryFactors y.toLinearMap := by
    by_contra hnotmem
    have hndvd : ¬ reciprocalPolynomial h ∣ minpoly K y.toLinearMap := fun hdiv =>
      hnotmem (mem_primaryFactors.mpr ⟨irreducible_reciprocalPolynomial hirr hh0,
        monic_reciprocalPolynomial hh0, hdiv⟩)
    have hcop : IsCoprime (reciprocalPolynomial h) (minpoly K y.toLinearMap) :=
      (irreducible_reciprocalPolynomial hirr hh0).coprime_iff_not_dvd.mpr hndvd
    have hdisj := Polynomial.disjoint_ker_aeval_of_isCoprime y.toLinearMap hcop
    have htop : LinearMap.ker (aeval y.toLinearMap (minpoly K y.toLinearMap)) = ⊤ := by
      rw [minpoly.aeval, LinearMap.ker_zero]
    rw [htop, disjoint_top] at hdisj
    have hmem : T d ∈ LinearMap.ker (aeval y.toLinearMap (reciprocalPolynomial h)) :=
      mem_primaryComponent.mp hTd_mem
    rw [hdisj] at hmem
    exact (T.injective.ne hd0) (by rw [map_zero]; exact (Submodule.mem_bot K).mp hmem)
  refine ⟨h, hh, hne1, hsqm, ?_⟩
  by_cases hself : h = reciprocalPolynomial h
  · have hle : h.natDegree ≤ (minpoly K y.toLinearMap).natDegree :=
      natDegree_le_of_dvd hhdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))
    have hpos : 0 < h.natDegree := hirr.natDegree_pos
    have hne_deg1 : h.natDegree ≠ 1 := by
      intro hdeg1
      have hform : h = X + C (h.coeff 0) := hmon.eq_X_add_C hdeg1
      have hrecip : reciprocalPolynomial h = X + C (h.coeff 0)⁻¹ := by
        conv_lhs => rw [hform]
        exact omorb_reciprocalPolynomial_X_add_C hh0
      have hCa : (C (h.coeff 0) : K[X]) = C ((h.coeff 0)⁻¹) := by
        have h1 : X + C (h.coeff 0) = X + C ((h.coeff 0)⁻¹) := by
          calc X + C (h.coeff 0) = h := hform.symm
            _ = reciprocalPolynomial h := hself
            _ = X + C (h.coeff 0)⁻¹ := hrecip
        exact add_left_cancel h1
      have ha : h.coeff 0 = (h.coeff 0)⁻¹ := C_injective hCa
      have haa : h.coeff 0 * h.coeff 0 = 1 := by
        simpa [← ha] using mul_inv_cancel₀ hh0
      have htwo : (2 : K) = 0 := by
        have h := CharTwo.add_self_eq_zero (1 : K)
        rwa [← two_mul, mul_one] at h
      have hsq : (h.coeff 0 + 1) ^ 2 = 0 := by
        rw [add_sq, pow_two, haa, htwo, one_pow]
        simp only [zero_mul, add_zero]
        exact CharTwo.add_self_eq_zero 1
      have ha1 : h.coeff 0 = 1 := by
        have h2 : h.coeff 0 = -1 := eq_neg_of_add_eq_zero_left (sq_eq_zero_iff.mp hsq)
        rw [h2, CharTwo.neg_eq]
      have hX1 : h = X - 1 := by
        rw [hform, ha1, CharTwo.sub_eq_add, C_1]
      exact hne1 hX1
    have hm_eq : minpoly K y.toLinearMap = h :=
      eq_of_monic_of_dvd_of_natDegree_le hmon (minpoly.monic (Algebra.IsIntegral.isIntegral _))
        hhdvd (le_of_eq (by omega))
    have htop : primaryComponent y.toLinearMap h = ⊤ := by
      rw [← hm_eq]
      show LinearMap.ker (aeval y.toLinearMap (minpoly K y.toLinearMap)) = ⊤
      rw [minpoly.aeval, LinearMap.ker_zero]
    intro d
    rw [htop, top_sup_eq]
    exact Submodule.mem_top
  · have hh' : reciprocalPolynomial h ∈ primaryFactors y.toLinearMap := hstar_mem
    have hcop : IsCoprime h (reciprocalPolynomial h) :=
      isCoprime_of_mem_primaryFactors hh hh' hself
    have hhdvd' : reciprocalPolynomial h ∣ minpoly K y.toLinearMap :=
      (mem_primaryFactors.mp hh').2.2
    have hmul : h * reciprocalPolynomial h ∣ minpoly K y.toLinearMap :=
      hcop.mul_dvd hhdvd hhdvd'
    have hpos : 0 < h.natDegree := hirr.natDegree_pos
    have hdegstar : (reciprocalPolynomial h).natDegree = h.natDegree :=
      natDegree_reciprocalPolynomial hh0
    have hdegmul : (h * reciprocalPolynomial h).natDegree =
        h.natDegree + (reciprocalPolynomial h).natDegree :=
      hmon.natDegree_mul (monic_reciprocalPolynomial hh0)
    have hle : (h * reciprocalPolynomial h).natDegree ≤
        (minpoly K y.toLinearMap).natDegree :=
      natDegree_le_of_dvd hmul (minpoly.ne_zero (Algebra.IsIntegral.isIntegral _))
    have hEq : minpoly K y.toLinearMap = h * reciprocalPolynomial h :=
      eq_of_monic_of_dvd_of_natDegree_le (hmon.mul (monic_reciprocalPolynomial hh0))
        (minpoly.monic (Algebra.IsIntegral.isIntegral _)) hmul (le_of_eq (by omega))
    have htop : primaryComponent y.toLinearMap h ⊔
        primaryComponent y.toLinearMap (reciprocalPolynomial h) = ⊤ := by
      show LinearMap.ker (aeval y.toLinearMap h) ⊔
        LinearMap.ker (aeval y.toLinearMap (reciprocalPolynomial h)) = ⊤
      rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime y.toLinearMap hcop, ← hEq]
      show LinearMap.ker (aeval y.toLinearMap (minpoly K y.toLinearMap)) = ⊤
      rw [minpoly.aeval, LinearMap.ker_zero]
    intro d
    rw [htop]
    exact Submodule.mem_top

private lemma omorb_toAdd_piMul (f : Fin r → Multiplicative (ZMod p)) (j : Fin r) :
    toAdd (piMul r p f) j = toAdd (f j) := by
  rw [piMul_apply, toAdd_ofAdd]

private lemma omorb_oddOrderIsometry (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f : Fin r → Multiplicative (ZMod p)) : OddOrderIsometry Q p (Δ.τ f) := by
  rw [Δ.τ_eq f]
  exact SevOm.Frame.oddOrderIsometry hQ hp2 hp hA Δ.F (piMul r p f)

theorem TBJOmData.oddOrderIsometry [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f : Fin r → Multiplicative (ZMod p)) :
    OddOrderIsometry Q p (Δ.τ f) :=
  omorb_oddOrderIsometry Δ Fact.out hp2 hQ hA f

theorem TBJOmData.mem_fixedSpace_iff (Δ : TBJOmData Q p A r) (f₀ : Fin r → Multiplicative (ZMod p))
    (v : V) : v ∈ fixedSpace (Δ.τ f₀) ↔
      ∀ j, toAdd (f₀ j) ≠ 0 → ∀ u ∈ Δ.F.U j, QuadraticMap.polar Q u v = 0 := by
  rw [mem_fixedSpace, Δ.τ_eq]
  exact Δ.F.fix (piMul r p f₀) v

private lemma omorb_le_fixedSpace_of_toAdd_eq_zero (Δ : TBJOmData Q p A r)
    (f₀ : Fin r → Multiplicative (ZMod p)) (j : Fin r) (hj : toAdd (f₀ j) = 0) :
    Δ.F.U j ≤ fixedSpace (Δ.τ f₀) := by
  rw [Δ.τ_eq]
  exact Δ.F.le_fixedSpace (s := piMul r p f₀) (by simpa [omorb_toAdd_piMul] using hj)

private lemma omorb_reciprocal_ne_X_sub_one {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) :
    reciprocalPolynomial h ≠ X - 1 := by
  intro he
  exact hX (by rw [← hx.reciprocal_reciprocal_eq hh, he, reciprocalPolynomial_X_sub_one])

private lemma omorb_fixedSpace_le_othersSpace {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) :
    fixedSpace x ≤ othersSpace x.toLinearMap h := by
  classical
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · have hne : (X - 1 : K[X]) ≠ h := fun e => hX e.symm
    have hne' : (X - 1 : K[X]) ≠ reciprocalPolynomial h :=
      (omorb_reciprocal_ne_X_sub_one hx hh hX).symm
    rw [fixedSpace_eq_primaryComponent]
    exact le_iSup₂_of_le (X - 1) ⟨hmem, hne, hne'⟩ le_rfl
  · rw [fixedSpace_eq_bot_of_not_mem hmem]
    exact bot_le

private lemma omorb_orbitSpace_reciprocal {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) :
    orbitSpace x.toLinearMap (reciprocalPolynomial h) = orbitSpace x.toLinearMap h := by
  rw [orbitSpace, orbitSpace, hx.reciprocal_reciprocal_eq hh, sup_comm]

private lemma omorb_orbitSpace_le_othersSpace {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    {h k : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hk : k ∈ primaryFactors x.toLinearMap) (hkh : k ≠ h)
    (hkh' : k ≠ reciprocalPolynomial h) :
    orbitSpace x.toLinearMap k ≤ othersSpace x.toLinearMap h := by
  have hk' : reciprocalPolynomial k ∈ primaryFactors x.toLinearMap := hx.reciprocalPolynomial_mem hk
  have h1 : primaryComponent x.toLinearMap k ≤ othersSpace x.toLinearMap h :=
    le_iSup₂_of_le k ⟨hk, hkh, hkh'⟩ le_rfl
  have h2 : reciprocalPolynomial k ≠ h := by
    intro e
    exact hkh' (by rw [← hx.reciprocal_reciprocal_eq hk, e])
  have h3 : reciprocalPolynomial k ≠ reciprocalPolynomial h := by
    intro e
    exact hkh (by rw [← hx.reciprocal_reciprocal_eq hk, e, hx.reciprocal_reciprocal_eq hh])
  have h4 : primaryComponent x.toLinearMap (reciprocalPolynomial k) ≤
      othersSpace x.toLinearMap h :=
    le_iSup₂_of_le (reciprocalPolynomial k) ⟨hk', h2, h3⟩ le_rfl
  rw [orbitSpace]
  exact sup_le h1 h4

private lemma omorb_isCompl_orthogonal (Δ : TBJOmData Q p A r) (j : Fin r) :
    IsCompl (Δ.F.U j) (LinearMap.BilinForm.orthogonal (polarBilin Q) (Δ.F.U j)) := by
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rw [polar_comm]
    exact h
  have hnd : (LinearMap.BilinForm.restrict (polarBilin Q) (Δ.F.U j)).Nondegenerate := by
    constructor
    · intro x hx
      refine Subtype.ext ?_
      refine Δ.F.nondeg j ↑x x.2 ?_
      intro v hv
      have h := hx ⟨v, hv⟩
      simpa [polarBilin_apply_apply, polar_comm] using h
    · intro y hy
      refine Subtype.ext ?_
      refine Δ.F.nondeg j ↑y y.2 ?_
      intro v hv
      have h := hy ⟨v, hv⟩
      simpa [polarBilin_apply_apply, polar_comm] using h
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd

private lemma omorb_neg_eq (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] (x : V) : -x = x := by
  have h : (-1 : K) • x = x := by rw [CharTwo.neg_eq (1 : K), one_smul]
  simpa using h

private lemma omorb_add_self (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V]
    [Module K V] (x : V) : x + x = 0 := by
  calc x + x = x + -x := by rw [omorb_neg_eq K x]
    _ = 0 := add_neg_cancel x

private lemma omorb_exists_decomp (Δ : TBJOmData Q p A r)
    (f₀ : Fin r → Multiplicative (ZMod p)) (v : V) :
    ∃ u : Fin r → V, (∀ j, u j ∈ Δ.F.U j) ∧
      v - ∑ j, u j ∈ fixedSpace (Δ.τ f₀) := by
  classical
  choose u hu b hb huv using fun j =>
    exists_add_of_isCompl (omorb_isCompl_orthogonal Δ j) v
  refine ⟨u, hu, ?_⟩
  rw [TBJOmData.mem_fixedSpace_iff]
  intro k _ w hw
  set T : V := ∑ j ∈ Finset.univ.erase k, u j with hTdef
  have hsum : ∑ j, u j = u k + T := by
    rw [hTdef]
    exact (Finset.add_sum_erase Finset.univ u (Finset.mem_univ k)).symm
  have hwk : v - ∑ j, u j = b k + T := by
    rw [sub_eq_iff_eq_add, ← huv k, hsum]
    symm
    calc (b k + T) + (u k + T) = (b k + u k) + (T + T) := by abel
      _ = (b k + u k) + 0 := by rw [omorb_add_self K]
      _ = u k + b k := by rw [add_zero, add_comm]
  have h1 : QuadraticMap.polar Q w (b k) = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp (hb k)) w hw
    rwa [polarBilin_apply_apply] at h
  have h2 : QuadraticMap.polar Q w T = 0 := by
    have hsum' : QuadraticMap.polar Q w T =
        ∑ j ∈ Finset.univ.erase k, QuadraticMap.polar Q w (u j) := by
      rw [hTdef]
      simpa [polarBilin_apply_apply] using
        map_sum ((polarBilin Q) w) (fun j => u j) (Finset.univ.erase k)
    rw [hsum']
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_erase] at hj
    exact Δ.F.orth k j hj.1.symm w hw (u j) (hu j)
  rw [hwk, QuadraticMap.polar_add_right, h1, h2, add_zero]

private lemma omorb_block_data (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) (j : Fin r) (hj : toAdd (f₀ j) ≠ 0)
    (y : Δ.D ≃ₗ[K] Δ.D) (hy : y = Δ.c ^ (toAdd (f₀ j)).val) :
    ∃ h, h ∈ primaryFactors y.toLinearMap ∧ h ∈ primaryFactors (Δ.τ f₀).toLinearMap ∧
      h ≠ X - 1 ∧ Squarefree (minpoly K y.toLinearMap) ∧
      (∀ d : Δ.D, d ∈ orbitSpace y.toLinearMap h) ∧
      Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h := by
  classical
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ hp hp2 hQ hA f₀
  have hpK : (p : K) ≠ 0 := hx.cast_ne_zero
  have hyp : y ^ p = 1 := by
    rw [hy]
    calc (Δ.c ^ (toAdd (f₀ j)).val) ^ p = Δ.c ^ ((toAdd (f₀ j)).val * p) :=
          (pow_mul _ _ _).symm
      _ = Δ.c ^ (p * (toAdd (f₀ j)).val) := by rw [mul_comm]
      _ = (Δ.c ^ p) ^ (toAdd (f₀ j)).val := pow_mul _ _ _
      _ = 1 := by rw [Δ.c_pow, one_pow]
  have hfix : ∀ d : Δ.D, y d = d → d = 0 := by
    intro d hd
    have hθ : Δ.θ j d ∈ Δ.F.U j := by
      rw [← Δ.θ_range j]
      exact LinearMap.mem_range.mpr ⟨d, rfl⟩
    have hact : Δ.F.ι (piMul r p f₀) (Δ.θ j d) = Δ.θ j d := by
      rw [Δ.θ_act, omorb_toAdd_piMul, ← hy, hd]
    have h0 : Δ.θ j d = 0 :=
      Δ.F.fpf (piMul r p f₀) j (by rw [omorb_toAdd_piMul]; exact hj) (Δ.θ j d) hθ hact
    exact Δ.θ_inj j (by rw [h0, map_zero])
  obtain ⟨T, hT⟩ := Δ.c_twist
  have hTy : T * y * T⁻¹ = y⁻¹ := by
    have h1 := congrArg (fun z : Δ.D ≃ₗ[K] Δ.D => z ^ (toAdd (f₀ j)).val) hT
    rw [conj_pow] at h1
    rw [hy, h1, ← inv_pow]
  obtain ⟨h, hh_y, hne1, hsq, hdec⟩ :=
    omorb_block_decomp Δ.finrank_D hp hpK y hyp hfix T hTy
  have hcommθ : ∀ d : Δ.D, Δ.θ j (y d) = Δ.τ f₀ (Δ.θ j d) := by
    intro d
    rw [Δ.τ_eq, hy, Δ.θ_act, omorb_toAdd_piMul]
  have hTransθ : ∀ (g : K[X]) (d : Δ.D),
      Δ.θ j (aeval y.toLinearMap g d) = aeval (Δ.τ f₀).toLinearMap g (Δ.θ j d) :=
    fun g d => omorb_aeval_map_eq (Δ.θ j) y.toLinearMap (Δ.τ f₀).toLinearMap hcommθ g d
  have hmin : minpoly K y.toLinearMap ∣ minpoly K (Δ.τ f₀).toLinearMap := by
    refine minpoly.dvd K _ ?_
    ext d
    apply Δ.θ_inj j
    rw [hTransθ (minpoly K (Δ.τ f₀).toLinearMap) d, minpoly.aeval]
    simp
  refine ⟨h, hh_y, ?_, hne1, hsq, hdec, ?_⟩
  · exact mem_primaryFactors.mpr ⟨irreducible_of_mem_primaryFactors hh_y,
      monic_of_mem_primaryFactors hh_y, (mem_primaryFactors.mp hh_y).2.2 |>.trans hmin⟩
  · intro u hu
    rw [← Δ.θ_range j] at hu
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨d1, hd1, d2, hd2, rfl⟩ := Submodule.mem_sup.mp (hdec d)
    rw [map_add]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_primaryComponent, ← hTransθ h d1, mem_primaryComponent.mp hd1, map_zero]
    · rw [mem_primaryComponent, ← hTransθ (reciprocalPolynomial h) d2,
        mem_primaryComponent.mp hd2, map_zero]

private lemma omorb_piece_orbit (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) (j : Fin r) (hj : toAdd (f₀ j) ≠ 0) :
    ∃ h ∈ primaryFactors (Δ.τ f₀).toLinearMap, h ≠ X - 1 ∧
      Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h := by
  obtain ⟨h, -, hhx, hne1, -, -, hU⟩ :=
    omorb_block_data Δ hp hp2 hQ hA f₀ j hj (Δ.c ^ (toAdd (f₀ j)).val) rfl
  exact ⟨h, hhx, hne1, hU⟩

private lemma omorb_piece_othersSpace (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1)
    {j : Fin r} {u : V} (hu : u ∈ Δ.F.U j)
    (hj : ¬ Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h) :
    u ∈ othersSpace (Δ.τ f₀).toLinearMap h := by
  classical
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ hp hp2 hQ hA f₀
  by_cases ht : toAdd (f₀ j) = 0
  · exact omorb_fixedSpace_le_othersSpace hx hh hX
      (omorb_le_fixedSpace_of_toAdd_eq_zero Δ f₀ j ht hu)
  · obtain ⟨k, hk, -, hUk⟩ := omorb_piece_orbit Δ hp hp2 hQ hA f₀ j ht
    have hkh : k ≠ h := by
      intro e
      exact hj (by rwa [← e])
    have hkh' : k ≠ reciprocalPolynomial h := by
      intro e
      exact hj (by rwa [← omorb_orbitSpace_reciprocal hx hh, ← e])
    exact omorb_orbitSpace_le_othersSpace hx hh hk hkh hkh' (hUk hu)

private lemma omorb_orbitSpace_le_iSup (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    orbitSpace (Δ.τ f₀).toLinearMap h ≤
      ⨆ (j : Fin r) (_ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h), Δ.F.U j := by
  classical
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ hp hp2 hQ hA f₀
  intro v hv
  obtain ⟨u, hu, hw⟩ := omorb_exists_decomp Δ f₀ v
  set O := orbitSpace (Δ.τ f₀).toLinearMap h
  set G : Finset (Fin r) := Finset.univ.filter (fun j => Δ.F.U j ≤ O) with hG
  set s : V := ∑ j ∈ G, u j with hs
  have hs_mem : s ∈ ⨆ (j : Fin r) (_ : Δ.F.U j ≤ O), Δ.F.U j := by
    rw [hs]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [hG, Finset.mem_filter] at hj
    exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj.2 (hu j))
  have hsO : s ∈ O := by
    rw [hs]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [hG, Finset.mem_filter] at hj
    exact hj.2 (hu j)
  have hsplit : ∑ j, u j = s + ∑ j ∈ Finset.univ.filter (fun j => ¬ (Δ.F.U j ≤ O)), u j := by
    rw [hs, hG]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => Δ.F.U j ≤ O) u).symm
  have hrO : v - s ∈ O := Submodule.sub_mem _ hv hsO
  have hrR : v - s ∈ othersSpace (Δ.τ f₀).toLinearMap h := by
    have hvs2 : v - s = (∑ j ∈ Finset.univ.filter (fun j => ¬ (Δ.F.U j ≤ O)), u j) +
        (v - ∑ j, u j) := by
      rw [sub_eq_iff_eq_add]
      symm
      calc (∑ j ∈ Finset.univ.filter (fun j => ¬ (Δ.F.U j ≤ O)), u j) +
            (v - ∑ j, u j) + s
          = s + ((∑ j ∈ Finset.univ.filter (fun j => ¬ (Δ.F.U j ≤ O)), u j) +
            (v - ∑ j, u j)) := add_comm _ _
        _ = (s + ∑ j ∈ Finset.univ.filter (fun j => ¬ (Δ.F.U j ≤ O)), u j) +
            (v - ∑ j, u j) := (add_assoc s _ _).symm
        _ = (∑ j, u j) + (v - ∑ j, u j) := by rw [← hsplit]
        _ = v := by abel
    rw [hvs2]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.sum_mem _ fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact omorb_piece_othersSpace Δ hp hp2 hQ hA f₀ hh hX (hu j) hj.2
    · exact omorb_fixedSpace_le_othersSpace hx hh hX hw
  have hzero : v - s = 0 := by
    have hbot : O ⊓ othersSpace (Δ.τ f₀).toLinearMap h = ⊥ :=
      (hx.isCompl_orbit_others hh).disjoint.eq_bot
    have hmem : v - s ∈ O ⊓ othersSpace (Δ.τ f₀).toLinearMap h :=
      Submodule.mem_inf.mpr ⟨hrO, hrR⟩
    rw [hbot] at hmem
    exact (Submodule.mem_bot K).mp hmem
  rw [sub_eq_zero.mp hzero]
  exact hs_mem

theorem TBJOmData.orbitSpace_eq [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    orbitSpace (Δ.τ f₀).toLinearMap h =
      ⨆ (j : Fin r) (_ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h), Δ.F.U j := by
  refine le_antisymm (omorb_orbitSpace_le_iSup Δ Fact.out hp2 hQ hA f₀ hh hX) ?_
  exact iSup₂_le fun j hj => hj

theorem TBJOmData.active_of_le_orbitSpace [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) (j : Fin r)
    (hU : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h) : toAdd (f₀ j) ≠ 0 := by
  intro ht
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ Fact.out hp2 hQ hA f₀
  have hle : Δ.F.U j ≤ othersSpace (Δ.τ f₀).toLinearMap h :=
    le_trans (omorb_le_fixedSpace_of_toAdd_eq_zero Δ f₀ j ht)
      (omorb_fixedSpace_le_othersSpace hx hh hX)
  have hbot : orbitSpace (Δ.τ f₀).toLinearMap h ⊓
      othersSpace (Δ.τ f₀).toLinearMap h = ⊥ :=
    (hx.isCompl_orbit_others hh).disjoint.eq_bot
  have hlebot : Δ.F.U j ≤ ⊥ := fun u hu => by
    have hmem : u ∈ orbitSpace (Δ.τ f₀).toLinearMap h ⊓
        othersSpace (Δ.τ f₀).toLinearMap h :=
      Submodule.mem_inf.mpr ⟨hU hu, hle hu⟩
    rw [hbot] at hmem
    exact hmem
  exact Δ.F.ne_bot j (le_bot_iff.mp hlebot)

private lemma omorb_exists_piece (Δ : TBJOmData Q p A r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ j, toAdd (f₀ j) ≠ 0 ∧ Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ hp hp2 hQ hA f₀
  have hO_ne : orbitSpace (Δ.τ f₀).toLinearMap h ≠ ⊥ := by
    intro hbot
    have hle : primaryComponent (Δ.τ f₀).toLinearMap h ≤ orbitSpace (Δ.τ f₀).toLinearMap h :=
      le_sup_left
    exact primaryComponent_ne_bot hx.squarefree_minpoly hh (le_bot_iff.mp (hbot ▸ hle))
  have hex : ∃ j, Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h := by
    by_contra hnone
    push Not at hnone
    have hbot : (⨆ (j : Fin r) (_ : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h),
        Δ.F.U j) = ⊥ :=
      iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => absurd hj (hnone j)
    have hle := omorb_orbitSpace_le_iSup Δ hp hp2 hQ hA f₀ hh hX
    rw [hbot] at hle
    exact hO_ne (le_bot_iff.mp hle)
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, TBJOmData.active_of_le_orbitSpace (p := p) (Q := Q) hp2 Δ hQ hA f₀ hh hX j hj, hj⟩

theorem TBJOmData.exists_piece [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) :
    ∃ j, toAdd (f₀ j) ≠ 0 ∧ Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h :=
  omorb_exists_piece Δ Fact.out hp2 hQ hA f₀ hh hX

theorem TBJOmData.piece_ker [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) (hX : h ≠ X - 1) (j : Fin r)
    (hj : toAdd (f₀ j) ≠ 0) (hU : Δ.F.U j ≤ orbitSpace (Δ.τ f₀).toLinearMap h) :
    (∃ d : Δ.D, d ≠ 0 ∧
      aeval ((Δ.c ^ (toAdd (f₀ j)).val : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D) h d = 0) ∨
    (∃ d : Δ.D, d ≠ 0 ∧
      aeval ((Δ.c ^ (toAdd (f₀ j)).val : Δ.D ≃ₗ[K] Δ.D) : Δ.D →ₗ[K] Δ.D)
        (reciprocalPolynomial h) d = 0) := by
  classical
  have hx : OddOrderIsometry Q p (Δ.τ f₀) := omorb_oddOrderIsometry Δ Fact.out hp2 hQ hA f₀
  obtain ⟨h', hh'_y, hh'_x, -, hsq', -, hU'⟩ :=
    omorb_block_data Δ Fact.out hp2 hQ hA f₀ j hj (Δ.c ^ (toAdd (f₀ j)).val) rfl
  have hex : h' = h ∨ h' = reciprocalPolynomial h := by
    by_contra hnot
    push Not at hnot
    have hle : orbitSpace (Δ.τ f₀).toLinearMap h' ≤ othersSpace (Δ.τ f₀).toLinearMap h :=
      omorb_orbitSpace_le_othersSpace hx hh hh'_x hnot.1 hnot.2
    have hbot : orbitSpace (Δ.τ f₀).toLinearMap h ⊓
        othersSpace (Δ.τ f₀).toLinearMap h = ⊥ :=
      (hx.isCompl_orbit_others hh).disjoint.eq_bot
    have hlebot : Δ.F.U j ≤ ⊥ := fun u hu => by
      have hmem : u ∈ orbitSpace (Δ.τ f₀).toLinearMap h ⊓
          othersSpace (Δ.τ f₀).toLinearMap h :=
        Submodule.mem_inf.mpr ⟨hU hu, hle (hU' hu)⟩
      rw [hbot] at hmem
      exact hmem
    exact Δ.F.ne_bot j (le_bot_iff.mp hlebot)
  rcases hex with heq | heq
  · left
    have hmem : primaryComponent (Δ.c ^ (toAdd (f₀ j)).val).toLinearMap h' ≠ ⊥ :=
      primaryComponent_ne_bot hsq' hh'_y
    rw [heq] at hmem
    obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp hmem
    exact ⟨d, hd0, mem_primaryComponent.mp hd⟩
  · right
    have hmem : primaryComponent (Δ.c ^ (toAdd (f₀ j)).val).toLinearMap h' ≠ ⊥ :=
      primaryComponent_ne_bot hsq' hh'_y
    rw [heq] at hmem
    obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).mp hmem
    exact ⟨d, hd0, mem_primaryComponent.mp hd⟩

end OrthTorus

end CFSG.StandardType

end
