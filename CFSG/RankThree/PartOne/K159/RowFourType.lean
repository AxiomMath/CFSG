module

public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.RankThree.PartOne.KC.OrthogonalPairedModel

public section

namespace CFSG.RankThree.PartOne.K159

open Module QuadraticMap CFSG.GroupTheory.WeirSylow Polynomial

section TypeProd

variable {K : Type} [Field K] [Finite K]

theorem isPlusType_prod_iff {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (h₁ : (polarBilin Q₁).Nondegenerate) (h₂ : (polarBilin Q₂).Nondegenerate)
    {d₁ d₂ : ℕ} (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hdim₁ : finrank K V₁ = 2 * d₁)
    (hdim₂ : finrank K V₂ = 2 * d₂) :
    IsPlusType (Q₁.prod Q₂) ↔ (IsPlusType Q₁ ↔ IsPlusType Q₂) := by
  rcases exists_isometry_quadPlus_or_quadMinus Q₂ h₂ hd₂ hdim₂ with ⟨⟨e₂⟩⟩ | ⟨b, c, hirr, ⟨e₂⟩⟩
  · have hp2 : IsPlusType Q₂ := (isPlusType_congr e₂).2 (isPlusType_quadPlus K d₂)
    by_cases hp1 : IsPlusType Q₁
    · exact ⟨fun _ => ⟨fun _ => hp2, fun _ => hp1⟩, fun _ => hp1.prod hp2⟩
    · have : ¬ IsPlusType (Q₁.prod Q₂) := by
        have h3 := not_isPlusType_prod_quadPlus h₁ hd₁ hdim₁ hp1 d₂
        rwa [isPlusType_congr ((QuadraticMap.IsometryEquiv.refl Q₁).prod e₂)]
      exact ⟨fun h => absurd h this, fun h => absurd (h.2 hp2) hp1⟩
  · have hnp2 : ¬ IsPlusType Q₂ := by
      rw [isPlusType_congr e₂]
      exact not_isPlusType_quadMinus (by omega) hirr
    by_cases hp1 : IsPlusType Q₁
    · have : ¬ IsPlusType (Q₁.prod Q₂) := by
        have h3 := not_isPlusType_prod_quadMinus h₁ hdim₁ hp1 hd₂ hirr
        rwa [isPlusType_congr ((QuadraticMap.IsometryEquiv.refl Q₁).prod e₂)]
      exact ⟨fun h => absurd h this, fun h => absurd (h.1 hp1) hnp2⟩
    · have : IsPlusType (Q₁.prod Q₂) := by
        have h3 := isPlusType_prod_quadMinus h₁ hd₁ hdim₁ hp1 d₂ hirr
        rwa [isPlusType_congr ((QuadraticMap.IsometryEquiv.refl Q₁).prod e₂)]
      exact ⟨fun _ => ⟨fun h => absurd h hp1, fun h => absurd h hnp2⟩, fun _ => this⟩

end TypeProd

section SupIso

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def supEquiv (A B : Submodule K V) (hAB : Disjoint A B) :
    (A × B) ≃ₗ[K] ↥(A ⊔ B) :=
  LinearEquiv.ofBijective
    ((LinearMap.codRestrict (A ⊔ B) (A.subtype.coprod B.subtype) fun ab =>
      Submodule.add_mem_sup ab.1.2 ab.2.2))
    ⟨fun ab ab' h => by
      have h1 : (ab.1 : V) + ab.2 = ab'.1 + ab'.2 := congrArg Subtype.val h
      have h2 : (ab.1 : V) - ab'.1 = ab'.2 - ab.2 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm (ab'.2 : V)]
        exact h1
      have h3 : ((ab.1 - ab'.1 : A) : V) ∈ A ⊓ B := by
        refine ⟨(ab.1 - ab'.1).2, ?_⟩
        have : ((ab.1 - ab'.1 : A) : V) = ab'.2 - ab.2 := h2
        rw [this]
        exact B.sub_mem ab'.2.2 ab.2.2
      have h4 := (Submodule.disjoint_def.1 hAB) _ (h3.1) (h3.2)
      have h5 : ab.1 = ab'.1 := sub_eq_zero.1 (Subtype.ext h4)
      have h6 : (ab.2 : V) = ab'.2 := by
        have := h1
        rw [congrArg Subtype.val h5] at this
        exact add_left_cancel this
      exact Prod.ext h5 (Subtype.ext h6),
    fun v => by
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 v.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩⟩

theorem supEquiv_apply (A B : Submodule K V) (hAB : Disjoint A B) (a : A) (b : B) :
    ((supEquiv A B hAB (a, b) : ↥(A ⊔ B)) : V) = (a : V) + b := rfl

noncomputable def isometryEquivSup (Q : QuadraticForm K V) (A B : Submodule K V) (hAB : Disjoint A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0) :
    (Q.comp (A ⊔ B).subtype).IsometryEquiv ((Q.comp A.subtype).prod (Q.comp B.subtype)) where
  toLinearEquiv := (supEquiv A B hAB).symm
  map_app' v := by
    obtain ⟨⟨a, b⟩, rfl⟩ := (supEquiv A B hAB).surjective v
    change ((Q.comp A.subtype).prod (Q.comp B.subtype))
      ((supEquiv A B hAB).symm (supEquiv A B hAB (a, b))) = _
    rw [LinearEquiv.symm_apply_apply]
    simp only [QuadraticMap.comp_apply, QuadraticMap.prod_apply, Submodule.subtype_apply,
      supEquiv_apply]
    rw [QuadraticMap.map_add (⇑Q) _ _, horth a a.2 b b.2, add_zero]

end SupIso

section Factors

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [CharP K 2] in
theorem not_dvd_card_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card K - 1 := by
  intro h
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h
  have h3 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
  rw [h3] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

omit [CharP K 2] in
theorem natDegree_eq_two_of_dvd_card_add_one (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : h.natDegree = 2 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ (X ^ p - 1 : K[X]) := hx.dvd_X_pow_sub_one hh
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have hpq2 : p ∣ Nat.card K ^ 2 - 1 := by
    have h1 : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      obtain ⟨a, ha⟩ : ∃ a, Nat.card K = a + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [ha]
      simp only [Nat.add_sub_cancel]
      apply Nat.sub_eq_of_eq_add
      ring
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨m, hm⟩ := hpq2
  have hdvd2 : h ∣ (X ^ (Nat.card K ^ 2) - X : K[X]) := by
    have h1 : (X ^ p - 1 : K[X]) ∣ (X ^ p) ^ m - 1 ^ m := sub_dvd_pow_sub_pow _ _ _
    rw [← pow_mul, one_pow, ← hm] at h1
    have h2 : (X ^ (Nat.card K ^ 2) - X : K[X]) = X * (X ^ (Nat.card K ^ 2 - 1) - 1) := by
      rw [mul_sub, mul_one, ← pow_succ']
      congr 2
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq
      omega
    rw [h2]
    exact (hdvd.trans h1).mul_left X
  have hdeg : h.natDegree ∣ 2 := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).2 hdvd2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdeg with h1 | h2
  · exfalso
    have heq : h = X - C (-(h.coeff 0)) := by
      rw [hmon.eq_X_add_C h1] at *
      simp
    set r : K := -(h.coeff 0) with hr
    have hroot : r ^ p = 1 := by
      have := Polynomial.dvd_iff_isRoot.1 (heq ▸ hdvd)
      simpa [sub_eq_zero] using this
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hroot
      exact zero_ne_one hroot
    have hq1 : r ^ (Nat.card K - 1) = 1 := by
      have := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one r hr0
    have hcop : Nat.gcd p (Nat.card K - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_sub_one hp hp2 hpq)
    have h3 : r ^ Nat.gcd p (Nat.card K - 1) = 1 := pow_gcd_eq_one.2 ⟨hroot, hq1⟩
    rw [hcop, pow_one] at h3
    apply hne1
    rw [heq, h3]
    simp
  · exact h2

omit [CharP K 2] in
theorem reciprocalPolynomial_eq_of_dvd_card_add_one (hx : OddOrderIsometry Q p x)
    (hpq : p ∣ Nat.card K + 1) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) :
    reciprocalPolynomial h = h := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ (X ^ p - 1 : K[X]) := hx.dvd_X_pow_sub_one hh
  have h0 := hx.coeff_zero_ne hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  set ξ : AdjoinRoot h := AdjoinRoot.root h with hξ
  have hξp : ξ ^ p = 1 := root_pow_eq_one hdvd
  have hξq : ξ ^ (Nat.card K + 1) = 1 := by
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hξp, one_pow]
  have hξ0 : ξ ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (Nat.succ_ne_zero _)] at hξq
    exact zero_ne_one hξq
  have hinv : ξ ^ Nat.card K = ξ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hξq
  have hroot : aeval ξ h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h1 : aeval (ξ ^ Nat.card K) h = 0 := by
    have := Fintype.ofFinite K
    have h2 := FiniteField.Polynomial.expand_card (K := K) h
    rw [← Nat.card_eq_fintype_card] at h2
    rw [← Polynomial.expand_aeval, h2, map_pow, hroot, zero_pow]
    exact (Nat.card_pos (α := K)).ne'
  have h3 : aeval (ξ ^ Nat.card K) (reciprocalPolynomial h) = 0 := by
    have hu0 : ξ ^ Nat.card K ≠ 0 := pow_ne_zero _ hξ0
    have := aeval_reciprocalPolynomial_of_unit (A := AdjoinRoot h) (Units.mk0 _ hu0) h
    rw [Units.val_mk0] at this
    rw [this]
    have h4 : ((Units.mk0 (ξ ^ Nat.card K) hu0)⁻¹ : (AdjoinRoot h)ˣ).val = ξ := by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, hinv, inv_inv]
    rw [h4, hroot, mul_zero, smul_zero]
  have e1 : h = minpoly K (ξ ^ Nat.card K) := minpoly.eq_of_irreducible_of_monic hirr h1 hmon
  have e2 : reciprocalPolynomial h = minpoly K (ξ ^ Nat.card K) :=
    minpoly.eq_of_irreducible_of_monic (irreducible_reciprocalPolynomial hirr h0) h3
      (monic_reciprocalPolynomial h0)
  rw [e2, ← e1]

omit [CharP K 2] in
theorem reciprocalPolynomial_eq_of_mem (hx : OddOrderIsometry Q p x) (hpq : p ∣ Nat.card K + 1)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) : reciprocalPolynomial h = h :=
  reciprocalPolynomial_eq_of_dvd_card_add_one hx hpq hh

end Factors

section Plane

open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] def RegOn (Q : QuadraticForm K V) (U : Submodule K V) : Prop :=
  ∀ u ∈ U, (∀ w ∈ U, polar Q u w = 0) → u = 0

theorem vec_add_self (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (w : V) : w + w = 0 := by
  rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]

theorem neg_eq_self_vec (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (w : V) : -w = w := neg_eq_of_add_eq_zero_right (vec_add_self K w)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem pow_apply_mem {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) (n : ℕ) {u : V} (hu : u ∈ U) :
    (x.toLinearMap ^ n) u ∈ U := by
  induction n generalizing u with
  | zero => simpa using hu
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (hxU u hu)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem aeval_mem {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) (f : K[X]) {u : V} (hu : u ∈ U) :
    aeval x.toLinearMap f u ∈ U := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact U.smul_mem c (pow_apply_mem hxU n hu)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem primaryProjection_mem_of_invariant {U : Submodule K V}
    (hxU : ∀ u ∈ U, x u ∈ U) (a : K[X]) {u : V} (hu : u ∈ U) :
    primaryProjection x.toLinearMap a u ∈ U :=
  aeval_mem hxU _ hu

omit [Finite K] [CharP K 2] in
theorem exists_polar_primaries (hx : OddOrderIsometry Q p x) {u v : V} (huv : polar Q u v ≠ 0) :
    ∃ a ∈ primaryFactors x.toLinearMap, ∃ b ∈ primaryFactors x.toLinearMap,
      polar Q (primaryProjection x.toLinearMap a u) (primaryProjection x.toLinearMap b v) ≠ 0 := by
  classical
  have hsq := hx.squarefree_minpoly
  have hsum : ∀ w : V, ∑ a ∈ primaryFactors x.toLinearMap, primaryProjection x.toLinearMap a w = w :=
    fun w => by
      have := LinearMap.congr_fun (sum_primaryProjection hsq) w
      rwa [LinearMap.sum_apply] at this
  have h1 : polar Q u v = ∑ b ∈ primaryFactors x.toLinearMap,
      polar Q u (primaryProjection x.toLinearMap b v) := by
    conv_lhs => rw [← hsum v]
    exact map_sum (polarBilin Q u) _ _
  obtain ⟨b, hb, hb0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ huv)
  have h2 : polar Q u (primaryProjection x.toLinearMap b v) =
      ∑ a ∈ primaryFactors x.toLinearMap,
        polar Q (primaryProjection x.toLinearMap a u) (primaryProjection x.toLinearMap b v) := by
    conv_lhs => rw [← hsum u]
    exact map_sum ((polarBilin Q).flip (primaryProjection x.toLinearMap b v)) _ _
  obtain ⟨a, ha, ha0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2 ▸ hb0)
  exact ⟨a, ha, b, hb, ha0⟩

omit [CharP K 2] in
theorem exists_vector (hx : OddOrderIsometry Q p x) (hpq : p ∣ Nat.card K + 1)
    {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) (hreg : RegOn Q U)
    (hfix : ∀ u ∈ U, x u = u → u = 0) (hU : U ≠ ⊥) :
    ∃ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 ∧
      ∃ v ∈ U, v ∈ primaryComponent x.toLinearMap h ∧ Q v ≠ 0 := by
  classical
  have hsq := hx.squarefree_minpoly
  obtain ⟨u₁, hu₁, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨u₂, hu₂, hpol⟩ : ∃ u₂ ∈ U, polar Q u₁ u₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu₁0 (hreg u₁ hu₁ hcon)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_polar_primaries hx hpol
  have hself : ∀ h ∈ primaryFactors x.toLinearMap, reciprocalPolynomial h = h := fun h hh =>
    reciprocalPolynomial_eq_of_mem hx hpq hh
  have hab' : a = b := by
    by_contra hne
    apply hab
    refine hx.polar_primaryComponent_eq_zero ha hb ?_ (primaryProjection_mem hsq ha u₁)
      (primaryProjection_mem hsq hb u₂)
    rw [hself a ha]
    exact fun h => hne h.symm
  subst hab'
  have hane : a ≠ X - 1 := by
    rintro rfl
    apply hab
    have hmem : primaryProjection x.toLinearMap (X - 1) u₁ ∈ U :=
      primaryProjection_mem_of_invariant hxU _ hu₁
    have hfixed : x (primaryProjection x.toLinearMap (X - 1) u₁) =
        primaryProjection x.toLinearMap (X - 1) u₁ := by
      have := mem_primaryComponent.1 (primaryProjection_mem hsq ha u₁)
      simpa [sub_eq_zero] using this
    rw [hfix _ hmem hfixed, QuadraticMap.polar_zero_left]
  refine ⟨a, ha, hane, ?_⟩
  have hw₁ : primaryProjection x.toLinearMap a u₁ ∈ U := primaryProjection_mem_of_invariant hxU _ hu₁
  have hw₂ : primaryProjection x.toLinearMap a u₂ ∈ U := primaryProjection_mem_of_invariant hxU _ hu₂
  have hc₁ := primaryProjection_mem hsq ha u₁
  have hc₂ := primaryProjection_mem hsq ha u₂
  by_contra hcon
  push Not at hcon
  apply hab
  have h1 := hcon _ hw₁ hc₁
  have h2 := hcon _ hw₂ hc₂
  have h3 := hcon _ (U.add_mem hw₁ hw₂) ((primaryComponent x.toLinearMap a).add_mem hc₁ hc₂)
  rw [QuadraticMap.polar, h3, h1, h2]
  simp

theorem exists_plane (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) (hreg : RegOn Q U)
    (hfix : ∀ u ∈ U, x u = u → u = 0) (hU : U ≠ ⊥) :
    ∃ (v : V) (c : K), v ∈ U ∧ c ≠ 0 ∧ Q v ≠ 0 ∧ x (x v) = c • x v + v ∧
      polar Q v (x v) = c * Q v ∧ ∀ s : K, s ^ 2 + c * s + 1 ≠ 0 := by
  classical
  obtain ⟨h, hh, hne1, v, hvU, hvh, hQv⟩ := exists_vector hx hpq hxU hreg hfix hU
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdeg := natDegree_eq_two_of_dvd_card_add_one hx hp hp2 hpq hh hne1
  have hnoroot : ∀ s : K, h.eval s ≠ 0 := by
    intro s hs
    have h1 : h.degree = 1 := degree_eq_one_of_irreducible_of_root hirr (Polynomial.IsRoot.def.2 hs)
    have h2 : h.natDegree = 1 := Polynomial.natDegree_eq_of_degree_eq_some h1
    omega
  set c : K := h.coeff 1 with hc
  set e : K := h.coeff 0 with he
  have hc2 : h.coeff 2 = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  have heval : ∀ s : K, h.eval s = s ^ 2 + c * s + e := by
    intro s
    rw [Polynomial.eval_eq_sum_range' (n := 3) (by omega)]
    simp [Finset.sum_range_succ, hc2]
    ring
  have hvv : x (x v) + c • x v + e • v = 0 := by
    have h1 := mem_primaryComponent.1 hvh
    rw [Polynomial.aeval_eq_sum_range' (n := 3) (by omega)] at h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_apply,
      LinearMap.smul_apply, hc2, pow_zero, Module.End.one_apply, pow_one, one_smul] at h1
    have h2 : (x.toLinearMap ^ 2) v = x (x v) := by
      rw [pow_two, Module.End.mul_apply]
      rfl
    rw [h2] at h1
    simp only [LinearEquiv.coe_coe] at h1
    calc x (x v) + c • x v + e • v = h.coeff 0 • v + h.coeff 1 • x v + x (x v) := by
          rw [hc, he]
          abel
      _ = 0 := h1
  set w := x v with hw
  have hxx : x w = c • w + e • v := by
    have : x w = -(c • w + e • v) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]
      exact hvv
    rw [this, neg_eq_self_vec K]
  have hQw : Q w = Q v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx.mem v
  have hQxw : Q (x w) = Q v := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx.mem w, hQw]
  have hpol1 : polar Q w (x w) = polar Q v w :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem v w
  have hww : polar Q w w = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  set B : K := polar Q v w with hB
  have hwv : polar Q w v = B := QuadraticMap.polar_comm _ _ _
  have eqB : e * B = B := by
    rw [hxx, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, hww, hwv] at hpol1
    simpa using hpol1
  have eqQ : Q v = c * c * Q v + e * e * Q v + c * e * B := by
    have h1 := hQxw
    rw [hxx, QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hwv, hQw] at h1
    simp only [smul_eq_mul] at h1
    linear_combination -h1
  have h11 : (1 : K) ^ 2 + c * 1 + e ≠ 0 := by
    have := hnoroot 1
    rwa [heval] at this
  by_cases he1 : e = 1
  · rw [he1] at eqQ h11 hxx
    have hc0 : c ≠ 0 := by
      intro hc0
      apply h11
      rw [hc0]
      calc (1 : K) ^ 2 + 0 * 1 + 1 = 1 + 1 := by ring
        _ = 0 := CharTwo.add_self_eq_zero 1
    have h1 : c * (c * Q v + B) = 0 := by
      linear_combination (-1 : K) * eqQ
    have h2 : c * Q v + B = 0 := (mul_eq_zero.1 h1).resolve_left hc0
    have hBc : B = c * Q v := by
      rw [CharTwo.add_eq_zero] at h2
      exact h2.symm
    refine ⟨v, c, hvU, hc0, hQv, ?_, hBc, fun s => ?_⟩
    · rw [hxx, one_smul]
    · have := hnoroot s
      rwa [heval, he1] at this
  · exfalso
    have hB0 : B = 0 := by
      have h1 : (e - 1) * B = 0 := by linear_combination eqB
      exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 he1)
    rw [hB0, mul_zero, add_zero] at eqQ
    have h1 : (c * c + e * e - 1) * Q v = 0 := by linear_combination -eqQ
    have h2 : c * c + e * e - 1 = 0 := (mul_eq_zero.1 h1).resolve_right hQv
    have h3 : (1 + c + e) ^ 2 = 0 := by
      rw [CharTwo.add_sq, CharTwo.add_sq, one_pow]
      have h4 : c ^ 2 + e ^ 2 = 1 := by
        have : c * c + e * e = 1 := sub_eq_zero.1 h2
        rw [← this]
        ring
      rw [add_assoc, h4]
      exact CharTwo.add_self_eq_zero 1
    have h5 : 1 + c + e = 0 := pow_eq_zero_iff (by norm_num) |>.1 h3
    apply h11
    rw [← h5]
    ring

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem plane_form {v : V} {c : K} (hQ : Q (x v) = Q v) (hB : polar Q v (x v) = c * Q v) (s t : K) :
    Q (s • v + t • x v) = Q v * (s ^ 2 + c * s * t + t ^ 2) := by
  rw [QuadraticMap.map_add (⇑Q) _ _, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hQ, hB]
  simp only [smul_eq_mul]
  ring

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem form_aniso {v : V} {c : K} (hQ : Q (x v) = Q v) (hB : polar Q v (x v) = c * Q v)
    (hQv : Q v ≠ 0) (hroot : ∀ s : K, s ^ 2 + c * s + 1 ≠ 0) {s t : K}
    (h : Q (s • v + t • x v) = 0) : s = 0 ∧ t = 0 := by
  rw [plane_form hQ hB] at h
  have h1 : s ^ 2 + c * s * t + t ^ 2 = 0 := (mul_eq_zero.1 h).resolve_left hQv
  by_cases ht : t = 0
  · subst ht
    have : s ^ 2 = 0 := by simpa using h1
    exact ⟨pow_eq_zero_iff (by norm_num) |>.1 this, rfl⟩
  · exfalso
    apply hroot (s / t)
    field_simp
    linear_combination h1

structure PlaneData (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (v : V) (c : K) : Prop where
  hc : c ≠ 0
  hQv : Q v ≠ 0
  hxx : x (x v) = c • x v + v
  hQ : Q (x v) = Q v
  hB : polar Q v (x v) = c * Q v
  hroot : ∀ s : K, s ^ 2 + c * s + 1 ≠ 0

section PlaneData

variable {v : V} {c : K}

omit [Finite K] [FiniteDimensional K V] in
theorem polar_self_zero (w : V) : polar Q w w = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem PlaneData.polar_xv_v (hd : PlaneData Q x v c) : polar Q (x v) v = c * Q v := by
  rw [QuadraticMap.polar_comm]
  exact hd.hB

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_plane_left (a b : V) (s t : K) :
    polar Q (s • a + t • x v) b = s * polar Q a b + t * polar Q (x v) b := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left]
  rfl

noncomputable def plane (x : V ≃ₗ[K] V) (v : V) : Submodule K V := Submodule.span K {v, x v}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_plane {u : V} : u ∈ plane x v ↔ ∃ s t : K, s • v + t • x v = u :=
  Submodule.mem_span_pair

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem PlaneData.plane_invariant (hd : PlaneData Q x v c) {u : V} (hu : u ∈ plane x v) :
    x u ∈ plane x v := by
  obtain ⟨s, t, rfl⟩ := mem_plane.1 hu
  refine mem_plane.2 ⟨t, s + t * c, ?_⟩
  rw [map_add, map_smul, map_smul, hd.hxx]
  simp only [smul_add, smul_smul, add_smul]
  abel

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.eq_zero_of_polar (hd : PlaneData Q x v c) {s t : K}
    (h1 : polar Q (s • v + t • x v) v = 0) (h2 : polar Q (s • v + t • x v) (x v) = 0) :
    s = 0 ∧ t = 0 := by
  have hβ : c * Q v ≠ 0 := mul_ne_zero hd.hc hd.hQv
  rw [polar_plane_left, polar_self_zero, hd.polar_xv_v] at h1
  rw [polar_plane_left, hd.hB, polar_self_zero] at h2
  simp only [mul_zero, zero_add, add_zero] at h1 h2
  exact ⟨(mul_eq_zero.1 h2).resolve_right hβ, (mul_eq_zero.1 h1).resolve_right hβ⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem PlaneData.plane_aniso (hd : PlaneData Q x v c) {u : V} (hu : u ∈ plane x v) (h : Q u = 0) :
    u = 0 := by
  obtain ⟨s, t, rfl⟩ := mem_plane.1 hu
  obtain ⟨rfl, rfl⟩ := form_aniso hd.hQ hd.hB hd.hQv hd.hroot h
  simp

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.plane_reg (hd : PlaneData Q x v c) : RegOn Q (plane x v) := by
  intro u hu hperp
  obtain ⟨s, t, rfl⟩ := mem_plane.1 hu
  have hv : v ∈ plane x v := mem_plane.2 ⟨1, 0, by simp⟩
  have hxv : x v ∈ plane x v := mem_plane.2 ⟨0, 1, by simp⟩
  obtain ⟨rfl, rfl⟩ := hd.eq_zero_of_polar (hperp v hv) (hperp (x v) hxv)
  simp

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem PlaneData.finrank_plane (hd : PlaneData Q x v c) :
    finrank K (plane x v) = 2 := by
  have hli : LinearIndependent K ![v, x v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hq : Q (s • v + t • x v) = 0 := by
      rw [hst]
      exact QuadraticMap.map_zero Q
    exact form_aniso hd.hQ hd.hB hd.hQv hd.hroot hq
  have hspan : Submodule.span K (Set.range ![v, x v]) = plane x v := by
    unfold plane
    congr 1
    ext w
    simp
    tauto
  rw [← hspan, finrank_span_eq_card hli]
  simp

@[expose] def orthPart (Q : QuadraticForm K V) (U : Submodule K V) (a b : V) : Submodule K V where
  carrier := {u | u ∈ U ∧ polar Q u a = 0 ∧ polar Q u b = 0}
  add_mem' := by
    rintro u u' ⟨hu, h1, h2⟩ ⟨hu', h3, h4⟩
    exact ⟨U.add_mem hu hu', by rw [QuadraticMap.polar_add_left, h1, h3, add_zero],
      by rw [QuadraticMap.polar_add_left, h2, h4, add_zero]⟩
  zero_mem' := ⟨U.zero_mem, QuadraticMap.polar_zero_left _ _, QuadraticMap.polar_zero_left _ _⟩
  smul_mem' := by
    rintro r u ⟨hu, h1, h2⟩
    exact ⟨U.smul_mem r hu, by rw [QuadraticMap.polar_smul_left, h1, smul_zero],
      by rw [QuadraticMap.polar_smul_left, h2, smul_zero]⟩

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.decomp (hd : PlaneData Q x v c) (u : V) :
    ∃ y ∈ plane x v, polar Q (u - y) v = 0 ∧ polar Q (u - y) (x v) = 0 := by
  have hβ : c * Q v ≠ 0 := mul_ne_zero hd.hc hd.hQv
  have hc0 := hd.hc
  have hq0 := hd.hQv
  refine ⟨(polar Q u (x v) / (c * Q v)) • v + (polar Q u v / (c * Q v)) • x v,
    mem_plane.2 ⟨_, _, rfl⟩, ?_, ?_⟩
  · rw [QuadraticMap.polar_sub_left, polar_plane_left, polar_self_zero, hd.polar_xv_v]
    field_simp
    ring
  · rw [QuadraticMap.polar_sub_left, polar_plane_left, hd.hB, polar_self_zero]
    field_simp
    ring

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_plane_orth {U : Submodule K V} {b : V}
    (hb : b ∈ orthPart Q U v (x v)) {a : V} (ha : a ∈ plane x v) : polar Q a b = 0 := by
  obtain ⟨s, t, rfl⟩ := mem_plane.1 ha
  rw [polar_plane_left, QuadraticMap.polar_comm Q v b, QuadraticMap.polar_comm Q (x v) b,
    hb.2.1, hb.2.2]
  simp

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.disjoint_orthPart (hd : PlaneData Q x v c) (U : Submodule K V) :
    Disjoint (plane x v) (orthPart Q U v (x v)) := by
  rw [Submodule.disjoint_def]
  intro u hu hu'
  obtain ⟨s, t, rfl⟩ := mem_plane.1 hu
  obtain ⟨rfl, rfl⟩ := hd.eq_zero_of_polar hu'.2.1 hu'.2.2
  simp

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.sup_orthPart (hd : PlaneData Q x v c) {U : Submodule K V} (hv : v ∈ U)
    (hxv : x v ∈ U) : plane x v ⊔ orthPart Q U v (x v) = U := by
  have hP : plane x v ≤ U := Submodule.span_le.2 (by
    intro w hw
    rcases hw with rfl | rfl
    · exact hv
    · exact hxv)
  refine le_antisymm (sup_le hP fun u hu => hu.1) fun u hu => ?_
  obtain ⟨y, hy, h1, h2⟩ := hd.decomp u
  have hyU : y ∈ U := hP hy
  have hz : u - y ∈ orthPart Q U v (x v) := ⟨U.sub_mem hu hyU, h1, h2⟩
  have : u = y + (u - y) := by abel
  rw [this]
  exact Submodule.add_mem_sup hy hz

omit [Finite K] in
theorem PlaneData.finrank_orthPart (hd : PlaneData Q x v c) {U : Submodule K V} (hv : v ∈ U)
    (hxv : x v ∈ U) : finrank K U = 2 + finrank K (orthPart Q U v (x v)) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (plane x v) (orthPart Q U v (x v))
  rw [hd.sup_orthPart hv hxv, (hd.disjoint_orthPart U).eq_bot, finrank_bot, hd.finrank_plane] at h1
  omega

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem plane_le {U : Submodule K V} (hv : v ∈ U) (hxv : x v ∈ U) : plane x v ≤ U :=
  Submodule.span_le.2 (by
    intro w hw
    rcases hw with rfl | rfl
    · exact hv
    · exact hxv)

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.orthPart_invariant (hx : OddOrderIsometry Q p x) (hd : PlaneData Q x v c)
    {U : Submodule K V} (hxU : ∀ u ∈ U, x u ∈ U) {u : V} (hu : u ∈ orthPart Q U v (x v)) :
    x u ∈ orthPart Q U v (x v) := by
  refine ⟨hxU u hu.1, ?_, ?_⟩
  · have hsymm : x.symm v = x v + c • v := by
      rw [LinearEquiv.symm_apply_eq, map_add, map_smul, hd.hxx]
      have h := vec_add_self K (c • x v)
      calc v = v + (c • x v + c • x v) := by rw [h, add_zero]
        _ = c • x v + v + c • x v := by abel
    rw [hx.polar_apply, hsymm, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      hu.2.2, hu.2.1]
    simp
  · rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem]
    exact hu.2.1

omit [Finite K] [FiniteDimensional K V] in
theorem PlaneData.orthPart_reg (hd : PlaneData Q x v c) {U : Submodule K V} (hreg : RegOn Q U)
    (hv : v ∈ U) (hxv : x v ∈ U) : RegOn Q (orthPart Q U v (x v)) := by
  intro u hu hperp
  refine hreg u hu.1 fun w hw => ?_
  obtain ⟨y, hy, h1, h2⟩ := hd.decomp w
  have hyU : y ∈ U := plane_le hv hxv hy
  have hz : w - y ∈ orthPart Q U v (x v) := ⟨U.sub_mem hw hyU, h1, h2⟩
  have e1 : polar Q u y = 0 := by
    obtain ⟨s, t, rfl⟩ := mem_plane.1 hy
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      hu.2.1, hu.2.2]
    simp
  have e2 : polar Q u (w - y) = 0 := hperp _ hz
  calc polar Q u w = polar Q u (y + (w - y)) := by congr 1; abel
    _ = 0 := by rw [QuadraticMap.polar_add_right, e1, e2, add_zero]

end PlaneData

section TypeSect

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem nondegenerate_of_regOn {U : Submodule K V} (h : RegOn Q U) :
    (polarBilin (Q.comp U.subtype)).Nondegenerate := by
  have key : ∀ a b : U, polarBilin (Q.comp U.subtype) a b = polar Q (a : V) (b : V) := by
    intro a b
    rw [QuadraticMap.polarBilin_apply_apply]
    simp [QuadraticMap.polar, QuadraticMap.comp_apply]
  constructor
  · intro a ha
    refine Subtype.ext (h a a.2 fun w hw => ?_)
    have := ha ⟨w, hw⟩
    rwa [key] at this
  · intro b hb
    refine Subtype.ext (h b b.2 fun w hw => ?_)
    have := hb ⟨w, hw⟩
    rw [key] at this
    rw [QuadraticMap.polar_comm]
    exact this

noncomputable def isometryOfEq (Q : QuadraticForm K V) {A B : Submodule K V} (h : A = B) :
    (Q.comp A.subtype).IsometryEquiv (Q.comp B.subtype) where
  toLinearEquiv := LinearEquiv.ofEq A B h
  map_app' v := by
    subst h
    rfl

theorem isPlusType_iff_even_of_fixedFree (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) :
    ∀ (k : ℕ) (U : Submodule K V), (∀ u ∈ U, x u ∈ U) → RegOn Q U → (∀ u ∈ U, x u = u → u = 0) →
      finrank K U = 2 * k → (IsPlusType (Q.comp U.subtype) ↔ Even k) := by
  intro k
  induction k with
  | zero =>
    intro U _ _ _ hdim
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    subst hU
    refine ⟨fun _ => ⟨0, rfl⟩, fun _ => ⟨⊥, ?_, ?_⟩⟩
    · simp
    · intro w hw
      rw [Submodule.mem_bot] at hw
      rw [hw]
      exact QuadraticMap.map_zero _
  | succ k ih =>
    intro U hxU hreg hfix hdim
    have hU : U ≠ ⊥ := by
      rintro rfl
      simp at hdim
    obtain ⟨v, c, hvU, hc, hQv, hxx, hB, hroot⟩ := exists_plane hx hp hp2 hpq hxU hreg hfix hU
    have hQ : Q (x v) = Q v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx.mem v
    have hd : PlaneData Q x v c := ⟨hc, hQv, hxx, hQ, hB, hroot⟩
    have hxvU : x v ∈ U := hxU v hvU
    have hdim' : finrank K (orthPart Q U v (x v)) = 2 * k := by
      have := hd.finrank_orthPart hvU hxvU
      omega
    have hreg' := hd.orthPart_reg hreg hvU hxvU
    have hinv' : ∀ u ∈ orthPart Q U v (x v), x u ∈ orthPart Q U v (x v) := fun u hu =>
      hd.orthPart_invariant hx hxU hu
    have hfix' : ∀ u ∈ orthPart Q U v (x v), x u = u → u = 0 := fun u hu h => hfix u hu.1 h
    have ih' := ih _ hinv' hreg' hfix' hdim'
    have hnp : ¬ IsPlusType (Q.comp (plane x v).subtype) := by
      rintro ⟨W, hW, hWs⟩
      have h1 : finrank K W = 1 := by
        have := hd.finrank_plane
        omega
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (by rintro rfl; simp at h1 : W ≠ ⊥)
      have h2 := hWs w hwW
      rw [QuadraticMap.comp_apply] at h2
      exact hw0 (Subtype.ext (hd.plane_aniso w.2 h2))
    have hPU : plane x v ≤ U := plane_le hvU hxvU
    by_cases hk : k = 0
    · subst hk
      have hbot : orthPart Q U v (x v) = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
      have hUP : U = plane x v := by
        rw [← hd.sup_orthPart hvU hxvU, hbot, sup_bot_eq]
      rw [isPlusType_congr (isometryOfEq Q hUP)]
      exact ⟨fun h => absurd h hnp, fun h => absurd h (by decide)⟩
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
      have eU : (Q.comp U.subtype).IsometryEquiv (Q.comp (plane x v ⊔ orthPart Q U v (x v)).subtype) :=
        isometryOfEq Q (hd.sup_orthPart hvU hxvU).symm
      have eS := isometryEquivSup Q (plane x v) (orthPart Q U v (x v)) (hd.disjoint_orthPart U)
        (fun a ha b hb => polar_plane_orth hb ha)
      rw [isPlusType_congr (eU.trans eS),
        isPlusType_prod_iff (nondegenerate_of_regOn hd.plane_reg) (nondegenerate_of_regOn hreg')
          (d₁ := 1) (d₂ := k) le_rfl hk1 hd.finrank_plane hdim', ih']
      constructor
      · intro h
        rw [Nat.even_add_one]
        intro hk'
        exact hnp (h.2 hk')
      · intro h
        rw [Nat.even_add_one] at h
        exact ⟨fun hp' => absurd hp' hnp, fun hk' => absurd hk' h⟩

end TypeSect

end Plane

end CFSG.RankThree.PartOne.K159
