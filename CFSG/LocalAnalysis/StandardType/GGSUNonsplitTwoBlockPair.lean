module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockFour
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockIso

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.RankThree.PartOne.OddIso
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

section General

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem aeval_eq_of_eqOn {X Y : Module.End K V} {U : Submodule K V} (hX : ∀ u ∈ U, X u ∈ U)
    (hXY : ∀ u ∈ U, X u = Y u) (P : K[X]) {u : V} (hu : u ∈ U) : aeval X P u = aeval Y P u := by
  have hpow : ∀ k : ℕ, ∀ u ∈ U, (X ^ k) u = (Y ^ k) u := by
    intro k
    induction k with
    | zero => intro u _; rfl
    | succ k ih =>
      intro u hu
      rw [pow_succ, Module.End.mul_apply, ih _ (hX u hu), pow_succ, Module.End.mul_apply,
        hXY u hu]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hP, hQ]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, hpow k u hu]

theorem range_pow_sub_one_le (Y : Module.End K V) (j : ℕ) :
    LinearMap.range (Y ^ j - 1) ≤ LinearMap.range (Y - 1) := by
  rw [← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _

theorem exists_monic_of_irreducible {g : K[X]} (hg : Irreducible g) :
    ∃ g' : K[X], Irreducible g' ∧ g'.Monic ∧ g' ∣ g ∧ ∀ X : Module.End K V,
      LinearMap.ker (aeval X g') = LinearMap.ker (aeval X g) := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have hc : g.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)
  refine ⟨g * C g.leadingCoeff⁻¹, (irreducible_mul_isUnit (isUnit_C.mpr hc.isUnit)).mpr hg,
    monic_mul_leadingCoeff_inv hg0, ⟨C g.leadingCoeff, by
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hg0), C_1, mul_one]⟩,
    fun X => ?_⟩
  ext v
  simp only [LinearMap.mem_ker, map_mul, aeval_C, Module.End.mul_apply,
    Module.algebraMap_end_apply, map_smul, smul_eq_zero, hc, false_or]

end General

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

@[expose] noncomputable def toUnit (g : ↥(unitarySU 2 f K n)) :
    LinearMap.GeneralLinearGroup K (Fin n → K) :=
  ⟨lin g, lin g⁻¹, by rw [← lin_mul, mul_inv_cancel, lin_one],
    by rw [← lin_mul, inv_mul_cancel, lin_one]⟩

theorem coe_toUnit (g : ↥(unitarySU 2 f K n)) :
    ((toUnit g : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) =
      lin g := rfl

theorem unitaryPrimaryData_toUnit (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A)
    {g : ↥(unitarySU 2 f K n)} (hg : g ∈ A) :
    UnitaryPrimaryData h.bar (stdHermForm h n) (toUnit g) where
  invol := h.bar_bar
  symm := stdHermForm_isSymm h n
  sep := stdHermForm_separatingLeft h n
  isom := (isometry_lin h g)
  squarefree := by
    refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - 1) ?_ ?_
    · have := (separable_X_pow_sub_C (1 : K) (hA.natCast_ne_zero h) one_ne_zero).squarefree
      rwa [map_one] at this
    · rw [coe_toUnit, map_sub, map_pow, aeval_X, map_one, hA.lin_pow hg, sub_self]

theorem mem_primaryFactors_of_ker {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {X : Module.End K V} {g : K[X]} (hg : Irreducible g) (hgm : g.Monic) {w : V} (hw0 : w ≠ 0)
    (hw : aeval X g w = 0) : g ∈ primaryFactors X := by
  refine mem_primaryFactors.mpr ⟨hg, hgm, ?_⟩
  by_contra hnd
  obtain ⟨a, b, hab⟩ := hg.coprime_iff_not_dvd.mpr hnd
  apply hw0
  have h1 : aeval X (a * g + b * minpoly K X) w = w := by rw [hab, map_one, Module.End.one_apply]
  rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, add_zero, Module.End.mul_apply, hw,
    map_zero] at h1
  exact h1.symm

omit [Field K] in
theorem le_range_of_fpf {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {U : Submodule K V} [FiniteDimensional K U] {Y Z : Module.End K V} (hYU : ∀ u ∈ U, Y u ∈ U)
    (hfix : ∀ u ∈ U, Y u = u → u = 0) (hZY : ∀ u ∈ U, Z u = Y u) :
    U ≤ LinearMap.range (Z - 1) := by
  have hT : ∀ u ∈ U, (Y - 1) u ∈ U := fun u hu => by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact U.sub_mem (hYU u hu) hu
  set T := (Y - 1).restrict hT with hTdef
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 := congrArg Subtype.val hu
    rw [LinearMap.coe_restrict_apply, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_zero] at h1
    exact Subtype.ext (hfix u u.2 (sub_eq_zero.mp h1))
  intro u hu
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨u, hu⟩
  refine ⟨w, ?_⟩
  have h1 : (Y - 1) (w : V) = u := congrArg Subtype.val hw
  rw [LinearMap.sub_apply, Module.End.one_apply] at h1
  rw [LinearMap.sub_apply, Module.End.one_apply, hZY w w.2, h1]

theorem two_le_finrank_rng (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A)
    {y : ↥(unitarySU 2 f K n)} (hy : y ∈ A) (hy1 : y ≠ 1) : 2 ≤ finrank K (rng y) := by
  have : CharP K 2 := h.charP
  set B := stdHermForm h n with hB
  have hnd := nondegOn_rng (h := h) hA hy
  have hne : rng y ≠ ⊥ := by
    intro hbot
    apply hy1
    refine eq_of_lin_apply fun v => ?_
    have h1 : (lin y - 1) v ∈ rng y := ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    rw [h1, lin_one]
    rfl
  by_contra hlt
  push Not at hlt
  have h1 : finrank K (rng y) = 1 := by
    have := Submodule.finrank_eq_zero.not.mpr hne
    omega
  obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨c, hc⟩ := hvspan ⟨lin y v, rng_inv hA hy hy v v.2⟩
  have hyv : lin y v = c • (v : Fin n → K) := (congrArg Subtype.val hc).symm
  have hv0' : (v : Fin n → K) ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hpow : ∀ k : ℕ, (lin y ^ k) v = c ^ k • (v : Fin n → K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hyv, smul_smul, pow_succ]
  have hcp : c ^ p = 1 := by
    have h2 := hpow p
    rw [hA.lin_pow hy, Module.End.one_apply] at h2
    have h3 : (c ^ p - 1) • (v : Fin n → K) = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0')
  have hBv : B v v ≠ 0 := by
    intro h0
    refine hv0' (hnd v v.2 fun m hm => ?_)
    obtain ⟨c', hc'⟩ := hvspan ⟨m, hm⟩
    have hm' : m = c' • (v : Fin n → K) := (congrArg Subtype.val hc').symm
    rw [hm', LinearMap.map_smulₛₗ₂, h0, smul_zero]
  have hcq : c ^ (2 ^ f + 1) = 1 := by
    have h2 := isometry_lin h y v v
    rw [hyv, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc] at h2
    have h3 : h.bar c * c = 1 := by
      have h4 : (h.bar c * c - 1) * B v v = 0 := by rw [sub_mul, h2, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hBv)
    rw [UnitaryFieldData.bar_apply] at h3
    rw [pow_succ]
    exact h3
  have hc1 : c = 1 := by
    have hcop : p.gcd (2 ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hA.not_dvd
    have h5 := pow_gcd_eq_one.mpr ⟨hcp, hcq⟩
    rwa [hcop, pow_one] at h5
  rw [hc1, one_smul] at hyv
  exact hv0' (eq_zero_of_mem_rng h hA hy v.2 hyv)

theorem exists_twoCopy (h : UnitaryFieldData 2 f K) (hA : MaxElemAb p A)
    (hcard : p ^ 4 ≤ Nat.card A) :
    ∃ (x a₁ a₂ : ↥(unitarySU 2 f K n)) (U₁ U₂ : Submodule K (Fin n → K))
      (θ : (Fin n → K) →ₗ[K] (Fin n → K)),
      x ∈ A ∧ a₁ ∈ A ∧ a₂ ∈ A ∧
      NondegOn (stdHermForm h n) U₁ ∧ NondegOn (stdHermForm h n) U₂ ∧
      (∀ u ∈ U₁, ∀ w ∈ U₂, stdHermForm h n u w = 0 ∧ stdHermForm h n w u = 0) ∧
      2 ≤ finrank K U₁ ∧ 4 * finrank K U₁ ≤ n ∧
      (∀ u ∈ U₁, lin x u ∈ U₁) ∧ (∀ u ∈ U₂, lin x u ∈ U₂) ∧
      (∀ v ∈ (U₁ ⊔ U₂).orthogonalBilin (stdHermForm h n), lin x v = v) ∧
      U₁ ≤ LinearMap.range (lin x - 1) ∧ U₂ ≤ LinearMap.range (lin x - 1) ∧
      (∀ u ∈ U₁, θ u ∈ U₂) ∧
      (∀ u ∈ U₁, ∀ v ∈ U₁, stdHermForm h n (θ u) (θ v) = stdHermForm h n u v) ∧
      (∀ u ∈ U₁, θ (lin x u) = lin x (θ u)) ∧ (∀ w ∈ U₂, ∃ u ∈ U₁, θ u = w) ∧
      ∀ c ∈ A, (∀ v ∈ (U₁ ⊔ U₂).orthogonalBilin (stdHermForm h n), lin c v = v) →
        ∃ i j : ℕ, c = a₁ ^ i * a₂ ^ j := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hp0 : 0 < p := hA.prime.pos
  have hpK := hA.natCast_ne_zero h
  set B := stdHermForm h n with hB
  obtain ⟨y₁, y₂, hy₁, hy₂, h4, hgen⟩ := exists_two_pieces (h := h) hA hcard
  set U₁ := rng y₁ with hU₁
  set U₂ := rng y₂ with hU₂
  have hnd₁ : NondegOn B U₁ := hy₁.nondegOn hA
  have hnd₂ : NondegOn B U₂ := hy₂.nondegOn hA
  have horth : ∀ u ∈ U₁, ∀ w ∈ U₂, B u w = 0 ∧ B w u = 0 := fun u hu w hw =>
    ⟨(hy₂.orth w hw u hu).2, (hy₂.orth w hw u hu).1⟩
  have hy₁U₂ : ∀ w ∈ U₂, lin y₁ w = w := fun w hw =>
    triv_orth_rng hA hy₁.mem w (Submodule.mem_orthogonalBilin.mpr fun u hu => (horth u hu w hw).1)
  have hfixpow : ∀ {Y : Module.End K (Fin n → K)} {U : Submodule K (Fin n → K)},
      (∀ u ∈ U, Y u = u) → ∀ k : ℕ, ∀ u ∈ U, (Y ^ k) u = u := by
    intro Y U hY k u hu
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, Module.End.mul_apply, hY u hu, ih]
  have hy₁1 : lin y₁ ≠ 1 := fun h1 => hy₁.ne_one (lin_injective (h1.trans lin_one.symm))
  have hy₂1 : lin y₂ ≠ 1 := fun h1 => hy₂.ne_one (lin_injective (h1.trans lin_one.symm))
  obtain ⟨g₀, hg₀, hg₀d, hg₀k⟩ :=
    OrdPNS.exists_irreducible_ker_ne_bot hA.prime (hA.lin_pow hy₁.mem) hy₁1
  obtain ⟨g, hg, hgm, hgg₀, hker⟩ := exists_monic_of_irreducible (V := Fin n → K) hg₀
  have : Fact (Irreducible g) := ⟨hg⟩
  have hgd : g ∣ cyclotomic p K := hgg₀.trans hg₀d
  have hgk₁ : LinearMap.ker (aeval (lin y₁) g) ≠ ⊥ := by rw [hker]; exact hg₀k
  obtain ⟨j, hj⟩ := NSFrame.exists_pow_ker_ne_bot hA.prime hpK hgd (hA.lin_pow hy₂.mem) hy₂1
  have hjp : ¬ p ∣ j := by
    rintro ⟨t, rfl⟩
    apply hj
    rw [pow_mul, hA.lin_pow hy₂.mem, one_pow]
    refine le_bot_iff.mp ((ker_aeval_le_range hpK hA.prime hgd).trans ?_)
    rw [sub_self, LinearMap.range_zero]
  obtain ⟨j', -, hjj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hA.prime).mpr hjp).symm hA.prime.one_lt
  have hy₂pow : (lin y₂ ^ j) ^ j' = lin y₂ := by
    rw [← pow_mul, ← Nat.mod_add_div (j * j') p, hjj', pow_add, pow_mul, hA.lin_pow hy₂.mem,
      one_pow, mul_one, pow_one]
  set x := y₁ * y₂ ^ j with hx
  have hxA : x ∈ A := A.mul_mem hy₁.mem (A.pow_mem hy₂.mem j)
  have hlinx : lin x = lin y₁ * lin y₂ ^ j := by rw [hx, lin_mul, SUTB.lin_pow]
  have hinv₁ : ∀ u ∈ U₁, lin x u ∈ U₁ := rng_inv hA hy₁.mem hxA
  have hinv₂ : ∀ u ∈ U₂, lin x u ∈ U₂ := rng_inv hA hy₂.mem hxA
  have hxU₁ : ∀ u ∈ U₁, lin x u = lin y₁ u := fun u hu => by
    rw [hlinx, Module.End.mul_apply, hfixpow hy₂.triv j u hu]
  have hU₂y₂ : ∀ w ∈ U₂, (lin y₂ ^ j) w ∈ U₂ := fun w hw => by
    rw [← SUTB.lin_pow]
    exact rng_inv hA hy₂.mem (A.pow_mem hy₂.mem j) w hw
  have hxU₂ : ∀ w ∈ U₂, lin x w = (lin y₂ ^ j) w := fun w hw => by
    rw [hlinx, Module.End.mul_apply, hy₁U₂ _ (hU₂y₂ w hw)]
  have hxM : ∀ v ∈ (U₁ ⊔ U₂).orthogonalBilin B, lin x v = v := by
    intro v hv
    have hv₁ := triv_orth_rng hA hy₁.mem v (orth_anti le_sup_left hv)
    have hv₂ := triv_orth_rng hA hy₂.mem v (orth_anti le_sup_right hv)
    rw [hlinx, Module.End.mul_apply, hfixpow (U := Submodule.span K {v}) (fun u hu => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul, hv₂]) j v (Submodule.mem_span_singleton_self v), hv₁]
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hgk₁
  have hw₁U : w₁ ∈ U₁ := ker_aeval_le_range hpK hA.prime hgd hw₁
  have hw₁x : aeval (lin x) g w₁ = 0 := by
    rw [aeval_eq_of_eqOn hinv₁ hxU₁ g hw₁U]
    exact LinearMap.mem_ker.mp hw₁
  obtain ⟨w₂, hw₂, hw₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hj
  have hw₂U : w₂ ∈ U₂ :=
    range_pow_sub_one_le (lin y₂) j (ker_aeval_le_range hpK hA.prime hgd hw₂)
  have hw₂x : aeval (lin x) g w₂ = 0 := by
    rw [aeval_eq_of_eqOn hinv₂ hxU₂ g hw₂U]
    exact LinearMap.mem_ker.mp hw₂
  have hgx : g ∈ primaryFactors (lin x) := mem_primaryFactors_of_ker hg hgm hw₁0 hw₁x
  have hpowx : ∀ {U : Submodule K (Fin n → K)} {Y : Module.End K (Fin n → K)},
      (∀ u ∈ U, lin x u ∈ U) → (∀ u ∈ U, lin x u = Y u) → ∀ k : ℕ, ∀ u ∈ U,
        (Y ^ k) u = (lin x ^ k) u := by
    intro U Y hU hY k u hu
    have := aeval_eq_of_eqOn hU hY (X ^ k) hu
    rw [map_pow, aeval_X, map_pow, aeval_X] at this
    exact this.symm
  have hmin₁ : ∀ W : Submodule K (Fin n → K), W ≤ U₁ → W ≠ ⊥ → NondegOn B W →
      (∀ w ∈ W, lin x w ∈ W) → W = U₁ := by
    intro W hW hW0 hWnd hWx
    refine hy₁.minimal W hW hW0 hWnd fun a ha w hw => ?_
    obtain ⟨k, hk⟩ := hy₁.cyc a ha
    rw [hk w (hW hw), SUTB.lin_pow, hpowx hinv₁ hxU₁ k w (hW hw)]
    exact invariant_pow hWx k w hw
  have hmin₂ : ∀ W : Submodule K (Fin n → K), W ≤ U₂ → W ≠ ⊥ → NondegOn B W →
      (∀ w ∈ W, lin x w ∈ W) → W = U₂ := by
    intro W hW hW0 hWnd hWx
    refine hy₂.minimal W hW hW0 hWnd fun a ha w hw => ?_
    obtain ⟨k, hk⟩ := hy₂.cyc a ha
    rw [hk w (hW hw), SUTB.lin_pow, ← hy₂pow, ← pow_mul, hpowx hinv₂ hxU₂ _ w (hW hw)]
    exact invariant_pow hWx _ w hw
  obtain ⟨θ, hθU, hθB, hθx, hθs⟩ := exists_isometry_of_pieces h
    (unitaryPrimaryData_toUnit h hA hxA) hp0 (hA.lin_pow hxA) hnd₁ hnd₂ hinv₁ hinv₂ hmin₁ hmin₂
    hgx ⟨w₁, hw₁U, hw₁0, hw₁x⟩ ⟨w₂, hw₂U, hw₂0, hw₂x⟩
  have hR₁ : U₁ ≤ LinearMap.range (lin x - 1) :=
    le_range_of_fpf (rng_inv hA hy₁.mem hy₁.mem)
      (fun u hu hyu => eq_zero_of_mem_rng h hA hy₁.mem hu hyu) hxU₁
  have hR₂ : U₂ ≤ LinearMap.range (lin x - 1) :=
    le_range_of_fpf hU₂y₂ (fun u hu hyu => by
      refine eq_zero_of_mem_rng h hA hy₂.mem hu ?_
      rw [← hy₂pow]
      exact hfixpow (U := Submodule.span K {u}) (fun v hv => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul, hyu]) j' u (Submodule.mem_span_singleton_self u)) hxU₂
  exact ⟨x, y₁, y₂, U₁, U₂, θ, hxA, hy₁.mem, hy₂.mem, hnd₁, hnd₂, horth,
    two_le_finrank_rng h hA hy₁.mem hy₁.ne_one, h4, hinv₁, hinv₂, hxM, hR₁, hR₂, hθU, hθB, hθx,
    hθs, hgen⟩

end SUTB

end CFSG.StandardType
