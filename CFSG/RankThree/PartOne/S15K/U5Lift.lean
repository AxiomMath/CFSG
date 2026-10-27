module

public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityBlock
public import CFSG.LinearAlgebra.OddSolvableUnitary.ExtraspecialModule
public import CFSG.RankThree.PartOne.S15K.CommonEigen

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K]

section Norm

variable (h : UnitaryFieldData 2 f K)

include h in
theorem natCast_ne_zero_of_char_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : K) ≠ 0 := by
  have : CharP K 2 := h.charP
  intro h0
  have := (CharP.cast_eq_zero_iff K 2 p).mp h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm

theorem not_dvd_pred_of_dvd_succ {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hpq : p ∣ q + 1) : ¬ p ∣ q - 1 := by
  intro hd
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq hd
  have : (q + 1) - (q - 1) = 2 := by omega
  rw [this] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem bar_mul_eq_one_of_pow_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1) {μ c : K}
    (hμ : μ ^ p = c) (hc : h.bar c * c = 1) : h.bar μ * μ = 1 := by
  have := h.finite
  have := Fintype.ofFinite K
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hμ
    rw [← hμ] at hc
    simp at hc
  have h1 : (h.bar μ * μ) ^ p = 1 := by
    rw [mul_pow, ← map_pow, hμ, hc]
  have hcard : Fintype.card K = 2 ^ (2 * f) := by rw [← Nat.card_eq_fintype_card, h.card]
  have h2 : (h.bar μ * μ) ^ (2 ^ f - 1) = 1 := by
    have hn : h.bar μ * μ = μ ^ (2 ^ f + 1) := by rw [UnitaryFieldData.bar_apply, pow_succ]
    rw [hn, ← pow_mul]
    have e : (2 ^ f + 1) * (2 ^ f - 1) = Fintype.card K - 1 := by
      rw [hcard, two_mul, pow_add]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hq
      rw [hk]
      simp only [Nat.add_sub_cancel_left]
      have : 1 + k + 1 = k + 2 := by omega
      rw [show 1 + k = k + 1 by omega, show (k + 1 + 1) = k + 2 by omega]
      have e2 : (k + 1) * (k + 1) = (k + 2) * k + 1 := by ring
      rw [e2, Nat.add_sub_cancel]
    rw [e]
    exact FiniteField.pow_card_sub_one_eq_one μ hμ0
  have hcop : Nat.Coprime p (2 ^ f - 1) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (not_dvd_pred_of_dvd_succ hp hp2 hq hpq)
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

end Norm

section Primary

variable (h : UnitaryFieldData 2 f K)

include h in
theorem aeval_X_pow_sub_C_toLinU {p : ℕ} (g : primeFormUnitary h (idGram K 5)) {c : Kˣ}
    (hgp : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c) :
    aeval ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) (X ^ p - C (c : K)) = 0 := by
  have hMp : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ p =
      algebraMap K (Matrix (Fin 5) (Fin 5) K) c := by
    have h1 : (((g : GL (Fin 5) K) ^ p : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ^ p := Units.val_pow_eq_pow_val _ _
    rw [← h1, hgp, GeneralLinearGroup.coe_scalar]
    rfl
  have hX : ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) = Matrix.toLinAlgEquiv' ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    (Matrix.toLin'_apply' _).symm.trans (KCLinComm.toLinAlgEquiv'_eq_toLin' _).symm
  rw [hX]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [← map_pow, hMp, AlgEquiv.commutes, sub_self]

include h in
theorem unitaryPrimaryData_of_pow_scalar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (g : primeFormUnitary h (idGram K 5)) {c : Kˣ}
    (hgp : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c) :
    UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 g) := by
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar (natCast_ne_zero_of_char_two h hp hp2) hgp
  refine ⟨h.bar_bar, idForm_isSymm h 5, idForm_separatingLeft h 5, toLinU_mem g, ?_⟩
  have hX : ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) = Matrix.toLin' ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
    (Matrix.toLin'_apply' _).symm
  rw [hX]
  exact hsq

include h in
theorem linear_of_mult_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    (g : primeFormUnitary h (idGram K 5)) {c : Kˣ} (hc : c ^ (2 ^ f + 1) = 1)
    (hgp : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c)
    (x : Module.End K (Fin 5 → K))
    (hx : x = ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K))) (a : primaryFactors x)
    (ha2 : 2 ≤ primaryMultiplicity x (a : K[X])) :
    ∃ μ : K, (a : K[X]) = X - C μ ∧ μ ^ p = (c : K) ∧ h.bar μ * μ = 1 := by
  classical
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  have HU := unitaryPrimaryData_of_pow_scalar h hp hp2 g hgp
  have hsq : Squarefree (minpoly K x) := by rw [hx]; exact HU.squarefree
  have hae : aeval x (X ^ p - C (c : K)) = 0 := by rw [hx]; exact aeval_X_pow_sub_C_toLinU h g hgp
  have hirr : Irreducible (a : K[X]) := irreducible_of_mem_primaryFactors a.2
  have hmonic : (a : K[X]).Monic := (mem_primaryFactors.mp a.2).2.1
  have hdvd : (a : K[X]) ∣ X ^ p - C (c : K) :=
    (mem_primaryFactors.mp a.2).2.2.trans (minpoly.dvd K x hae)
  have hdeg : (a : K[X]).natDegree ≤ 2 := by
    have hfin := finrank_eq_sum_degree_mul_multiplicity (x := x) hsq
    have hdim : Module.finrank K (Fin 5 → K) = 5 := by simp
    have hsum : (a : K[X]).natDegree * primaryMultiplicity x (a : K[X]) ≤ 5 := by
      have h1 := Finset.single_le_sum
        (f := fun b : primaryFactors x => (b : K[X]).natDegree * primaryMultiplicity x (b : K[X]))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [← hfin, hdim] at h1
      exact h1
    nlinarith
  have hcn : h.bar (c : K) * c = 1 := by
    have := (pow_succ_eq_one_iff_norm h c).mp hc
    rw [UnitaryFieldData.norm] at this
    rw [mul_comm]
    exact this
  have hpK : p ∣ Nat.card K - 1 := by
    rw [h.card]
    have h1 : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hq
      rw [two_mul, pow_add, hk]
      simp only [Nat.add_sub_cancel_left]
      have e2 : (1 + k) * (1 + k) = (1 + k + 1) * k + 1 := by ring
      rw [e2, Nat.add_sub_cancel]
    rw [h1]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp hpK
  by_cases hroot : ∃ ω : K, ω ^ p = c
  · obtain ⟨ω, hω⟩ := hroot
    rw [X_pow_sub_C_eq_prod hζ hp.pos hω] at hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hirr.prime _).mp hdvd
    have heq := eq_of_monic_of_associated hmonic (monic_X_sub_C _)
      (Irreducible.associated_of_dvd hirr (irreducible_X_sub_C _) hi)
    have hμ : (ζ ^ i * ω) ^ p = c := by
      rw [mul_pow, ← pow_mul, mul_comm i p, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hω]
    exact ⟨ζ ^ i * ω, heq, hμ, bar_mul_eq_one_of_pow_eq h hp hp2 hpq hμ hcn⟩
  · push Not at hroot
    have hirr' := X_pow_sub_C_irreducible_of_prime hp hroot
    have heq := eq_of_monic_of_associated hmonic (monic_X_pow_sub_C _ hp.ne_zero)
      (Irreducible.associated_of_dvd hirr hirr' hdvd)
    rw [heq, natDegree_X_pow_sub_C] at hdeg
    omega

end Primary

section Glue

variable {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def glueEnd (π A : Module.End K V) (c : K) : Module.End K V :=
  (1 - π) + c • (A * π)

theorem glueEnd_apply (π A : Module.End K V) (c : K) (v : V) :
    glueEnd π A c v = v - π v + c • A (π v) := by
  simp [glueEnd, Module.End.mul_apply, sub_eq_add_neg, add_comm]

theorem glueEnd_mul {π A A' : Module.End K V} {c c' : K} (hππ : ∀ v, π (π v) = π v)
    (hA' : ∀ v, A' (π v) = π (A' v)) :
    glueEnd π A c * glueEnd π A' c' = glueEnd π (A * A') (c * c') := by
  refine LinearMap.ext fun v => ?_
  have h2 : π (A' (π v)) = A' (π v) := by rw [← hA' (π v), hππ]
  have hπw : π (v - π v + c' • A' (π v)) = c' • A' (π v) := by
    rw [map_add, map_sub, map_smul, hππ, h2]
    abel
  rw [Module.End.mul_apply, glueEnd_apply π A' c' v, glueEnd_apply π A c _, hπw,
    glueEnd_apply π (A * A') (c * c') v, map_smul, Module.End.mul_apply]
  module

theorem glueEnd_one {π : Module.End K V} : glueEnd π 1 1 = 1 := by
  refine LinearMap.ext fun v => ?_
  simp [glueEnd_apply]

theorem commute_glueEnd {π A y : Module.End K V} {c : K} (hπ : Commute y π) (hA : Commute y A) :
    Commute y (glueEnd π A c) := by
  unfold glueEnd
  exact (Commute.one_right y |>.sub_right hπ).add_right ((hA.mul_right hπ).smul_right c)

end Glue

section GlueForm

variable {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem glueEnd_isometry (B : V →ₛₗ[σ] V →ₗ[K] K) {π A : Module.End K V} {c : K}
    (hππ : ∀ v, π (π v) = π v) (hπB : ∀ v w, B (π v) w = B v (π w))
    (hA : ∀ v, A (π v) = π (A v)) (hAB : ∀ v w, B (A v) (A w) = B v w) (hc : σ c * c = 1)
    (v w : V) : B (glueEnd π A c v) (glueEnd π A c w) = B v w := by
  have hV1 : ∀ u w : V, B (π u) (w - π w) = 0 := fun u w => by
    rw [map_sub, hπB u w, hπB u (π w), hππ, sub_self]
  have hV2 : ∀ u w : V, B (u - π u) (π w) = 0 := fun u w => by
    rw [map_sub, LinearMap.sub_apply, hπB u (π w), hππ, sub_self]
  have e1 : ∀ (a b a' b' : V) (c₁ c₂ : K), B (a + c₁ • a') (b + c₂ • b') =
      B a b + c₂ * B a b' + σ c₁ * B a' b + σ c₁ * c₂ * B a' b' := by
    intro a b a' b' c₁ c₂
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring
  have e2 : ∀ a b a' b' : V, B (a + a') (b + b') = B a b + B a b' + B a' b + B a' b' := by
    intro a b a' b'
    simp only [map_add, LinearMap.add_apply]
    ring
  have hX1 : B (v - π v) (A (π w)) = 0 := by rw [hA w]; exact hV2 v (A w)
  have hX2 : B (A (π v)) (w - π w) = 0 := by rw [hA v]; exact hV1 (A v) w
  have hsplit : B v w = B (v - π v) (w - π w) + B (π v) (π w) := by
    conv_lhs => rw [← sub_add_cancel v (π v), ← sub_add_cancel w (π w)]
    rw [e2, hV2 v w, hV1 v w]
    ring
  rw [glueEnd_apply, glueEnd_apply, e1, hX1, hX2, hAB, hsplit]
  linear_combination (B (π v) (π w)) * hc

end GlueForm

section SpecialElem

open CFSG.RankThree.PartOne.KCUnitaryBlock

variable (h : UnitaryFieldData 2 f K)

include h in
theorem dualPoly_X_sub_C_eq {μ : K} (hμ : h.bar μ * μ = 1) :
    dualPoly h.bar (X - C μ) = X - C μ := by
  have hbar0 : h.bar μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ
    exact zero_ne_one hμ
  rw [dualPoly_X_sub_C hbar0]
  congr 2
  exact inv_eq_of_mul_eq_one_right hμ

include h in
theorem exists_specialBlock_mul_scalar {x : LinearMap.GeneralLinearGroup K (Fin 5 → K)}
    (HU : UnitaryPrimaryData h.bar (idForm h 5) x) {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ : K[X]) ∈ primaryFactors (x : Module.End K (Fin 5 → K)))
    (A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) (hA : A ∈ sesqUnitaryGroup (idForm h 5))
    (hAx : Commute (A : Module.End K (Fin 5 → K)) (x : Module.End K (Fin 5 → K))) {c : K}
    (hc0 : c ≠ 0) (hc : h.bar c * c = 1)
    (hcm : c ^ Module.finrank K (primaryComponent (x : Module.End K (Fin 5 → K)) (X - C μ)) =
      LinearMap.det ((A : Module.End K (Fin 5 → K)).restrict
        (fun _ hv => apply_mem_primaryComponent (a := X - C μ) hAx hv))) :
    ∃ s : LinearMap.GeneralLinearGroup K (Fin 5 → K),
      s ∈ specialBlock (idForm h 5) x (X - C μ) ∧
      ∀ v ∈ primaryComponent (x : Module.End K (Fin 5 → K)) (X - C μ),
        (A : Module.End K (Fin 5 → K)) v = (s : Module.End K (Fin 5 → K)) (c • v) := by
  classical
  set V := Fin 5 → K
  have hsq := HU.squarefree
  set π : Module.End K V := primaryProjection (x : Module.End K V) (X - C μ) with hπdef
  have hdual := dualPoly_X_sub_C_eq h hμ
  have hππ : ∀ v, π (π v) = π v := fun v => by
    have := congrArg (fun T : Module.End K V => T v) (primaryProjection_mul_self hsq ha)
    exact this
  have hπB : ∀ v w, idForm h 5 (π v) w = idForm h 5 v (π w) := by
    intro v w
    have h1 := hermAdjoint_spec HU.symm HU.sep π v w
    have h2 : hermAdjoint HU.symm HU.sep π = π := by
      have := adj_primaryProjection HU ha
      rw [hdual] at this
      exact this
    rw [h2] at h1
    exact h1
  have hπx : Commute (x : Module.End K V) π := (commute_aeval (Commute.refl _) _)
  have hπA : Commute (A : Module.End K V) π := commute_aeval hAx _
  have hπAinv : Commute ((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) π :=
    hπA.units_inv_left
  have hAπ : ∀ v, (A : Module.End K V) (π v) = π ((A : Module.End K V) v) := fun v =>
    congrArg (fun T : Module.End K V => T v) hπA.eq
  have hAinvπ : ∀ v, ((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (π v) =
      π (((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) := fun v =>
    congrArg (fun T : Module.End K V => T v) hπAinv.eq
  have hAB : ∀ v w, idForm h 5 ((A : Module.End K V) v) ((A : Module.End K V) w) =
      idForm h 5 v w := fun v w => (mem_sesqUnitaryGroup.mp hA) v w
  have hc' : h.bar c⁻¹ * c⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hc, inv_one]
  have hAinv1 : (A : Module.End K V) * ((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]; rfl
  have hAinv2 : ((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) * (A : Module.End K V) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel]; rfl
  let s : LinearMap.GeneralLinearGroup K V :=
    ⟨glueEnd π (A : Module.End K V) c⁻¹,
      glueEnd π ((A⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) c, by
        rw [glueEnd_mul hππ hAinvπ, hAinv1, inv_mul_cancel₀ hc0, glueEnd_one], by
        rw [glueEnd_mul hππ hAπ, hAinv2, mul_inv_cancel₀ hc0, glueEnd_one]⟩
  have hsv : ∀ v, (s : Module.End K V) v = v - π v + c⁻¹ • (A : Module.End K V) (π v) := fun v =>
    glueEnd_apply π (A : Module.End K V) c⁻¹ v
  have hsB : s ∈ sesqUnitaryGroup (idForm h 5) :=
    mem_sesqUnitaryGroup.mpr fun v w => glueEnd_isometry (idForm h 5) hππ hπB hAπ hAB hc' v w
  have hcomm : Commute (s : Module.End K V) (x : Module.End K V) :=
    (commute_glueEnd (c := c⁻¹) hπx hAx.symm).symm
  have hVa : ∀ v ∈ primaryComponent (x : Module.End K V) (X - C μ), π v = v := fun v hv =>
    primaryProjection_of_mem hsq ha hv
  have hid' : ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ X - C μ →
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (s : Module.End K V) v = v := by
    intro b hb hba v hv
    have h0 : π v = 0 := primaryProjection_of_mem_ne hsq ha hb hba hv
    rw [hsv, h0, map_zero, smul_zero, sub_zero, add_zero]
  have hid : ∀ v : V, (∀ w ∈ primaryComponent (x : Module.End K V) (X - C μ),
      idForm h 5 w v = 0) → (s : Module.End K V) v = v := by
    intro v hv
    have hπv : π v ∈ primaryComponent (x : Module.End K V) (X - C μ) :=
      primaryProjection_mem hsq ha v
    have h0 : π v = 0 := by
      refine eq_zero_of_perfect_right HU ha ha hdual.symm hπv fun u hu => ?_
      have := hπB u v
      rw [hVa u hu] at this
      rw [← this]
      exact hv u hu
    rw [hsv, h0, map_zero, smul_zero, sub_zero, add_zero]
  have hdet : LinearMap.det (s : Module.End K V) = 1 := by
    rw [det_eq_det_restrict_of_trivial_off hsq ha hcomm hid']
    have hres : (s : Module.End K V).restrict
        (fun _ hv => apply_mem_primaryComponent (a := X - C μ) hcomm hv) =
        c⁻¹ • (A : Module.End K V).restrict
          (fun _ hv => apply_mem_primaryComponent (a := X - C μ) hAx hv) := by
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (s : Module.End K V) (v : V) = c⁻¹ • (A : Module.End K V) (v : V)
      rw [hsv, hVa v v.2, sub_self, zero_add]
    rw [hres, LinearMap.det_smul, ← hcm, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hc0)
  refine ⟨s, mem_specialBlock_of_degree_one HU hμ ha hsB hcomm hid hdet, fun v hv => ?_⟩
  rw [hsv, map_smul π c v, hVa v hv, map_smul (A : Module.End K V) c v, smul_smul, sub_self,
    zero_add, inv_mul_cancel₀ hc0, one_smul]

end SpecialElem

section Twist

open CFSG.RankThree.PartOne.KCUnitaryBlock

variable (h : UnitaryFieldData 2 f K)

include h in
theorem toLinU_scalar' {z : primeFormUnitary h (idGram K 5)} {c : Kˣ}
    (hz : (z : GL (Fin 5) K) = GeneralLinearGroup.scalar (Fin 5) c) :
    ((toLinU h 5 z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) =
      (c : K) • (1 : Module.End K (Fin 5 → K)) := by
  refine LinearMap.ext fun v => ?_
  rw [toLinU_apply_eq, hz]
  ext i
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem mem_primaryComponent_X_sub_C {V : Type*} [AddCommGroup V] [Module K V]
    {x : Module.End K V} {μ : K} {v : V} :
    v ∈ primaryComponent x (X - C μ) ↔ x v = μ • v := by
  rw [mem_primaryComponent]
  simp [sub_eq_zero, Algebra.algebraMap_eq_smul_one]

include h in
theorem exists_twist (hq : 3 < 2 ^ f) (g A : primeFormUnitary h (idGram K 5))
    (hcomm : primeFormConjHom h (idGram K 5) A * primeFormConjHom h (idGram K 5) g =
      primeFormConjHom h (idGram K 5) g * primeFormConjHom h (idGram K 5) A) :
    ∃ lam : Kˣ, lam ^ (2 ^ f + 1) = 1 ∧
      ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) *
        ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) =
      (lam : K) • (((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) *
        ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))) := by
  set κ : primeFormUnitary h (idGram K 5) := (A * g) * (g * A)⁻¹ with hκ
  have h0 : primeFormConjHom h (idGram K 5) (A * g) = primeFormConjHom h (idGram K 5) (g * A) := by
    rw [map_mul, map_mul, hcomm]
  have h1 : primeFormConjHom h (idGram K 5) κ = 1 := by
    rw [hκ, map_mul, map_inv, h0, mul_inv_cancel]
  obtain ⟨lam, hlam, hκlam⟩ := (primeFormConjHom_eq_one_iff (by norm_num) hq κ).mp h1
  refine ⟨lam, hlam, ?_⟩
  have h2 : A * g = κ * (g * A) := by rw [hκ]; group
  have h3 := toLinU_scalar' h hκlam
  have h4 := congrArg (fun z : primeFormUnitary h (idGram K 5) =>
    ((toLinU h 5 z : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))) h2
  simp only [map_mul, Units.val_mul] at h4
  rw [h4, h3, smul_mul_assoc, one_mul]

include h in
theorem twist_eq_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    (g A : primeFormUnitary h (idGram K 5)) {c : Kˣ} (hc : c ^ (2 ^ f + 1) = 1)
    (hgp : (g : GL (Fin 5) K) ^ p = GeneralLinearGroup.scalar (Fin 5) c)
    (x : Module.End K (Fin 5 → K))
    (hx : x = ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K))) (a : primaryFactors x)
    (ha2 : 2 ≤ primaryMultiplicity x (a : K[X])) {lam : Kˣ}
    (hEnd : ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) * x = (lam : K) • (x * ((toLinU h 5 A :
          LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)))) :
    lam = 1 := by
  classical
  by_contra hne
  have hp2 : p ≠ 2 := by omega
  obtain ⟨μ, hμa, hμp, -⟩ := linear_of_mult_two h hp hp5 hpq g hc hgp x hx a ha2
  set A' : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 A : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) with hA'
  have hxp : x ^ p = (c : K) • (1 : Module.End K (Fin 5 → K)) := by
    have h1 := toLinU_scalar' h (z := g ^ p) (c := c) (by rw [Subgroup.coe_pow]; exact hgp)
    rw [map_pow, Units.val_pow_eq_pow_val] at h1
    rw [hx]
    exact h1
  have hpow : ∀ n : ℕ, A' * x ^ n = (lam : K) ^ n • (x ^ n * A') := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, hEnd, mul_smul_comm, smul_smul,
        pow_succ (lam : K) n, mul_assoc (x ^ n) x A']
  set Ainv : Module.End K (Fin 5 → K) :=
    (((toLinU h 5 A)⁻¹ : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K))
    with hAinv
  have hAAinv : A' * Ainv = 1 := by
    rw [hA', hAinv, ← Units.val_mul, mul_inv_cancel]; rfl
  have hinj : Function.Injective A' :=
    ((Module.End.isUnit_iff A').mp (Units.isUnit (toLinU h 5 A))).1
  have hlamp : (lam : K) ^ p = 1 := by
    have h1 := hpow p
    rw [hxp, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at h1
    set v₀ : Fin 5 → K := Pi.single (0 : Fin 5) (1 : K) with hv₀
    have hv₀ne : v₀ ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp [hv₀] at this
    have h2 := congrArg (fun T : Module.End K (Fin 5 → K) => T (Ainv v₀)) h1
    simp only [LinearMap.smul_apply, ← Module.End.mul_apply, hAAinv, Module.End.one_apply] at h2
    have h3 : ((lam : K) ^ p - 1) • ((c : K) • v₀) = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    have hcv : (c : K) • v₀ ≠ 0 := smul_ne_zero c.ne_zero hv₀ne
    have h4 := (smul_eq_zero.mp h3).resolve_right hcv
    exact sub_eq_zero.mp h4
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hμp
    exact c.ne_zero hμp.symm
  have hbp : (μ⁻¹ • x) ^ p = 1 := by
    rw [_root_.smul_pow, hxp, smul_smul, inv_pow, hμp, inv_mul_cancel₀ c.ne_zero, one_smul]
  have hcb : A' * (μ⁻¹ • x) = (lam : K) • ((μ⁻¹ • x) * A') := by
    rw [mul_smul_comm, hEnd, smul_mul_assoc, smul_comm]
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (lam : K) = p :=
    orderOf_eq_prime hlamp (fun h1 => hne (Units.ext h1))
  have hζ : IsPrimitiveRoot (lam : K) p := by
    have := IsPrimitiveRoot.orderOf (lam : K)
    rwa [hord] at this
  have hshift := CFSG.OddSolvableUnitary.finrank_eq_mul_finrank_eigenspace_one hp.pos hζ hbp hinj hcb
  have heig : (μ⁻¹ • x).eigenspace 1 = primaryComponent x (X - C μ) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, mem_primaryComponent_X_sub_C, LinearMap.smul_apply, one_smul,
      inv_smul_eq_iff₀ hμ0, eq_comm]
  have hfr : Module.finrank K (primaryComponent x (X - C μ)) =
      primaryMultiplicity x (a : K[X]) := by
    have h1 := finrank_primaryComponent x (a : K[X])
    have hnd : (a : K[X]).natDegree = 1 := by rw [hμa]; exact natDegree_X_sub_C μ
    rw [hnd, one_mul] at h1
    rw [← hμa]
    exact h1
  rw [heig, hfr, Module.finrank_fin_fun] at hshift
  nlinarith

end Twist




end CFSG.RankThree.PartOne.S15K
