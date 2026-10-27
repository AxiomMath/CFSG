module

import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.StandardType

theorem kgLangTorA_exists_dual_normal {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    {σ : F ≃+* F} (hσ : orderOf σ = p) :
    ∃ a b : F, ∀ k < p,
      ∑ i ∈ Finset.range p, (σ ^ i) (a * (σ ^ k) b) = if k = 0 then 1 else 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hσfin : IsOfFinOrder σ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, by rw [← hσ]; exact pow_orderOf_eq_one σ⟩
  let G : Subgroup (F ≃+* F) := Subgroup.zpowers σ
  haveI : Finite G := finite_zpowers.mpr hσfin
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun f : F ≃+* F => (f : F → F)) (fun f g h => by ext x; exact congr_fun h x)
  let K : Subfield F := FixedPoints.subfield G F
  haveI : IsGalois K F := IsGalois.of_fixed_field F G
  haveI : Module.Finite K F := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  haveI : PerfectField K := PerfectField.ofFinite
  haveI : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let e : G ≃* (F ≃ₐ[K] F) := FixedPoints.toAlgAutMulEquiv G F
  have he_apply : ∀ (g : G) (x : F), e g x = g • x := by
    intro g x
    change (FixedPoints.toAlgAutMulEquiv G F g) x = g • x
    rw [show FixedPoints.toAlgAutMulEquiv G F g = MulSemiringAction.toAlgEquiv K F g from rfl]
    exact MulSemiringAction.toAlgEquiv_apply K F g x
  have hsum : ∀ x : F, algebraMap K F (Algebra.trace K F x) = ∑ i ∈ Finset.range p, (σ ^ i) x := by
    intro x
    rw [trace_eq_sum_automorphisms (K := K) x]
    have h1 : (∑ τ : F ≃ₐ[K] F, τ x) = ∑ g : G, e g x :=
      (Fintype.sum_equiv e (fun g : G => e g x) (fun τ : F ≃ₐ[K] F => τ x) (fun g => rfl)).symm
    have h2 : (∑ g : G, e g x) = ∑ g : G, (g : F ≃+* F) x := by
      apply Finset.sum_congr rfl
      intro g _
      rw [he_apply]
      exact RingAut.smul_def (g : F ≃+* F) x
    have h3 : (∑ g : G, (g : F ≃+* F) x) = ∑ i ∈ Finset.range p, (σ ^ i) x := by
      symm
      refine Finset.sum_bij (fun i _ => (⟨σ ^ i, Subgroup.npow_mem_zpowers σ i⟩ : G)) ?_ ?_ ?_ ?_
      · intro i hi; exact Finset.mem_univ _
      · intro i hi j hj hij
        have h : σ ^ i = σ ^ j := Subtype.ext_iff.mp hij
        rw [pow_inj_mod, hσ, Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
          Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at h
        exact h
      · intro g _
        obtain ⟨i, hi, hii⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp g.2)
        rw [hσ] at hi
        exact ⟨i, hi, Subtype.ext hii⟩
      · intro i hi; rfl
    rw [h1, h2, h3]
  let nb : Module.Basis (F ≃ₐ[K] F) K F := IsGalois.normalBasis K F
  let b : F := nb 1
  let a : F := nb.traceDual 1
  refine ⟨a, b, ?_⟩
  intro k hk
  have hnb : nb (e ⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩) = (σ ^ k) b := by
    rw [IsGalois.normalBasis_apply, he_apply]
    exact RingAut.smul_def ((⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) : F ≃+* F) b
  have htrace : Algebra.trace K F (a * (σ ^ k) b) =
      if (⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) = 1 then 1 else 0 := by
    rw [← hnb]
    have h := Module.Basis.trace_traceDual_mul nb 1 (e ⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩)
    simpa [a] using h
  have hcond : (⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) = 1 ↔ k = 0 := by
    rw [Subtype.ext_iff]
    change σ ^ k = 1 ↔ k = 0
    rw [← pow_zero σ, pow_inj_mod, hσ, Nat.zero_mod, Nat.mod_eq_of_lt hk]
  calc ∑ i ∈ Finset.range p, (σ ^ i) (a * (σ ^ k) b)
      = algebraMap K F (Algebra.trace K F (a * (σ ^ k) b)) := (hsum _).symm
    _ = algebraMap K F (if (⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) = 1 then 1 else 0) := by
        rw [htrace]
    _ = if (⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) = 1 then 1 else 0 := by
        by_cases h : (⟨σ ^ k, Subgroup.npow_mem_zpowers σ k⟩ : G) = 1 <;> simp [h]
    _ = if k = 0 then 1 else 0 := by rw [if_congr hcond rfl rfl]

private lemma kgLangTorALangAux_add_sub_mod {p c j : ℕ} (hp : 0 < p) (hc : c ≤ p) (hj : j < p) :
    (c + (j + p - c) % p) % p = j := by
  have hcancel : (c + (j + p - c) % p) % p ≡ j [MOD p] := by
    refine Nat.ModEq.add_right_cancel' c ?_
    have h1 : (c + (j + p - c) % p) % p + c ≡ c + (j + p - c) % p + c [MOD p] :=
      Nat.ModEq.add_right c (Nat.mod_modEq _ _)
    have h2 : c + (j + p - c) % p ≡ c + (j + p - c) [MOD p] :=
      Nat.ModEq.add_left c (Nat.mod_modEq _ _)
    have h3 : c + (j + p - c) = j + p := by omega
    rw [h3] at h2
    have h4 : j + p ≡ j [MOD p] := by rw [Nat.ModEq, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    have h5 : c + (j + p - c) % p + c ≡ j + c [MOD p] :=
      (Nat.ModEq.add_right c h2).trans (Nat.ModEq.add_right c h4)
    exact h1.trans h5
  exact Nat.ModEq.eq_of_lt_of_lt hcancel (Nat.mod_lt _ hp) hj

private lemma kgLangTorALangAux_sub_add_mod {p c k : ℕ} (hp : 0 < p) (hc : c ≤ p) (hk : k < p) :
    (((c + k) % p) + p - c) % p = k := by
  have hcancel : (((c + k) % p) + p - c) % p ≡ k [MOD p] := by
    refine Nat.ModEq.add_right_cancel' c ?_
    have h1 : (((c + k) % p) + p - c) % p + c ≡ ((c + k) % p) + p - c + c [MOD p] :=
      Nat.ModEq.add_right c (Nat.mod_modEq _ _)
    have h2 : ((c + k) % p) + p - c + c = (c + k) % p + p := by omega
    rw [h2] at h1
    have h3 : (c + k) % p + p ≡ (c + k) % p [MOD p] := by
      rw [Nat.ModEq, Nat.add_mod_right]
    have h4 : (c + k) % p ≡ c + k [MOD p] := Nat.mod_modEq _ _
    exact h1.trans (h3.trans (by simpa [Nat.add_comm] using h4))
  exact Nat.ModEq.eq_of_lt_of_lt hcancel (Nat.mod_lt _ hp) hk

private lemma kgLangTorALangAux_exp_succ_mod {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    (((p - i) % p) + 1) % p = (p - i + 1) % p := by
  simpa using Nat.ModEq.add_right 1 (Nat.mod_modEq (p - i) p)

private lemma kgLangTorALangAux_exp_shift_mod {p i : ℕ} (hp : 0 < p) (hi : i < p) :
    (p - i) % p = (p - (i + 1) % p + 1) % p := by
  have h1 : (i + 1) % p ≡ i + 1 [MOD p] := Nat.mod_modEq _ _
  have h2 : p - (i + 1) % p ≡ p - (i + 1) [MOD p] :=
    Nat.ModEq.sub_left (le_of_lt (Nat.mod_lt _ hp)) (by omega) h1
  have h3 : p - (i + 1) % p + 1 ≡ p - (i + 1) + 1 [MOD p] := Nat.ModEq.add_right 1 h2
  have h4 : p - (i + 1) + 1 = p - i := by omega
  rw [h4] at h3
  exact h3.symm

private lemma kgLangTorALangAux_map_smul {d : ℕ} {F : Type} [Semiring F]
    (f : F →+* F) (c : F) (M : Matrix (Fin d) (Fin d) F) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

private lemma kgLangTorALangAux_sum_reindex {F M : Type} [Mul F] [AddCommMonoid M] [Monoid M] [SMul F M]
    {p c : ℕ} (hp : 0 < p) (hc : c ≤ p) (A : F) (B : ℕ → F) (E : M) :
    (∑ j ∈ Finset.range p, (A * B j) • E ^ ((j + p - c) % p))
      = ∑ k ∈ Finset.range p, (A * B ((c + k) % p)) • E ^ k := by
  refine Finset.sum_nbij' (fun j => (j + p - c) % p) (fun k => (c + k) % p) ?_ ?_ ?_ ?_ ?_
  · intro j hj; exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  · intro k hk; exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  · intro j hj; exact kgLangTorALangAux_add_sub_mod hp hc (Finset.mem_range.mp hj)
  · intro k hk; exact kgLangTorALangAux_sub_add_mod hp hc (Finset.mem_range.mp hk)
  · intro j hj
    rw [kgLangTorALangAux_add_sub_mod hp hc (Finset.mem_range.mp hj)]

private lemma kgLangTorALangAux_sum_shift {F M : Type} [Mul F] [AddCommMonoid M] [Monoid M] [SMul F M]
    {p : ℕ} (hp : 0 < p) (A : ℕ → F) (E : M) :
    (∑ i ∈ Finset.range p, A ((i + 1) % p) • E ^ ((p - i) % p))
      = ∑ j ∈ Finset.range p, A j • E ^ ((p - j + 1) % p) := by
  refine Finset.sum_nbij' (fun i => (i + 1) % p) (fun j => (j + p - 1) % p) ?_ ?_ ?_ ?_ ?_
  · intro i hi; exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  · intro j hj; exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  · intro i hi
    have h := kgLangTorALangAux_sub_add_mod hp (show 1 ≤ p by omega) (Finset.mem_range.mp hi)
    simpa only [Nat.add_comm 1 i] using h
  · intro j hj
    have h := kgLangTorALangAux_add_sub_mod hp (show 1 ≤ p by omega) (Finset.mem_range.mp hj)
    rw [Nat.add_comm ((j + p - 1) % p) 1]
    exact h
  · intro i hi
    rw [kgLangTorALangAux_exp_shift_mod hp (Finset.mem_range.mp hi)]

theorem kgLangTorA_lang_poly {d p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    {σ : F ≃+* F} (hσ : orderOf σ = p) {e : GL (Fin d) F}
    (he : Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e) (hep : e ^ p = 1) :
    ∃ (s : GL (Fin d) F) (P : Polynomial F),
      (s : Matrix (Fin d) (Fin d) F) = Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) P ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e := by
  classical
  obtain ⟨a, b, hab⟩ := kgLangTorA_exists_dual_normal hp hσ
  let E : Matrix (Fin d) (Fin d) F := (e : Matrix (Fin d) (Fin d) F)
  have hEp : E ^ p = 1 := by
    have h := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) hep
    simpa [E, Units.val_pow_eq_pow_val] using h
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hEσ : E.map (σ : F →+* F) = E := by
    ext i j
    have h := congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) he
    have h' := congrFun (congrFun h i) j
    rw [Matrix.GeneralLinearGroup.map_apply] at h'
    simpa [E, Matrix.map_apply] using h'
  let P : Polynomial F := ∑ i ∈ Finset.range p, Polynomial.C ((σ ^ i) a) * Polynomial.X ^ ((p - i) % p)
  let T : Polynomial F := ∑ j ∈ Finset.range p, Polynomial.C ((σ ^ j) b) * Polynomial.X ^ j
  let S : Matrix (Fin d) (Fin d) F := Polynomial.aeval E P
  let T' : Matrix (Fin d) (Fin d) F := Polynomial.aeval E T
  have hS : S = ∑ i ∈ Finset.range p, (σ ^ i) a • E ^ ((p - i) % p) := by
    simp only [S, P]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
  have hT : T' = ∑ j ∈ Finset.range p, (σ ^ j) b • E ^ j := by
    simp only [T', T]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]

  have hAB : ∀ i k, i < p → k < p →
      (σ ^ i) (a * (σ ^ k) b) = (σ ^ i) a * (σ ^ ((i + k) % p)) b := by
    intro i k hi hk
    rw [map_mul]
    have h1 : (σ ^ i) ((σ ^ k) b) = (σ ^ (i + k)) b := by
      change (σ ^ i * σ ^ k) b = (σ ^ (i + k)) b
      rw [pow_add]
    rw [h1, pow_eq_pow_mod (i + k) hσp]
  have hST : S * T' = 1 := by
    rw [hS, hT, Finset.sum_mul]
    simp only [Finset.mul_sum]
    have hterm : ∀ i j, i < p → j < p →
        ((σ ^ i) a • E ^ ((p - i) % p)) * ((σ ^ j) b • E ^ j)
          = ((σ ^ i) a * (σ ^ j) b) • E ^ ((j + p - i) % p) := by
      intro i j hi hj
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      rw [← pow_add, pow_eq_pow_mod _ hEp]
      congr 1
      have hmod := Nat.ModEq.add_right j (Nat.mod_modEq (p - i) p)
      have h4 : (p - i) + j = j + p - i := by omega
      rw [h4] at hmod
      exact hmod
    have hgoal : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
          ((σ ^ i) a • E ^ ((p - i) % p)) * ((σ ^ j) b • E ^ j))
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
          ((σ ^ i) a * (σ ^ j) b) • E ^ ((j + p - i) % p) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
    rw [hgoal]
    have hstep : ∀ i ∈ Finset.range p,
        (∑ j ∈ Finset.range p, ((σ ^ i) a * (σ ^ j) b) • E ^ ((j + p - i) % p))
          = ∑ k ∈ Finset.range p, ((σ ^ i) a * (σ ^ ((i + k) % p)) b) • E ^ k := by
      intro i hi
      exact kgLangTorALangAux_sum_reindex hp.pos (le_of_lt (Finset.mem_range.mp hi))
        ((σ ^ i) a) (fun j => (σ ^ j) b) E
    rw [Finset.sum_congr rfl hstep]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hc : ∀ k ∈ Finset.range p,
        (∑ i ∈ Finset.range p, (σ ^ i) a * (σ ^ ((i + k) % p)) b) = if k = 0 then 1 else 0 := by
      intro k hk
      rw [← hab k (Finset.mem_range.mp hk)]
      apply Finset.sum_congr rfl
      intro i hi
      exact (hAB i k (Finset.mem_range.mp hi) (Finset.mem_range.mp hk)).symm
    have hsum0 : (∑ x ∈ Finset.range p,
          (∑ i ∈ Finset.range p, (σ ^ i) a * (σ ^ ((i + x) % p)) b) • E ^ x)
        = ∑ x ∈ Finset.range p, (if x = 0 then (1 : F) else 0) • E ^ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hc x hx]
    rw [hsum0]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      simp [hk0]
    · intro h
      exact absurd (Finset.mem_range.mpr hp.pos) h
  have hTS : T' * S = 1 := by
    rw [← Polynomial.aeval_mul, mul_comm T P, Polynomial.aeval_mul]
    exact hST
  have hSE : S.map (σ : F →+* F) = S * E := by
    have hleft : S.map (σ : F →+* F) = ∑ j ∈ Finset.range p, (σ ^ j) a • E ^ ((p - j + 1) % p) := by
      rw [hS]
      have h1 : (∑ i ∈ Finset.range p, (σ ^ i) a • E ^ ((p - i) % p)).map (σ : F →+* F)
          = ∑ i ∈ Finset.range p, ((σ ^ i) a • E ^ ((p - i) % p)).map (σ : F →+* F) := by
        ext r c
        simp [Matrix.map_apply, Matrix.sum_apply, map_sum]
      rw [h1]
      have h2 : ∀ i ∈ Finset.range p,
          ((σ ^ i) a • E ^ ((p - i) % p)).map (σ : F →+* F) = (σ ^ ((i + 1) % p)) a • E ^ ((p - i) % p) := by
        intro i hi
        rw [kgLangTorALangAux_map_smul, Matrix.map_pow, hEσ]
        congr 1
        have hcoe : (σ ^ ((i + 1) % p)) a = σ ((σ ^ i) a) := by
          rw [← pow_eq_pow_mod (i + 1) hσp, pow_succ']
          rfl
        exact hcoe.symm
      rw [Finset.sum_congr rfl h2]
      exact kgLangTorALangAux_sum_shift hp.pos (fun i => (σ ^ i) a) E
    have hright : S * E = ∑ j ∈ Finset.range p, (σ ^ j) a • E ^ ((p - j + 1) % p) := by
      rw [hS, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Matrix.smul_mul, ← pow_succ, pow_eq_pow_mod _ hEp,
          kgLangTorALangAux_exp_succ_mod hp.pos (Finset.mem_range.mp hi)]
    rw [hleft, hright]
  let s : GL (Fin d) F := Units.mk S T' hST hTS
  refine ⟨s, P, ?_, ?_⟩
  · rfl
  · apply Units.ext
    have hval : ((Matrix.GeneralLinearGroup.map (σ : F →+* F) s : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        = S.map (σ : F →+* F) := by
      ext i j
      rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
    rw [hval, Units.val_mul]
    exact hSE

end CFSG.StandardType
