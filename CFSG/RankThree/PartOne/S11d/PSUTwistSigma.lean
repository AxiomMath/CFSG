module

public import CFSG.RankThree.PartOne.TCU.ThreeComp

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.OddIso
open scoped commutatorElement

variable {F p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 F K}

section Basic3

variable {A : SUn h 3} {u : Module.End K (Fin 3 → K)} {c : K}

theorem TwistSetup.finrank_range_eq_one [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p) (hAp : A ^ p = 1)
    (hA1 : A ≠ 1) (S : TwistSetup h 3 p A u c) :
    Module.finrank K (LinearMap.range (u - 1)) = 1 := by
  have hchar : CharP K 2 := h.charP
  have hsum := LinearMap.finrank_range_add_finrank_ker (u - 1)
  rw [Module.finrank_fin_fun] at hsum
  have hle : Module.finrank K (LinearMap.range (u - 1)) ≤ 1 := by
    have := S.hm
    omega
  have hne : LinearMap.range (u - 1) ≠ ⊥ := by
    intro hb
    have hu1 : u = 1 := by
      refine LinearMap.ext fun v => ?_
      have hv : (u - 1) v ∈ LinearMap.range (u - 1) := ⟨v, rfl⟩
      rw [hb, Submodule.mem_bot] at hv
      exact sub_eq_zero.mp (by simpa using hv)
    have hAc1 : linOf (A : GL (Fin 3) K) = c • LinearMap.id := by rw [S.hAc, hu1]; rfl
    have hAp' : linOf (A : GL (Fin 3) K) ^ p = 1 := by
      rw [← linOf_pow, ← Subgroup.coe_pow, hAp]
      exact linOf_one
    have hcp : c ^ p = 1 := by
      have h1 := congrArg (fun f : Module.End K (Fin 3 → K) => f (Pi.single 0 1)) hAp'
      simp only [hAc1, smul_pow, Module.End.one_apply] at h1
      have h2 : (c ^ p • (LinearMap.id : Module.End K (Fin 3 → K)) ^ p) (Pi.single 0 1) =
          c ^ p • (Pi.single 0 1 : Fin 3 → K) := by simp
      rw [h2] at h1
      have h3 := congrFun h1 0
      simpa using h3
    have hdet : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = c ^ 3 := by
      rw [← LinearMap.det_toLin' ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)]
      change LinearMap.det (linOf (A : GL (Fin 3) K)) = _
      rw [hAc1, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
    have hdet1 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_gramSU_iff_unitary h).mp A.2).2
    have hc1 : c = 1 := eq_one_of_pow_three_of_pow_prime hp hp5 (by rw [← hdet, hdet1]) hcp
    apply hA1
    apply Subtype.ext
    apply linOf_injective
    rw [Subgroup.coe_one, linOf_one, hAc1, hc1, one_smul]
    rfl
  have h1 : 1 ≤ Module.finrank K (LinearMap.range (u - 1)) := Submodule.one_le_finrank_iff.mpr hne
  omega

end Basic3

section Sigma

variable {A : SUn h 3} {u : Module.End K (Fin 3 → K)} {c : K}

theorem TwistSetup.exists_nu [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p) (hAp : A ^ p = 1)
    (hA1 : A ≠ 1) (S : TwistSetup h 3 p A u c) :
    ∃ ν : K, ν ≠ 1 ∧ ∀ v, (u - 1) ((u - ν • 1) v) = 0 := by
  classical
  have hchar : CharP K 2 := h.charP
  have hfr := S.finrank_range_eq_one hp hp5 hAp hA1
  have hRne : LinearMap.range (u - 1) ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at hfr
    exact absurd hfr (by norm_num)
  obtain ⟨ℓ, hℓR, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  have hRspan : LinearMap.range (u - 1) = Submodule.span K {ℓ} :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem ℓ _).mpr hℓR)
      ((finrank_span_singleton hℓ0).trans hfr.symm)).symm
  have hℓinv : u ℓ ∈ LinearMap.range (u - 1) := range_invariant u hℓR
  rw [hRspan, Submodule.mem_span_singleton] at hℓinv
  obtain ⟨ν, hν⟩ := hℓinv
  have hν1 : ν ≠ 1 := by
    intro hν1
    have hker : ℓ ∈ LinearMap.ker (u - 1) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hν, hν1,
        one_smul]
    have hdis := disjoint_iff.mp (isCompl_ker_range S.hodd S.hup).disjoint
    have h0 : ℓ ∈ LinearMap.ker (u - 1) ⊓ LinearMap.range (u - 1) := ⟨hker, hℓR⟩
    rw [hdis, Submodule.mem_bot] at h0
    exact hℓ0 h0
  refine ⟨ν, hν1, fun v => ?_⟩
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := exists_fix_add_range S.hodd S.hup v
  rw [hRspan, Submodule.mem_span_singleton] at hw
  obtain ⟨κ, rfl⟩ := hw
  have huv₁ : u v₁ = v₁ := sub_eq_zero.mp (LinearMap.mem_ker.mp hv₁)
  have huℓ : u ℓ = ν • ℓ := hν.symm
  have h1 : (u - ν • 1) (v₁ + κ • ℓ) = (1 - ν) • v₁ := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
      huv₁, huℓ]
    module
  rw [h1, map_smul]
  have h0 : (u - 1) v₁ = 0 := LinearMap.mem_ker.mp hv₁
  rw [h0, smul_zero]

theorem TwistSetup.sigma_eq [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p) (hAp : A ^ p = 1)
    (hA1 : A ≠ 1) (S : TwistSetup h 3 p A u c) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hσA : glAut σ (A : GL (Fin 3) K) = A) : σ c = c := by
  classical
  obtain ⟨ν, hν1, hquad⟩ := S.exists_nu hp hp5 hAp hA1
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMlin : Matrix.toLin' M = c • u := S.hAc
  have hc0 : c ≠ 0 := S.hc
  have hu2 : u * u - (1 + ν) • u + ν • (1 : Module.End K (Fin 3 → K)) = 0 := by
    refine LinearMap.ext fun v => ?_
    have e := hquad v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul] at e
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, Module.End.mul_apply, LinearMap.zero_apply]
    calc u (u v) - (1 + ν) • u v + ν • v = u (u v) - u v - ν • (u v - v) := by module
      _ = 0 := e
  have hmat : M * M - (c * (1 + ν)) • M + (c ^ 2 * ν) • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
    apply Matrix.toLin'.injective
    have hT : (c • u) * (c • u) - (c * (1 + ν)) • (c • u) +
        (c ^ 2 * ν) • (1 : Module.End K (Fin 3 → K)) = 0 := by
      rw [smul_mul_smul_comm]
      calc (c * c) • (u * u) - (c * (1 + ν)) • (c • u) + (c ^ 2 * ν) • (1 : Module.End K _)
          = c ^ 2 • (u * u - (1 + ν) • u + ν • (1 : Module.End K _)) := by module
        _ = 0 := by rw [hu2, smul_zero]
    rw [map_zero, map_add, map_sub, Matrix.toLin'_mul, map_smul, map_smul, Matrix.toLin'_one,
      hMlin]
    rw [Module.End.mul_eq_comp, Module.End.one_eq_id] at hT
    exact hT
  have hMσ : M.map σ = M := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hσA
    simpa [coe_glAut] using this
  have hsm : ∀ (a : K) (N : Matrix (Fin 3) (Fin 3) K), (a • N).map σ = σ a • N.map σ := by
    intro a N
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
  have hmat' : M * M - (σ c * (1 + σ ν)) • M +
      (σ c ^ 2 * σ ν) • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
    have h1 := congrArg (σ.toRingHom.mapMatrix (m := Fin 3)) hmat
    have hMσ' : M.map ⇑σ.toRingHom = M := hMσ
    have hsm' : ∀ (a : K) (N : Matrix (Fin 3) (Fin 3) K),
        (a • N).map ⇑σ.toRingHom = σ.toRingHom a • N.map ⇑σ.toRingHom := hsm
    simp only [map_sub, map_add, map_mul, map_zero, map_one, map_pow, RingHom.mapMatrix_apply,
      hMσ', hsm', Matrix.map_one _ (map_zero σ.toRingHom) (map_one σ.toRingHom)] at h1
    exact h1
  have hkey : (c * (1 + ν) - σ c * (1 + σ ν)) • M =
      (c ^ 2 * ν - σ c ^ 2 * σ ν) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← sub_eq_zero]
    calc (c * (1 + ν) - σ c * (1 + σ ν)) • M -
          (c ^ 2 * ν - σ c ^ 2 * σ ν) • (1 : Matrix (Fin 3) (Fin 3) K)
        = (M * M - (σ c * (1 + σ ν)) • M + (σ c ^ 2 * σ ν) • (1 : Matrix (Fin 3) (Fin 3) K)) -
          (M * M - (c * (1 + ν)) • M + (c ^ 2 * ν) • (1 : Matrix (Fin 3) (Fin 3) K)) := by module
      _ = 0 := by rw [hmat', hmat, sub_zero]
  have hnotscalar : ∀ d : K, M ≠ d • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro d hd
    have hfr := S.finrank_range_eq_one hp hp5 hAp hA1
    have hd' : c • u = d • (LinearMap.id : Module.End K (Fin 3 → K)) := by
      rw [← hMlin, hd, map_smul, Matrix.toLin'_one]
    have hu : u = (c⁻¹ * d) • (LinearMap.id : Module.End K (Fin 3 → K)) := by
      calc u = c⁻¹ • (c • u) := (inv_smul_smul₀ hc0 u).symm
        _ = (c⁻¹ * d) • LinearMap.id := by rw [hd', smul_smul]
    by_cases hd1 : c⁻¹ * d = 1
    · have h0 : u - 1 = 0 := by
        rw [hu, hd1, one_smul]
        exact sub_eq_zero.mpr rfl
      rw [h0, LinearMap.range_zero, finrank_bot] at hfr
      exact absurd hfr (by norm_num)
    · have hd1' : c⁻¹ * d - 1 ≠ 0 := sub_ne_zero.mpr hd1
      have hrange : LinearMap.range (u - 1) = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro v
        refine ⟨(c⁻¹ * d - 1)⁻¹ • v, ?_⟩
        have e : ∀ w, (u - 1) w = (c⁻¹ * d - 1) • w := fun w => by
          rw [hu]
          simp [sub_smul]
        rw [e, smul_inv_smul₀ hd1']
      rw [hrange, finrank_top, Module.finrank_fin_fun] at hfr
      norm_num at hfr
  have ha : c * (1 + ν) = σ c * (1 + σ ν) := by
    by_contra hne
    have hne' : c * (1 + ν) - σ c * (1 + σ ν) ≠ 0 := sub_ne_zero.mpr hne
    refine hnotscalar ((c ^ 2 * ν - σ c ^ 2 * σ ν) / (c * (1 + ν) - σ c * (1 + σ ν))) ?_
    calc M = (c * (1 + ν) - σ c * (1 + σ ν))⁻¹ •
          ((c * (1 + ν) - σ c * (1 + σ ν)) • M) := (inv_smul_smul₀ hne' M).symm
      _ = _ := by rw [hkey, smul_smul, div_eq_inv_mul]
  have hb : c ^ 2 * ν = σ c ^ 2 * σ ν := by
    have h0 : (c ^ 2 * ν - σ c ^ 2 * σ ν) • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
      rw [← hkey, ha, sub_self, zero_smul]
    have h00 := congrFun (congrFun h0 0) 0
    simpa [sub_eq_zero] using h00
  have hsum : σ c + σ c * σ ν = c + c * ν := by linear_combination -ha
  have hprod : σ c * (σ c * σ ν) = c * (c * ν) := by linear_combination -hb
  have hq : (σ c - c) * (σ c - c * ν) = 0 := by linear_combination (σ c) * hsum - hprod
  rcases mul_eq_zero.mp hq with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have e1 : σ c = c * ν := sub_eq_zero.mp h1
    have hσσ : σ (σ c) = c := by
      calc σ (σ c) = σ (c * ν) := by rw [e1]
        _ = σ c * σ ν := map_mul σ c ν
        _ = c := by linear_combination hsum - e1
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
    have hs2 : ∀ k : ℕ, (σ ^ (2 * k)) c = c := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.mul_succ, pow_add]
        change (σ ^ (2 * k)) ((σ ^ 2) c) = c
        have h22 : (σ ^ 2) c = c := by
          rw [pow_two]
          exact hσσ
        rw [h22, ih]
    have hpow : (σ ^ p) c = c := by
      rw [← hσ, pow_orderOf_eq_one]
      rfl
    rw [hm, pow_succ'] at hpow
    have hσc : σ c = c := by
      change σ ((σ ^ (2 * m)) c) = c at hpow
      rwa [hs2 m] at hpow
    apply hν1
    have h2 : c * ν = c * 1 := by rw [← e1, hσc, mul_one]
    exact mul_left_cancel₀ hc0 h2

end Sigma

end CFSG.RankThree.PartOne.TCU
