module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3BorelTorus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem uc22pwI3_dvd_two_mul_of_involution {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : Type} [Group X]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (α : SpecialLinearGroup (Fin 3) K →* X)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    {σ : MulAut X} (hσ2 : σ * σ = 1)
    (hσU : ∀ x, x ∈ (unitriangular 3 K).map α ↔ σ x ∈ (unitriangular 3 K).map α)
    {i : ℕ} {ε : Bool}
    (hi : ∀ d ∈ SpecialLinearGroup.diagonalTorus K 3,
      σ (α d) * (α (uc22pwI3TorusMap K ε i d))⁻¹ ∈ (unitriangular 3 K).map α) :
    n ∣ 2 * i := by
  let xd : Kˣ →* X := α.comp (uc22pwI3dSL K)
  have hker : ∀ c : Kˣ, xd c ∈ (unitriangular 3 K).map α → c = 1 := by
    intro c hc
    obtain ⟨u, hu, hue⟩ := hc
    have hz : u⁻¹ * uc22pwI3dSL K c ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (α u)⁻¹ * xd c = 1
      rw [hue, inv_mul_cancel]
    exact uc22pwI3_dSL_eq_one_of_mul_center (u := u) (z := u⁻¹ * uc22pwI3dSL K c) hu (hαc hz)
      (by group)
  have hPF : uc22pwI3PF xd ((unitriangular 3 K).map α) σ i := by
    intro a
    have h := hi _ (uc22pwI3dSL_mem_diagonalTorus a)
    rw [uc22pwI3TorusMap_dSL] at h
    exact h
  have hU : ∀ u ∈ (unitriangular 3 K).map α, σ u ∈ (unitriangular 3 K).map α :=
    fun u hu => (hσU u).1 hu
  have hpow := uc22pwI3PF_pow hU hPF 2
  rw [pow_two, hσ2] at hpow
  have hfix : ∀ a : Kˣ, a ^ 2 ^ (2 * i) = a := uc22pwI3PF_eq_of_one hker hpow
  have hfixK : ∀ x : K, x ^ 2 ^ (2 * i) = x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · have h2 := congrArg (fun u : Kˣ => (u : K)) (hfix (Units.mk0 x hx))
      simpa using h2
  exact uc22pwI2_dvd_of_forall_pow hK hfixK

theorem uc22pwI3_involution_borel_action {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hn : 3 ≤ n)
    (h : IsL3 (X ⧸ Subgroup.center X) n) (U : Sylow 2 X) {r : ℕ}
    (hri : ∀ i : ℕ, n ∣ 2 * i → r ∣ 2 ^ i - 1) {σ τ : MulAut X}
    (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1)
    (hσU : ∀ x, x ∈ (U : Subgroup X) ↔ σ x ∈ (U : Subgroup X))
    (hτU : ∀ x, x ∈ (U : Subgroup X) ↔ τ x ∈ (U : Subgroup X))
    (hσne : ∃ b ∈ normalizer ((U : Subgroup X) : Set X), b ^ r ∈ (U : Subgroup X) ∧
      σ b * b⁻¹ ∉ (U : Subgroup X))
    (hτne : ∃ b ∈ normalizer ((U : Subgroup X) : Set X), b ^ r ∈ (U : Subgroup X) ∧
      τ b * b⁻¹ ∉ (U : Subgroup X))
    {b : X} (hb : b ∈ normalizer ((U : Subgroup X) : Set X))
    (hbr : b ^ r ∈ (U : Subgroup X)) :
    σ b * (τ b)⁻¹ ∈ (U : Subgroup X) := by
  obtain ⟨K, _, _, _, α, hK, hα, hαc, hαU⟩ := uc22pwI3_exists_cover_sylow hq (by omega) h U
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hconv : ∀ φ : MulAut X, (∀ x, x ∈ (U : Subgroup X) ↔ φ x ∈ (U : Subgroup X)) →
      ∀ x, x ∈ (unitriangular 3 K).map α ↔ φ x ∈ (unitriangular 3 K).map α := by
    intro φ hφ x
    rw [hαU]
    exact hφ x
  have data : ∀ φ : MulAut X, φ * φ = 1 → (∀ x, x ∈ (U : Subgroup X) ↔ φ x ∈ (U : Subgroup X)) →
      ∃ ε : Bool, ∀ d ∈ SpecialLinearGroup.diagonalTorus K 3, (α d) ^ r = 1 →
        φ (α d) * (α (if ε then uc22pwI3Jsl K * d⁻¹ * uc22pwI3Jsl K else d))⁻¹ ∈
          (U : Subgroup X) := by
    intro φ hφ2 hφU
    obtain ⟨ν, hνα, hν⟩ := uc22pwI3_lift hq hK5 α hα hαc φ (hconv φ hφU)
    obtain ⟨i, ε, hi⟩ := uc22pwI3_torus_action ν hν
    have hi' : ∀ d ∈ SpecialLinearGroup.diagonalTorus K 3,
        φ (α d) * (α (uc22pwI3TorusMap K ε i d))⁻¹ ∈ (unitriangular 3 K).map α := by
      intro d hd
      have h1 : α (ν d * (uc22pwI3TorusMap K ε i d)⁻¹) ∈ (unitriangular 3 K).map α :=
        Subgroup.mem_map.mpr ⟨_, hi d hd, rfl⟩
      rwa [map_mul, map_inv, hνα] at h1
    have hn2 : n ∣ 2 * i :=
      uc22pwI3_dvd_two_mul_of_involution hK α hαc hφ2 (hconv φ hφU) hi'
    obtain ⟨k, hk⟩ := hri i hn2
    refine ⟨ε, fun d hd hdr => ?_⟩
    have hpow : α (d ^ 2 ^ i) = α d := by
      have h1 : 2 ^ i = r * k + 1 := by
        have := Nat.one_le_two_pow (n := i)
        omega
      rw [map_pow, h1, pow_succ, pow_mul, hdr, one_pow, one_mul]
    have h := hi' d hd
    rw [hαU] at h
    cases ε
    · simpa [uc22pwI3TorusMap, hpow] using h
    · simp only [uc22pwI3TorusMap, if_true, map_mul, map_inv, hpow] at h
      simpa only [if_true, map_mul, map_inv] using h
  have dec : ∀ b ∈ normalizer ((U : Subgroup X) : Set X), b ^ r ∈ (U : Subgroup X) →
      ∃ d ∈ SpecialLinearGroup.diagonalTorus K 3, b * (α d)⁻¹ ∈ (U : Subgroup X) ∧
        (α d) ^ r = 1 := by
    intro b hb hbr
    rw [← hαU] at hb
    obtain ⟨d, hd, hu⟩ := uc22pwI3_exists_torus_of_mem_normalizer α hα hαc hb
    rw [hαU] at hb hu
    have hdN : α d ∈ normalizer ((U : Subgroup X) : Set X) := by
      have e : α d = (b * (α d)⁻¹)⁻¹ * b := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hu)) hb
    have hpm : ∀ m : ℕ, b ^ m * ((α d) ^ m)⁻¹ ∈ (U : Subgroup X) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have e : b ^ (m + 1) * ((α d) ^ (m + 1))⁻¹ =
            (b ^ m * ((α d) ^ m)⁻¹) * ((α d) ^ m * (b * (α d)⁻¹) * ((α d) ^ m)⁻¹) := by
          group
        rw [e]
        exact Subgroup.mul_mem _ ih
          ((Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hdN m) _).1 hu)
    have hdr : (α d) ^ r ∈ (U : Subgroup X) := by
      have e : (α d) ^ r = (b ^ r * ((α d) ^ r)⁻¹)⁻¹ * b ^ r := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hpm r)) hbr
    refine ⟨d, hd, hu, ?_⟩
    rw [← map_pow]
    rw [← map_pow, ← hαU] at hdr
    exact uc22pwI3_eq_one_of_torus_mem α hαc (Subgroup.pow_mem _ hd r) hdr
  have triv : ∀ φ : MulAut X, (∀ x, x ∈ (U : Subgroup X) ↔ φ x ∈ (U : Subgroup X)) →
      (∀ d ∈ SpecialLinearGroup.diagonalTorus K 3, (α d) ^ r = 1 →
        φ (α d) * (α d)⁻¹ ∈ (U : Subgroup X)) →
      ∀ b ∈ normalizer ((U : Subgroup X) : Set X), b ^ r ∈ (U : Subgroup X) →
        φ b * b⁻¹ ∈ (U : Subgroup X) := by
    intro φ hφU hφd b hb hbr
    obtain ⟨d, hd, hu, hdr⟩ := dec b hb hbr
    have e : φ b * b⁻¹ =
        φ (b * (α d)⁻¹) * (φ (α d) * (α d)⁻¹) * (b * (α d)⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hφU _).1 hu) (hφd d hd hdr))
      (Subgroup.inv_mem _ hu)
  have graph : ∀ φ : MulAut X, φ * φ = 1 →
      (∀ x, x ∈ (U : Subgroup X) ↔ φ x ∈ (U : Subgroup X)) →
      (∃ b ∈ normalizer ((U : Subgroup X) : Set X), b ^ r ∈ (U : Subgroup X) ∧
        φ b * b⁻¹ ∉ (U : Subgroup X)) →
      ∀ d ∈ SpecialLinearGroup.diagonalTorus K 3, (α d) ^ r = 1 →
        φ (α d) * (α (uc22pwI3Jsl K * d⁻¹ * uc22pwI3Jsl K))⁻¹ ∈ (U : Subgroup X) := by
    intro φ hφ2 hφU hφne
    obtain ⟨ε, hε⟩ := data φ hφ2 hφU
    cases ε
    · exfalso
      obtain ⟨b', hb', hb'r, hb'n⟩ := hφne
      refine hb'n (triv φ hφU (fun d hd hdr => ?_) b' hb' hb'r)
      simpa using hε d hd hdr
    · intro d hd hdr
      simpa using hε d hd hdr
  obtain ⟨d, hd, hu, hdr⟩ := dec b hb hbr
  have h1 := graph σ hσ2 hσU hσne d hd hdr
  have h2 := graph τ hτ2 hτU hτne d hd hdr
  have e : σ b * (τ b)⁻¹ = σ (b * (α d)⁻¹) *
      ((σ (α d) * (α (uc22pwI3Jsl K * d⁻¹ * uc22pwI3Jsl K))⁻¹) *
        (τ (α d) * (α (uc22pwI3Jsl K * d⁻¹ * uc22pwI3Jsl K))⁻¹)⁻¹) *
      (τ (b * (α d)⁻¹))⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ((hσU _).1 hu)
    (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2))) (Subgroup.inv_mem _ ((hτU _).1 hu))

end CFSG.LocalAnalysis.UniquenessCase.UC22
