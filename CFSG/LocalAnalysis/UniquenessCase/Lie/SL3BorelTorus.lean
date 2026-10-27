module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem uc22pwI3dSL_mem_diagonalTorus (a : Kˣ) :
    uc22pwI3dSL K a ∈ SpecialLinearGroup.diagonalTorus K 3 :=
  SpecialLinearGroup.mem_diagonalTorus_iff.mpr (by
    rw [coe_uc22pwI3dSL]; exact isDiag_diagonal _)

theorem uc22pwI3TorusMap_dSL [CharP K 2] (ε : Bool) (i : ℕ) (a : Kˣ) :
    uc22pwI3TorusMap K ε i (uc22pwI3dSL K a) = uc22pwI3dSL K (a ^ 2 ^ i) := by
  have hJ : (uc22pwI3Jsl K)⁻¹ = uc22pwI3Jsl K := inv_eq_of_mul_eq_one_right uc22pwI3Jsl_mul_self
  cases ε
  · simp [uc22pwI3TorusMap, map_pow]
  · simp only [uc22pwI3TorusMap, if_true, ← map_pow, ← map_inv]
    have h := uc22pwI3Jsl_conj_dSL (K := K) (a ^ 2 ^ i)⁻¹
    rw [hJ] at h
    rw [h, map_inv, inv_inv]

theorem uc22pwI3_eq_one_of_torus_mem {X : Type} [Group X]
    (α : SpecialLinearGroup (Fin 3) K →* X)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    {d : SpecialLinearGroup (Fin 3) K} (hd : d ∈ SpecialLinearGroup.diagonalTorus K 3)
    (hdU : α d ∈ (unitriangular 3 K).map α) : α d = 1 := by
  obtain ⟨u, hu, hud⟩ := hdU
  have hz : u⁻¹ * d ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hud, inv_mul_cancel]
  obtain ⟨c, -, hzc⟩ := uc22pwI3_center_scalar (Subgroup.inv_mem _ (hαc hz))
  have hdiag : (d : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    SpecialLinearGroup.mem_diagonalTorus_iff.mp hd
  have hu_eq : u = d * (u⁻¹ * d)⁻¹ := by group
  have hm : (u : Matrix (Fin 3) (Fin 3) K) =
      (d : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    conv_lhs => rw [hu_eq]
    rw [Matrix.SpecialLinearGroup.coe_mul, hzc]
  have hu1 : u = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · subst hij
      simpa using hu.2 i
    · rw [hm, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij, scalar_apply,
        Matrix.mul_diagonal, hdiag hij, zero_mul]
  rw [← hud, hu1, map_one]

theorem uc22pwI3_exists_torus_of_mem_normalizer [Finite K] [CharP K 2] {X : Type}
    [Group X] (α : SpecialLinearGroup (Fin 3) K →* X) (hα : Function.Surjective α)
    (hαc : α.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K)) {b : X}
    (hb : b ∈ normalizer (((unitriangular 3 K).map α : Subgroup X) : Set X)) :
    ∃ d ∈ SpecialLinearGroup.diagonalTorus K 3,
      b * (α d)⁻¹ ∈ (unitriangular 3 K).map α := by
  obtain ⟨g, rfl⟩ := hα b
  have hU₀ : IsPGroup 2 (unitriangular 3 K) := by
    obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
    rw [← hQ]
    exact Q.isPGroup'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hU₀
  have hpow : ∀ s ∈ unitriangular 3 K, s ^ 2 ^ k = 1 := by
    intro s hs
    have h1 := pow_card_eq_one' (G := unitriangular 3 K) (x := (⟨s, hs⟩ : unitriangular 3 K))
    rw [hk] at h1
    exact congrArg Subtype.val h1
  have key : ∀ y : SpecialLinearGroup (Fin 3) K,
      α y ∈ normalizer (((unitriangular 3 K).map α : Subgroup X) : Set X) →
        ∀ s ∈ unitriangular 3 K, y * s * y⁻¹ ∈ unitriangular 3 K := by
    intro y hy s hs
    have h1 : α (y * s * y⁻¹) ∈ (unitriangular 3 K).map α := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hy _).1 ⟨s, hs, rfl⟩
    obtain ⟨u₀, hu₀, hu₀eq⟩ := h1
    have hzker : u₀⁻¹ * (y * s * y⁻¹) ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu₀eq, inv_mul_cancel]
    have hzc := hαc hzker
    have e : y * s * y⁻¹ = u₀ * (u₀⁻¹ * (y * s * y⁻¹)) := by group
    have hN1 : (y * s * y⁻¹) ^ 2 ^ k = 1 := by
      have h2 := map_pow (MulAut.conj y) s (2 ^ k)
      simp only [MulAut.conj_apply] at h2
      rw [← h2, hpow s hs]
      group
    have hz1 : (u₀⁻¹ * (y * s * y⁻¹)) ^ 2 ^ k = 1 := by
      have h2 : (y * s * y⁻¹) ^ 2 ^ k = u₀ ^ 2 ^ k * (u₀⁻¹ * (y * s * y⁻¹)) ^ 2 ^ k := by
        conv_lhs => rw [e]
        exact (Commute.mul_pow (Subgroup.mem_center_iff.1 hzc u₀) _)
      rw [hN1, hpow u₀ hu₀, one_mul] at h2
      exact h2.symm
    have hz3 := uc22pwI3_center_pow_three hzc
    have hord : orderOf (u₀⁻¹ * (y * s * y⁻¹)) ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz1) (orderOf_dvd_of_pow_eq_one hz3)
    have hgcd : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [hgcd] at hord
    have hz : u₀⁻¹ * (y * s * y⁻¹) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
    rw [hz, mul_one] at e
    rw [e]
    exact hu₀
  have hg : g ∈ normalizer ((unitriangular 3 K : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => key g hb s hs, fun hs => ?_⟩
    have hb' : α g⁻¹ ∈ normalizer (((unitriangular 3 K).map α : Subgroup X) : Set X) := by
      rw [map_inv]
      exact inv_mem hb
    have := key g⁻¹ hb' _ hs
    simpa [mul_assoc] using this
  rw [normalizer_unitriangular] at hg
  obtain ⟨u, hu, d, hd, rfl⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.exists_unitriangular_mul_diagonal hg
  exact ⟨d, SpecialLinearGroup.mem_diagonalTorus_iff.mpr hd, ⟨u, hu, by simp⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
