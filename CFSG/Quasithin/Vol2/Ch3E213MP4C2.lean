module

public import CFSG.Quasithin.Vol2.Ch3E213MP4C1

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem realize_mk {J : HermitianForm 3 K} {β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    {σ : K ≃+* K} {A : GL (Fin 3) K}
    (hβ : ∀ g : J.specialSubgroup,
      ((β ⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), Subgroup.mem_map_of_mem _ g.2⟩ :
          ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹))
    (y : ProjectiveSpecialUnitaryMatrixGroup J) (M : GL (Fin 3) K)
    (hyM : (y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M) :
    (β y : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom M * A⁻¹) := by
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
  have hy : y = ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ := Subtype.ext hgy.symm
  have key : ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom g) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom M) := by
    rw [← ProjGenLinGroup.map_mk, ← ProjGenLinGroup.map_mk, hgy, hyM]
  rw [hy, hβ ⟨g, hg⟩, map_mul, map_mul, map_mul, map_mul, key]

theorem upper_of_normalizes (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hβB : ∀ x ∈ unitaryCoordinateStabilizer J 0, β x ∈ unitaryCoordinateStabilizer J 0)
    {σ : K ≃+* K} {A : GL (Fin 3) K}
    (hβ : ∀ g : J.specialSubgroup,
      ((β ⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), Subgroup.mem_map_of_mem _ g.2⟩ :
          ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹)) :
    (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinv, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  let ψ := hermitianUnipotentPSU J hJ
  have hψ (z : hermitianUnipotentCoord J) : ((ψ z : ProjectiveSpecialUnitaryMatrixGroup J) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (hermitianUnipotentGL J z) := rfl
  have hone : J.conj 1 = 1 := map_one _
  have h₁ : ψ (centralCoord J 1 hone) ∈ unitaryCoordinateStabilizer J 0 ∧
      orderOf (ψ (centralCoord J 1 hone)) = 2 :=
    (hinv _).mpr ⟨1, _, by rw [hone, CharTwo.add_self_eq_zero], one_ne_zero,
      centralCoord_matrix J 1 hone, hψ _⟩
  obtain ⟨b, M', -, hb0, hM', hθ₁⟩ := (hinv (β (ψ (centralCoord J 1 hone)))).mp
    ⟨hβB _ h₁.1, by rw [MulEquiv.orderOf_eq]; exact h₁.2⟩
  have hσ₁ : GeneralLinearGroup.map σ.toRingHom (hermitianUnipotentGL J (centralCoord J 1 hone)) =
      hermitianUnipotentGL J (centralCoord J 1 hone) := by
    apply GeneralLinearGroup.ext
    intro i j
    rw [GeneralLinearGroup.map_apply, centralCoord_matrix]
    fin_cases i <;> fin_cases j <;> simp
  have h₂ := realize_mk hβ _ _ (hψ (centralCoord J 1 hone))
  rw [hσ₁, hθ₁] at h₂
  obtain ⟨c, -, hc⟩ := exists_smul_of_mk_eq h₂
  have hmat : (A : Matrix (Fin 3) (Fin 3) K) * !![1, 0, 1; 0, 1, 0; 0, 0, 1] =
      c • (!![1, 0, b; 0, 1, 0; 0, 0, 1] * (A : Matrix (Fin 3) (Fin 3) K)) := by
    rw [← centralCoord_matrix J 1 hone, ← hM', ← Units.val_mul, ← Matrix.smul_mul, ← hc,
      ← Units.val_mul, inv_mul_cancel_right]
  obtain ⟨hA10, hA20, hA21, -⟩ := central_root_conj_entries hdetA hb0 hmat
  exact ⟨hA10, hA20, hA21⟩

theorem cube_fixed_of_centralizes (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hβB : ∀ x ∈ unitaryCoordinateStabilizer J 0, β x ∈ unitaryCoordinateStabilizer J 0)
    (hβT : ∀ c : Kˣ, β (torusPSU J hJ c) * (torusPSU J hJ c)⁻¹ ∈
      (hermitianUnipotentPSU J hJ).range)
    {σ : K ≃+* K} {A : GL (Fin 3) K}
    (hβ : ∀ g : J.specialSubgroup,
      ((β ⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), Subgroup.mem_map_of_mem _ g.2⟩ :
          ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom (g : GL (Fin 3) K) * A⁻¹)) :
    ∀ x : K, σ x ^ 3 = x ^ 3 := by
  obtain ⟨hA10, hA20, hA21⟩ := upper_of_normalizes J hf hcard hfixed hJ hβB hβ
  have hdetA : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact (GeneralLinearGroup.det A).ne_zero
  have hdet3 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 * (A : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    have h := hdetA
    rw [Matrix.det_fin_three, hA10, hA20, hA21] at h
    simpa using h
  intro x
  by_cases hx : x = 0
  · simp [hx]
  set c : Kˣ := Units.mk0 x hx with hcdef
  obtain ⟨z, hz⟩ := hβT c
  have h1 : β (torusPSU J hJ c) = hermitianUnipotentPSU J hJ z * torusPSU J hJ c := by
    rw [hz, inv_mul_cancel_right]
  have h2 := realize_mk hβ (torusPSU J hJ c) (torusGL J c) (torusPSU_val J hJ c)
  rw [h1, Subgroup.coe_mul, torusPSU_val] at h2
  have h3 : ((hermitianUnipotentPSU J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) :
      ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (hermitianUnipotentGL J z) := rfl
  rw [h3, ← map_mul] at h2
  obtain ⟨μ, hμ0, hμ⟩ := exists_smul_of_mk_eq h2
  have hσt : (GeneralLinearGroup.map σ.toRingHom (torusGL J c) : Matrix (Fin 3) (Fin 3) K) =
      !![σ x, 0, 0; 0, σ (J.conj x / x), 0; 0, 0, σ (J.conj x)⁻¹] := by
    ext i j
    rw [GeneralLinearGroup.map_apply, torusGL_val]
    fin_cases i <;> fin_cases j <;> simp [torusMatrix, hcdef]
  have ht : (torusGL J c : Matrix (Fin 3) (Fin 3) K) =
      !![x, 0, 0; 0, J.conj x / x, 0; 0, 0, (J.conj x)⁻¹] := by
    rw [torusGL_val]
    rfl
  have e1 : A * GeneralLinearGroup.map σ.toRingHom (torusGL J c) =
      A * GeneralLinearGroup.map σ.toRingHom (torusGL J c) * A⁻¹ * A := by group
  have hmat : (A : Matrix (Fin 3) (Fin 3) K) * !![σ x, 0, 0; 0, σ (J.conj x / x), 0;
      0, 0, σ (J.conj x)⁻¹] = μ • ((hermitianUnipotentGL J z : Matrix (Fin 3) (Fin 3) K) *
        !![x, 0, 0; 0, J.conj x / x, 0; 0, 0, (J.conj x)⁻¹] * (A : Matrix (Fin 3) (Fin 3) K)) := by
    calc (A : Matrix (Fin 3) (Fin 3) K) * !![σ x, 0, 0; 0, σ (J.conj x / x), 0;
          0, 0, σ (J.conj x)⁻¹] =
        ((A * GeneralLinearGroup.map σ.toRingHom (torusGL J c) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) := by rw [← hσt, Units.val_mul]
      _ = ((A * GeneralLinearGroup.map σ.toRingHom (torusGL J c) * A⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
        rw [← Units.val_mul, ← e1]
      _ = _ := by rw [hμ, Matrix.smul_mul, Units.val_mul, ht]
  have hN := hermitianUnipotentGL_val J z
  obtain ⟨e0, e1, e2⟩ := diag_conj_entries hA10 hA20 hA21
    (left_ne_zero_of_mul (left_ne_zero_of_mul hdet3)) (right_ne_zero_of_mul
      (left_ne_zero_of_mul hdet3)) (right_ne_zero_of_mul hdet3) (by rw [hN]; simp)
    (by rw [hN]; simp) (by rw [hN]; simp) (by rw [hN]; simp) (by rw [hN]; simp)
    (by rw [hN]; simp) hmat
  have hcx : J.conj x ≠ 0 := (map_ne_zero _).mpr hx
  have hcube := cube_eq_one_of_torus hx hcx ((map_ne_zero σ).mpr hx) e0
    (by rw [← map_div₀]; exact e1) (by rw [← map_inv₀]; exact e2)
  rw [e0, mul_pow, hcube, one_mul]

end CFSG.Quasithin.Ch3E213M.P4C
