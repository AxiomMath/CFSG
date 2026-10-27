module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
import CFSG.RankThree.PartTwo.Sec13.Item13K410

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138V

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K]

theorem det_diagTau {τ : K} (hτ : τ ^ 3 = 1) : GeneralLinearGroup.det (diagTau hτ) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_diagTau_eq_diagonal, det_diagonal, Fin.prod_univ_three,
    Units.val_one]
  show τ * τ ^ 2 * 1 = 1
  rw [mul_one, ← pow_succ']
  exact hτ

theorem det_scalar_units (u : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]

theorem eq_one_of_scalar_eq_one {u : Kˣ} (h : GeneralLinearGroup.scalar (Fin 3) u = 1) :
    u = 1 := by
  apply Units.ext
  have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simpa [GeneralLinearGroup.coe_scalar] using this

theorem det_commutator_eq_one (a b : GL (Fin 3) K) :
    GeneralLinearGroup.det (a * b * a⁻¹ * b⁻¹) = 1 := by
  have key : ∀ x y : Kˣ, x * y * x⁻¹ * y⁻¹ = 1 := fun x y => by rw [mul_comm x y]; group
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  exact key _ _

theorem exists_diagUnits_of_commute_of_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y z g X : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hD : g⁻¹ * (Y * z) * g = diagTau hτ) (hX : X * Y = Y * X) :
    ∃ a b e : Kˣ, g⁻¹ * X * g = diagUnits a b e := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have hXz : X * (Y * z) = (Y * z) * X := by
    calc X * (Y * z) = (X * Y) * z := by group
      _ = Y * (X * z) := by rw [hX]; group
      _ = (Y * z) * X := by rw [commute_of_mem_statedScalars hz X]; group
  have hc : (g⁻¹ * X * g) * diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 =
      diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 * (g⁻¹ * X * g) := by
    rw [← diagTau_eq_diagUnits hτ hτ0, ← hD]
    calc g⁻¹ * X * g * (g⁻¹ * (Y * z) * g) = g⁻¹ * (X * (Y * z)) * g := by group
      _ = g⁻¹ * ((Y * z) * X) * g := by rw [hXz]
      _ = g⁻¹ * (Y * z) * g * (g⁻¹ * X * g) := by group
  refine Sec12.KS128Move.exists_diagUnits_of_commute ?_ ?_ ?_ hc
  · intro h
    have h' := congrArg Units.val h
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at h'
    apply hτ1
    have : τ * (τ - 1) = 0 := by linear_combination -h'
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hτ0)
  · intro h
    apply hτ1
    simpa using congrArg Units.val h
  · intro h
    have h' := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h'
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h', div_one]

theorem commute_of_commute_of_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y z g A B : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hD : g⁻¹ * (Y * z) * g = diagTau hτ) (hA : A * Y = Y * A) (hB : B * Y = Y * B) :
    A * B = B * A := by
  obtain ⟨a, b, e, hab⟩ := exists_diagUnits_of_commute_of_diagTau hτ hτ1 hz hD hA
  obtain ⟨a', b', e', hab'⟩ := exists_diagUnits_of_commute_of_diagTau hτ hτ1 hz hD hB
  have hA' : A = g * diagUnits a b e * g⁻¹ := by rw [← hab]; group
  have hB' : B = g * diagUnits a' b' e' * g⁻¹ := by rw [← hab']; group
  have hc : diagUnits a b e * diagUnits a' b' e' = diagUnits a' b' e' * diagUnits a b e := by
    rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm e]
  rw [hA', hB']
  calc g * diagUnits a b e * g⁻¹ * (g * diagUnits a' b' e' * g⁻¹) =
      g * (diagUnits a b e * diagUnits a' b' e') * g⁻¹ := by group
    _ = g * (diagUnits a' b' e' * diagUnits a b e) * g⁻¹ := by rw [hc]
    _ = g * diagUnits a' b' e' * g⁻¹ * (g * diagUnits a b e * g⁻¹) := by group

theorem not_irreducible_of_commute_of_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y z g X : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hD : g⁻¹ * (Y * z) * g = diagTau hτ) (hX : X * Y = Y * X) :
    ¬ ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (X : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  obtain ⟨a, b, e, hab⟩ := exists_diagUnits_of_commute_of_diagTau hτ hτ1 hz hD hX
  refine not_irreducible_of_diag (z := 1) (g := g) (one_mem _) (d := ![(a : K), b, e]) ?_
  rw [mul_one, hab, coe_diagUnits]

theorem pow_three_eq_scalar_det_of_diagTau {τ : K} (hτ : τ ^ 3 = 1) {Y z g : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K) (hD : g⁻¹ * (Y * z) * g = diagTau hτ) :
    Y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det Y) := by
  obtain ⟨ζ, rfl⟩ := hz
  have hYz : Y * GeneralLinearGroup.scalar (Fin 3) ζ = g * diagTau hτ * g⁻¹ := by
    rw [← hD]
    group
  have hc : Commute Y (GeneralLinearGroup.scalar (Fin 3) ζ) :=
    CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ Y
  have h1 : Y ^ 3 * GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) = 1 := by
    rw [map_pow, ← hc.mul_pow, hYz, conj_pow, diagTau_pow_three hτ, mul_one, mul_inv_cancel]
  have h2 : GeneralLinearGroup.det Y * ζ ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det hYz
    rw [map_mul, map_mul, map_mul, map_inv, det_diagTau hτ, mul_one, det_scalar_units,
      mul_inv_cancel] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left h1, eq_inv_of_mul_eq_one_left h2, map_inv]

theorem scalar_mul_pow_pow_three {Y : GL (Fin 3) K}
    (hY : Y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det Y)) (l : Kˣ)
    (n : ℕ) :
    (GeneralLinearGroup.scalar (Fin 3) l * Y ^ n) ^ 3 = GeneralLinearGroup.scalar (Fin 3)
      (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) l * Y ^ n)) := by
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) l) (Y ^ n) :=
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l (Y ^ n)).symm
  rw [hc.mul_pow, ← pow_mul, mul_comm n 3, pow_mul, hY, map_mul, map_pow, det_scalar_units,
    map_mul, map_pow, map_pow]

theorem commutator_pow_three_of_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M z g y₀ : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hD : g⁻¹ * (M ^ 3 * z) * g = diagTau hτ) {μ : Kˣ}
    (hy₀ : y₀ * M ^ 3 * y₀⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * M ^ 3) :
    (y₀ * M * y₀⁻¹ * M⁻¹) ^ 3 = GeneralLinearGroup.scalar (Fin 3) μ := by
  set S := GeneralLinearGroup.scalar (Fin 3) μ with hS
  set N := y₀ * M * y₀⁻¹ with hN
  have hN3 : N ^ 3 = S * M ^ 3 := by
    rw [hN, conj_pow, hy₀]
  have hSN : N * S⁻¹ = S⁻¹ * N :=
    commute_of_mem_statedScalars (inv_mem (⟨μ, rfl⟩ : S ∈ StatedScalars (Fin 3) K)) N
  have hNY : N * M ^ 3 = M ^ 3 * N := by
    have hM3 : M ^ 3 = S⁻¹ * N ^ 3 := by
      rw [hN3]
      group
    rw [hM3]
    calc N * (S⁻¹ * N ^ 3) = (N * S⁻¹) * N ^ 3 := by group
      _ = S⁻¹ * (N * N ^ 3) := by rw [hSN]; group
      _ = S⁻¹ * (N ^ 3 * N) := by rw [← pow_succ', ← pow_succ]
      _ = S⁻¹ * N ^ 3 * N := by group
  have hMY : M * M ^ 3 = M ^ 3 * M := by
    rw [← pow_succ', ← pow_succ]
  have hNM : Commute N M := commute_of_commute_of_diagTau hτ hτ1 hz hD hNY hMY
  calc (N * M⁻¹) ^ 3 = N ^ 3 * M⁻¹ ^ 3 := hNM.inv_right.mul_pow 3
    _ = S * M ^ 3 * (M ^ 3)⁻¹ := by rw [hN3, inv_pow]
    _ = S := by group

theorem false_of_diagTau_cube {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {M z g y₀ : GL (Fin 3) K} (hz : z ∈ StatedScalars (Fin 3) K)
    (hD : g⁻¹ * (M ^ 3 * z) * g = diagTau hτ) {μ : Kˣ}
    (hy₀ : y₀ * M ^ 3 * y₀⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * M ^ 3)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (y₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    {l : Kˣ} {n : ℕ}
    (hU : y₀ * M * y₀⁻¹ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) l * (M ^ 3) ^ n) :
    False := by
  have h1 := commutator_pow_three_of_diagTau hτ hτ1 hz hD hy₀
  have h2 := scalar_mul_pow_pow_three (pow_three_eq_scalar_det_of_diagTau hτ hz hD) l n
  rw [← hU, det_commutator_eq_one, map_one] at h2
  rw [h2] at h1
  have hμ : μ = 1 := eq_one_of_scalar_eq_one h1.symm
  subst hμ
  rw [map_one, one_mul] at hy₀
  have hc : y₀ * M ^ 3 = M ^ 3 * y₀ := by
    calc y₀ * M ^ 3 = y₀ * M ^ 3 * y₀⁻¹ * y₀ := by group
      _ = M ^ 3 * y₀ := by rw [hy₀]
  exact not_irreducible_of_commute_of_diagTau hτ hτ1 hz hD hc hirr

variable {π : Bool} {p f : ℕ}

theorem not_type123_three_pow_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (M : GL (Fin 3) K) : ¬ Type123 π (p ^ f) K (M ^ 3) 3 := by
  rintro ⟨-, hY3, hirr⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hY3
  have hyM : ((M ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (ξ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hξ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hnc := Sec12.KS128NotHJTC.not_cube_of_irreducible hτ hτ1 (hK.three_ne_zero hq) hyM hirr
  have hdet := det_eq_of_cube hnc hyM
  apply hnc (M : Matrix (Fin 3) (Fin 3) K).det
  rw [← hdet, Units.val_pow_eq_pow_val, Matrix.det_pow]

theorem false_of_cube_root_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {M y₀ : GL (Fin 3) K} (hMH : M ∈ glPi π 3 (p ^ f) K)
    (hMZ : M ^ 3 ∉ StatedScalars (Fin 3) K) (hM9 : (M ^ 3) ^ 3 ∈ StatedScalars (Fin 3) K)
    (hy₀ : Type123 π (p ^ f) K y₀ 3)
    (hcomm : y₀ * M ^ 3 * y₀⁻¹ * (M ^ 3)⁻¹ ∈ StatedScalars (Fin 3) K)
    (hU : (y₀ * M * y₀⁻¹ * M⁻¹) ^ 3 ∈ StatedScalars (Fin 3) K →
      ∃ n : ℕ, y₀ * M * y₀⁻¹ * M⁻¹ * ((M ^ 3) ^ n)⁻¹ ∈ StatedScalars (Fin 3) K) :
    False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, -, hirr⟩ := hy₀
  have hYH : M ^ 3 ∈ glPi π 3 (p ^ f) K := pow_mem hMH 3
  have hYZ : M ^ 3 ∉ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact fun h => hMZ h.2
  have hY3 : (M ^ 3) ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact ⟨pow_mem hYH 3, hM9⟩
  obtain ⟨μ, hμ⟩ := hcomm
  have hy₀M : y₀ * M ^ 3 * y₀⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * M ^ 3 := by
    rw [hμ]
    group
  rcases type123_exhaust hK hq hYH hYZ hY3 with h1 | h2 | h3
  · obtain ⟨τ', hτ', hτ'1, z, hz, g, -, hD⟩ := h1
    have hzS := mem_statedScalars_of_mem_zPi hK hq hτ' hτ'1 hz
    have hU3 : (y₀ * M * y₀⁻¹ * M⁻¹) ^ 3 ∈ StatedScalars (Fin 3) K := by
      rw [commutator_pow_three_of_diagTau hτ' hτ'1 hzS hD hy₀M]
      exact ⟨μ, rfl⟩
    obtain ⟨n, l, hl⟩ := hU hU3
    have hU' : y₀ * M * y₀⁻¹ * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) l * (M ^ 3) ^ n := by
      rw [hl]
      group
    exact false_of_diagTau_cube hτ' hτ'1 hzS hD hy₀M hirr hU'
  · exact Sec13.not_irreducible_of_commute_type2 hK hq h2 ⟨μ, hμ⟩ hirr
  · exact not_type123_three_pow_three hK hq M h3

end CFSG.RankThree.PartTwo.Sec13.Ronan138V
