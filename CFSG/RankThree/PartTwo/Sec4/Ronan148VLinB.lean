module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.Ronan148VElation
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VHeisTorus

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem exists_cube_root [Finite F] (h9 : 9 ∣ Nat.card F - 1) {s : Fˣ} (hs : s ^ 3 = 1) :
    ∃ μ : Fˣ, μ ^ 3 = s := by
  have := Fintype.ofFinite F
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hγo : orderOf γ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hγ s)
  obtain ⟨N9, hN9⟩ := h9
  have hN : orderOf γ = 9 * N9 := by rw [hγo, hN9]
  have h3j : (orderOf γ : ℤ) ∣ j * 3 := by
    rw [orderOf_dvd_iff_zpow_eq_one, _root_.zpow_mul, hj,
      show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hs
  rw [hN] at h3j
  obtain ⟨t, ht⟩ := h3j
  refine ⟨γ ^ ((N9 : ℤ) * t), ?_⟩
  rw [← zpow_natCast, ← _root_.zpow_mul, ← hj]
  congr 1
  push_cast at ht ⊢
  linarith

variable [Finite F] [CharP F 2]

theorem exists_type1_lift {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 1) {z : projectiveSL 3 F} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hinv : ∀ t : projectiveSL 3 F, t ^ 2 = 1 → t * z = z * t → t = 1) :
    ∃ Z : SpecialLinearGroup (Fin 3) F, proj 3 F Z = z ∧
      Type123 true (2 ^ (3 * n)) F (Matrix.SpecialLinearGroup.toGL Z) 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hK : PiField true 2 (3 * n) F := ⟨Nat.prime_two, by omega, hF⟩
  have hqt : ModThree true (2 ^ (3 * n)) := hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hqt
  obtain ⟨Z, rfl⟩ := proj_surjective 3 F z
  refine ⟨Z, rfl, ?_⟩
  set Zg := Matrix.SpecialLinearGroup.toGL Z with hZg
  have hZgc : (Zg : Matrix (Fin 3) (Fin 3) F) = (Z : Matrix (Fin 3) (Fin 3) F) := rfl
  have hZZ : Zg ∉ zPi true 3 (2 ^ (3 * n)) F := by
    intro hz
    obtain ⟨ξ, -, hξ⟩ := exists_scalar_of_mem_zPi hK hqt hτ hτ1 hz
    apply hz1
    apply proj_eq_one_of_eq_smul_one (a := (ξ : F))
    rw [← hZgc, ← hξ, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  obtain ⟨s, -, hs⟩ := exists_eq_smul_one_of_mem_scalars
    (proj_eq_one_iff.mp (by rw [map_pow]; exact hz3) : Z ^ 3 ∈ scalars 3 F)
  rw [Matrix.SpecialLinearGroup.coe_pow] at hs
  have hs3 : s ^ 3 = 1 := by
    have hdet := congrArg Matrix.det hs
    rw [Matrix.det_pow, Matrix.SpecialLinearGroup.det_coe, one_pow, det_smul, det_one,
      Fintype.card_fin, mul_one] at hdet
    exact hdet.symm
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs3
  have hZ3 : Zg ^ 3 ∈ zPi true 3 (2 ^ (3 * n)) F := by
    have : Zg ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs0) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hZgc, hs, GeneralLinearGroup.coe_scalar, scalar_apply,
        smul_one_eq_diagonal, Units.val_mk0]
    rw [this]
    exact scalar_mem_zPi hK hqt hτ hτ1 (mem_rootsOfUnity_of_card hF _)
  have hZH : Zg ∈ glPi true 3 (2 ^ (3 * n)) F := mem_glPi_true _ _
  rcases type123_exhaust hK hqt hZH hZZ hZ3 with h1 | ⟨e, he3, he1, ζ, hζ, g, -, hD⟩ | h3
  · exact h1
  ·
    exfalso
    set T₀ : GL (Fin 3) F := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h2]
      linear_combination h2, by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h2]
      linear_combination h2⟩ with hT₀
    have hT₀T₀ : T₀ * T₀ = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hT₀, mul_apply, Fin.sum_univ_three]
      linear_combination h2
    have hT₀D : T₀ * diagE e = diagE e * T₀ := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_diagE]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      fin_cases i <;> fin_cases j <;> simp [hT₀]
    set T : GL (Fin 3) F := g * T₀ * g⁻¹ with hT
    have hTdet : (T : Matrix (Fin 3) (Fin 3) F).det = 1 := by
      rw [hT, Units.val_mul, Units.val_mul, Matrix.det_units_conj, hT₀]
      simp [det_fin_three]
    set TS : SpecialLinearGroup (Fin 3) F := ⟨T, hTdet⟩ with hTS
    obtain ⟨ξ, -, rfl⟩ := exists_scalar_of_mem_zPi hK hqt hτ hτ1 hζ
    have hsc : ∀ A : GL (Fin 3) F, A * GeneralLinearGroup.scalar (Fin 3) ξ =
        GeneralLinearGroup.scalar (Fin 3) ξ * A := fun A =>
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ξ A).eq
    have hZD : Zg = g * diagE e * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ := by
      rw [← hD]
      group
    have hTZ : T * Zg = Zg * T := by
      rw [hZD, hT]
      have hs' : (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ * (g * T₀ * g⁻¹) =
          g * T₀ * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hsc]
        group
      calc g * T₀ * g⁻¹ * (g * diagE e * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹)
          = g * (T₀ * diagE e) * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ := by group
        _ = g * (diagE e * T₀) * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ := by rw [hT₀D]
        _ = g * diagE e * g⁻¹ * ((GeneralLinearGroup.scalar (Fin 3) ξ)⁻¹ * (g * T₀ * g⁻¹)) := by
            rw [hs']
            group
        _ = _ := by group
    have h1 := hinv (proj 3 F TS) (by
      rw [pow_two, ← map_mul]
      apply proj_eq_one_of_eq_smul_one (a := 1)
      rw [Matrix.SpecialLinearGroup.coe_mul, one_smul]
      change (T : Matrix (Fin 3) (Fin 3) F) * T = 1
      rw [← Units.val_mul, hT]
      calc ((g * T₀ * g⁻¹ * (g * T₀ * g⁻¹) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = ((g * (T₀ * T₀) * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
            congr 1
            group
        _ = 1 := by rw [hT₀T₀, mul_one, mul_inv_cancel, Units.val_one]) (by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      change (T : Matrix (Fin 3) (Fin 3) F) * (Zg : Matrix (Fin 3) (Fin 3) F) =
        (Zg : Matrix (Fin 3) (Fin 3) F) * T
      rw [← Units.val_mul, ← Units.val_mul, hTZ])
    obtain ⟨c, -, hc⟩ := exists_eq_smul_one_of_mem_scalars (proj_eq_one_iff.mp h1)
    have hT₀s : (T₀ : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
      have e1 : T₀ = g⁻¹ * T * g := by rw [hT]; group
      rw [e1, Units.val_mul, Units.val_mul]
      change ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (TS : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = _
      rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    have := congrFun (congrFun hT₀s 1) 2
    simp [hT₀] at this
  ·
    exfalso
    obtain ⟨-, -, hirr⟩ := h3
    have h9 : 9 ∣ Nat.card F - 1 := by
      rw [hF]
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · have h64 : 2 ^ (3 * n) = 64 ^ k := by
          rw [hk, show 3 * (k + k) = 6 * k by ring, pow_mul]
          norm_num
        rw [h64]
        have hm : 64 ^ k % 9 = 1 := by rw [Nat.pow_mod]; norm_num
        have : 1 ≤ 64 ^ k := Nat.one_le_pow _ _ (by norm_num)
        omega
      · exfalso
        have h8 : 2 ^ (3 * n) = 8 * 64 ^ k := by
          rw [hk, show 3 * (2 * k + 1) = 6 * k + 3 by ring, pow_add, pow_mul]
          norm_num
          ring
        rw [h8, Nat.mul_mod, Nat.pow_mod] at hq
        norm_num at hq
    have hsu3 : (Units.mk0 s hs0) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact hs3
    obtain ⟨μ, hμ⟩ := exists_cube_root h9 hsu3
    have hμs : (μ : F) ^ 3 = s := by
      have := congrArg Units.val hμ
      rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    set Y : Matrix (Fin 3) (Fin 3) F := (μ⁻¹ : F) • (Z : Matrix (Fin 3) (Fin 3) F) with hY
    have hY3 : Y * Y * Y = 1 := by
      have : (Z : Matrix (Fin 3) (Fin 3) F) * Z * Z = s • 1 := by rw [← hs]; rw [pow_three']
      rw [hY, smul_mul_smul_comm, smul_mul_smul_comm, this, smul_smul, ← hμs]
      rw [show (μ : F)⁻¹ * (μ : F)⁻¹ * (μ : F)⁻¹ * (μ : F) ^ 3 = 1 by
        field_simp [μ.ne_zero]]
      rw [one_smul]
    have hsum : 1 + τ + τ ^ 2 = 0 := one_add_tau_add_sq hτ hτ1
    have hprod : (Y - 1) * (Y - τ • 1) * (Y - τ ^ 2 • 1) = 0 := by
      have e : (Y - 1) * (Y - τ • 1) * (Y - τ ^ 2 • 1) =
          Y * Y * Y - (1 + τ + τ ^ 2) • (Y * Y) + (τ * (1 + τ + τ ^ 2)) • Y - τ ^ 3 • 1 := by
        simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
          Matrix.mul_one, smul_smul]
        module
      rw [e, hY3, hsum, hτ, zero_smul, mul_zero, zero_smul, sub_zero, add_zero, one_smul,
        sub_self]
    have hdet0 : ((Y - 1) * (Y - τ • 1) * (Y - τ ^ 2 • 1)).det = 0 := by
      rw [hprod]
      exact Matrix.det_zero
    rw [Matrix.det_mul, Matrix.det_mul] at hdet0
    obtain ⟨l, v, hv0, hv⟩ : ∃ (l : F) (v : Fin 3 → F), v ≠ 0 ∧ (Y - l • 1) *ᵥ v = 0 := by
      rcases mul_eq_zero.mp hdet0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
          exact ⟨1, v, hv0, by rw [one_smul]; exact hv⟩
        · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
          exact ⟨τ, v, hv0, hv⟩
      · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
        exact ⟨τ ^ 2, v, hv0, hv⟩
    have hZv : (Zg : Matrix (Fin 3) (Fin 3) F) *ᵥ v = ((μ : F) * l) • v := by
      rw [hZgc]
      have h1 : Y *ᵥ v = l • v := by
        simp only [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv
        exact hv
      rw [hY, smul_mulVec] at h1
      have h4 := congrArg (fun w => (μ : F) • w) h1
      simp only [smul_smul, mul_inv_cancel₀ μ.ne_zero, one_smul] at h4
      exact h4
    rcases hirr (Submodule.span F {v}) (by
      intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [mulVec_smul, hZv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)) with h | h
    · exact hv0 ((Submodule.span_singleton_eq_bot).mp h)
    · have h1 := congrArg (fun W : Submodule F (Fin 3 → F) => Module.finrank F W) h
      rw [finrank_span_singleton hv0, finrank_top, Module.finrank_fin_fun] at h1
      omega

omit [Finite F] [CharP F 2] in
theorem exists_cycThree_pow_mul_of_commute {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Z r : SpecialLinearGroup (Fin 3) F} {g ζ : GL (Fin 3) F}
    (hζ : ζ ∈ StatedScalars (Fin 3) F)
    (hD : g⁻¹ * (Matrix.SpecialLinearGroup.toGL Z * ζ) * g = diagTau hτ)
    (hrc : proj 3 F r * proj 3 F Z = proj 3 F Z * proj 3 F r) :
    ∃ k : ℕ, k < 3 ∧ ∃ ν : Fˣ, (ν : F) = τ ^ (2 * k) ∧
      Matrix.SpecialLinearGroup.toGL r * Matrix.SpecialLinearGroup.toGL Z *
          (Matrix.SpecialLinearGroup.toGL r)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ν * Matrix.SpecialLinearGroup.toGL Z ∧
      ∃ a b e : Fˣ,
        g⁻¹ * Matrix.SpecialLinearGroup.toGL r * g = cycThree ^ k * diagUnits a b e := by
  obtain ⟨ξ, rfl⟩ := hζ
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  set Zg := Matrix.SpecialLinearGroup.toGL Z with hZg
  set rg := Matrix.SpecialLinearGroup.toGL r with hrg
  obtain ⟨ν, hν0, hν⟩ := exists_smul_of_proj_eq (A := Z) (B := r * Z * r⁻¹) (by
    rw [map_mul, map_mul, map_inv, hrc, mul_inv_cancel_right])
  have h1 : rg * Zg * rg⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0) * Zg := by
    apply Units.ext
    rw [hrg, hZg, ← map_inv, ← map_mul, ← map_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
      scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Units.val_mk0]
    exact hν
  have h2 : (g⁻¹ * rg * g) * diagTau hτ * (g⁻¹ * rg * g)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0) * diagTau hτ := by
    rw [← hD]
    set S := GeneralLinearGroup.scalar (Fin 3) ξ with hS
    set N := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν hν0) with hN
    have e1 : S * rg⁻¹ = rg⁻¹ * S := (hsc ξ rg⁻¹).symm
    have e2 : g⁻¹ * N = N * g⁻¹ := hsc _ g⁻¹
    calc g⁻¹ * rg * g * (g⁻¹ * (Zg * S) * g) * (g⁻¹ * rg * g)⁻¹
        = g⁻¹ * rg * Zg * (S * rg⁻¹) * g := by group
      _ = g⁻¹ * (rg * Zg * rg⁻¹) * S * g := by rw [e1]; group
      _ = (g⁻¹ * N) * Zg * S * g := by rw [h1]; group
      _ = N * (g⁻¹ * (Zg * S) * g) := by rw [e2]; group
  obtain ⟨k, hk, hkν, a, b, e, hab⟩ := exists_cycThree_pow_mul_of_conj hτ hτ1 h2
  exact ⟨k, hk, Units.mk0 ν hν0, hkν, h1, a, b, e, hab⟩

omit [Finite F] [CharP F 2] in
theorem exists_diagUnits_of_commute {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Z r : SpecialLinearGroup (Fin 3) F} {g ζ : GL (Fin 3) F}
    (hζ : ζ ∈ StatedScalars (Fin 3) F)
    (hD : g⁻¹ * (Matrix.SpecialLinearGroup.toGL Z * ζ) * g = diagTau hτ)
    (hrc : proj 3 F r * proj 3 F Z = proj 3 F Z * proj 3 F r) {M : ℕ} (hM : Nat.Coprime M 3)
    (hrM : proj 3 F r ^ M = 1) :
    ∃ a b e : Fˣ, g⁻¹ * Matrix.SpecialLinearGroup.toGL r * g = diagUnits a b e := by
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  obtain ⟨k, hk, -, -, -, a, b, e, hab⟩ := exists_cycThree_pow_mul_of_commute hτ hτ1 hζ hD hrc
  set rg := Matrix.SpecialLinearGroup.toGL r with hrg
  have hk0 : k = 0 := by
    by_contra hk0
    have hcube : ∃ u : Fˣ, (g⁻¹ * rg * g) ^ 3 = GeneralLinearGroup.scalar (Fin 3) u := by
      rw [hab]
      rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
      · exact ⟨_, by rw [pow_one]; exact cycThree_mul_diagUnits_pow_three a b e⟩
      · exact ⟨_, cycThree_sq_mul_diagUnits_pow_three a b e⟩
    obtain ⟨u, hu⟩ := hcube
    have hr3 : rg ^ 3 = GeneralLinearGroup.scalar (Fin 3) u := by
      have e1 : (g⁻¹ * rg * g) ^ 3 = g⁻¹ * rg ^ 3 * g := by
        have := conj_pow (a := g⁻¹) (b := rg) (i := 3)
        rwa [inv_inv] at this
      rw [e1] at hu
      calc rg ^ 3 = g * (g⁻¹ * rg ^ 3 * g) * g⁻¹ := by group
        _ = g * GeneralLinearGroup.scalar (Fin 3) u * g⁻¹ := by rw [hu]
        _ = GeneralLinearGroup.scalar (Fin 3) u := by rw [hsc, mul_inv_cancel_right]
    have hp3 : proj 3 F r ^ 3 = 1 := by
      rw [← map_pow]
      apply proj_eq_one_of_eq_smul_one (a := (u : F))
      have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hr3
      simp only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, scalar_apply] at this
      rw [Matrix.SpecialLinearGroup.coe_pow, ← smul_one_eq_diagonal] at *
      exact this
    have hp1 : proj 3 F r = 1 := by
      have h := pow_gcd_eq_one.mpr ⟨hp3, hrM⟩
      rwa [Nat.gcd_comm, Nat.Coprime.gcd_eq_one hM, pow_one] at h
    obtain ⟨s, -, hs⟩ := exists_eq_smul_one_of_mem_scalars (proj_eq_one_iff.mp hp1)
    have hcD : ((cycThree ^ k * diagUnits a b e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        s • 1 := by
      rw [← hab]
      have : g⁻¹ * rg * g = rg := by
        have hr : rg = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s (by
          rintro rfl
          have := congrArg Matrix.det hs
          rw [Matrix.SpecialLinearGroup.det_coe, zero_smul, Matrix.det_zero] at this
          exact one_ne_zero this)) := by
          apply Units.ext
          rw [hrg, GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0,
            ← smul_one_eq_diagonal]
          exact hs
        rw [hr, hsc, inv_mul_cancel_right]
      rw [this, hrg]
      exact hs
    rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · have := congrFun (congrFun hcD 1) 0
      rw [pow_one, Units.val_mul, coe_cycThree, coe_diagUnits] at this
      simp [Matrix.mul_apply, Fin.sum_univ_three] at this
    · have := congrFun (congrFun hcD 0) 1
      rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_cycThree, coe_diagUnits, pow_two] at this
      simp [Matrix.mul_apply, Fin.sum_univ_three] at this
  subst hk0
  exact ⟨a, b, e, by rw [hab, pow_zero, one_mul]⟩

omit [Finite F] [CharP F 2] in
theorem conj_eq_inv_scalar_mul {A B : GL (Fin 3) F} {μ : Fˣ}
    (h : A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * B) :
    B * A * B⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A := by
  have hsc : ∀ (u : Fˣ) (C : GL (Fin 3) F),
      C * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * C :=
    fun u C => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u C).eq
  have h1 : A * B = GeneralLinearGroup.scalar (Fin 3) μ * B * A := by
    rw [← h]
    group
  have hs : GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc B * A * B⁻¹ = (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ *
        GeneralLinearGroup.scalar (Fin 3) μ) * (B * A) * B⁻¹ := by rw [hs, one_mul]
    _ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * B * A) *
        B⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A * B) * B⁻¹ := by rw [h1]
    _ = GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * A := by group

omit [Finite F] [CharP F 2] in
theorem commute_of_conj_diagUnits {g A B : GL (Fin 3) F} {a b c a' b' c' : Fˣ}
    (hA : g⁻¹ * A * g = diagUnits a b c) (hB : g⁻¹ * B * g = diagUnits a' b' c') :
    A * B = B * A := by
  have hA' : A = g * diagUnits a b c * g⁻¹ := by rw [← hA]; group
  have hB' : B = g * diagUnits a' b' c' * g⁻¹ := by rw [← hB]; group
  have hc : diagUnits a b c * diagUnits a' b' c' = diagUnits a' b' c' * diagUnits a b c := by
    rw [diagUnits_mul, diagUnits_mul, mul_comm a, mul_comm b, mul_comm c]
  rw [hA', hB']
  calc g * diagUnits a b c * g⁻¹ * (g * diagUnits a' b' c' * g⁻¹) =
      g * (diagUnits a b c * diagUnits a' b' c') * g⁻¹ := by group
    _ = g * (diagUnits a' b' c' * diagUnits a b c) * g⁻¹ := by rw [hc]
    _ = g * diagUnits a' b' c' * g⁻¹ * (g * diagUnits a b c * g⁻¹) := by group

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
