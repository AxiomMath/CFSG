module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentGen
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTorus
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentSinger
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K]

theorem pow_nine_mul_add {u : K} (hu : u ^ 9 = 1) (k r : ℕ) : u ^ (9 * k + r) = u ^ r := by
  rw [pow_add, pow_mul, hu, one_pow, one_mul]

theorem pow_three_det_witness {d₀ d₁ d₂ : K} (h0 : d₀ ^ 9 = 1) (h1 : d₁ ^ 9 = 1)
    (h2 : d₂ ^ 9 = 1) {N : ℕ} (hN : N = 4 ∨ N = 16)
    (hR : d₁ * d₀ ^ N * d₂ ^ (N ^ 2) = d₂ * d₁ ^ N * d₀ ^ (N ^ 2)) :
    (d₁ * d₀ ^ N / (d₂ * d₂ ^ N)) ^ 3 = 1 := by
  have hd0 : d₀ ≠ 0 := by rintro rfl; simp at h0
  have hd1 : d₁ ≠ 0 := by rintro rfl; simp at h1
  have hd2 : d₂ ≠ 0 := by rintro rfl; simp at h2
  rcases hN with rfl | rfl
  ·
    have key : d₂ ^ 15 = d₁ ^ 3 * d₀ ^ 12 := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd1 (pow_ne_zero 4 hd0)) hd2)
      linear_combination hR
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 3 (mul_ne_zero hd2 (pow_ne_zero 4 hd2)))]
    linear_combination -key
  ·
    have hR' : d₁ * d₀ ^ 7 * d₂ ^ 4 = d₂ * d₁ ^ 7 * d₀ ^ 4 := by
      have e1 : d₀ ^ 16 = d₀ ^ 7 := by rw [show 16 = 9 * 1 + 7 from rfl, pow_nine_mul_add h0]
      have e2 : d₂ ^ (16 ^ 2) = d₂ ^ 4 := by
        rw [show 16 ^ 2 = 9 * 28 + 4 from rfl, pow_nine_mul_add h2]
      have e3 : d₁ ^ 16 = d₁ ^ 7 := by rw [show 16 = 9 * 1 + 7 from rfl, pow_nine_mul_add h1]
      have e4 : d₀ ^ (16 ^ 2) = d₀ ^ 4 := by
        rw [show 16 ^ 2 = 9 * 28 + 4 from rfl, pow_nine_mul_add h0]
      rw [e1, e2, e3, e4] at hR
      exact hR
    have key : d₀ ^ 3 * d₂ ^ 3 = d₁ ^ 6 := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hd1 (pow_ne_zero 4 hd0)) hd2)
      linear_combination hR'
    have key2 : d₂ ^ 6 = d₁ ^ 3 * d₀ ^ 3 := by
      have h12 : d₁ ^ 12 = d₁ ^ 3 := by rw [show 12 = 9 * 1 + 3 from rfl, pow_nine_mul_add h1]
      have h6 : d₀ ^ 6 * d₀ ^ 3 = 1 := by rw [← pow_add]; exact h0
      calc d₂ ^ 6 = d₂ ^ 6 * (d₀ ^ 6 * d₀ ^ 3) := by rw [h6, mul_one]
        _ = (d₀ ^ 3 * d₂ ^ 3) ^ 2 * d₀ ^ 3 := by ring
        _ = d₁ ^ 3 * d₀ ^ 3 := by rw [key, ← pow_mul, show 6 * 2 = 12 from rfl, h12]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero 3 (mul_ne_zero hd2 (pow_ne_zero 16 hd2)))]
    have e5 : d₀ ^ (16 * 3) = d₀ ^ 3 := by
      rw [show 16 * 3 = 9 * 5 + 3 from rfl, pow_nine_mul_add h0]
    have e6 : d₂ ^ (17 * 3) = d₂ ^ 6 := by
      rw [show 17 * 3 = 9 * 5 + 6 from rfl, pow_nine_mul_add h2]
    calc (d₁ * d₀ ^ 16) ^ 3 = d₁ ^ 3 * d₀ ^ (16 * 3) := by ring
      _ = d₂ ^ (17 * 3) := by rw [e5, e6, key2]
      _ = (d₂ * d₂ ^ 16) ^ 3 := by ring

theorem pow_sixtyfour (hK : PiField false 2 3 K) (c : K) : c ^ 64 = c := by
  have := hK.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card]; exact hK.card
  rw [← hcard]
  exact FiniteField.pow_card c

theorem fieldAut_cube (hK : PiField false 2 3 K) {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16)
    (hσ : ∀ c, σ c = c ^ N) (c : K) : σ (σ (σ c)) = c := by
  rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
  rcases hN with rfl | rfl
  · exact pow_sixtyfour hK c
  · rw [show 16 * 16 * 16 = 64 * 64 from rfl, pow_mul, pow_sixtyfour hK, pow_sixtyfour hK]

theorem frobGL_cube (hK : PiField false 2 3 K) {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16)
    (hσ : ∀ c, σ c = c ^ N) (A : GL (Fin 3) K) : frobGL σ (frobGL σ (frobGL σ A)) = A := by
  apply Units.ext
  rw [coe_frobGL, coe_frobGL, coe_frobGL]
  ext i j
  simp only [Matrix.map_apply, fieldAut_cube hK hN hσ]

theorem mk_frob_diag_eq {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16) (hσ : ∀ c, σ c = c ^ N)
    {ρ : Kˣ} (hρ9 : ρ ^ 9 = 1) :
    pmk (frobGL σ (diagUnits ρ ρ (ρ * ρ)⁻¹)) = pmk (diagUnits ρ ρ (ρ * ρ)⁻¹ : GL (Fin 3) K) := by
  have hσρ : Units.map (σ : K →* K) ρ = ρ ^ N := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ _)
  rw [frobGL_diagUnits, map_inv, map_mul, hσρ, RonanK432.L3Hard.mk_diagUnits_eq_iff]
  refine ⟨ρ * (ρ ^ N)⁻¹, by group, by group, ?_⟩
  rcases hN with rfl | rfl
  · calc (ρ ^ 4 * ρ ^ 4)⁻¹ * (ρ * (ρ ^ 4)⁻¹) = (ρ * ρ)⁻¹ * (ρ ^ 9)⁻¹ := by group
      _ = (ρ * ρ)⁻¹ := by rw [hρ9, inv_one, mul_one]
  · calc (ρ ^ 16 * ρ ^ 16)⁻¹ * (ρ * (ρ ^ 16)⁻¹) = (ρ * ρ)⁻¹ * ((ρ ^ 9) ^ 5)⁻¹ := by group
      _ = (ρ * ρ)⁻¹ := by rw [hρ9, one_pow, inv_one, mul_one]

variable {ι : Type*} {α : ι → MulAut (projImage (slPi false 3 (2 ^ 3) K))}
  {e₀ : projImage (slPi false 3 (2 ^ 3) K)}

theorem exists_order_nine (hK : PiField false 2 3 K) :
    ∃ ρ : Kˣ, ρ ∈ rootsOfUnity 9 K ∧ orderOf ρ = 9 :=
  exists_orderOf_eq hK (by norm_num) (dvd_refl 9)

theorem CentConfig.false_of_field_diag (hK : PiField false 2 3 K)
    (hc : CentConfig false 2 3 K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    {γ : MulAut (projImage (slPi false 3 (2 ^ 3) K))}
    (hgen : ∀ x, α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ)
    {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16) (hσ : ∀ c, σ c = c ^ N) {a b c : Kˣ}
    (hγ : ∀ s (hs : s ∈ slPi false 3 (2 ^ 3) K),
      (γ (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        pmk (diagUnits a b c * frobGL σ s * (diagUnits a b c)⁻¹)) : False := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨ρ, hρ, hρo⟩ := exists_order_nine hK
  have hρ9 : ρ ^ 9 = 1 := (mem_rootsOfUnity _ _).mp hρ
  set t : GL (Fin 3) K := diagUnits ρ ρ (ρ * ρ)⁻¹ with htdef
  have ht : t ∈ slPi false 3 (2 ^ 3) K := torusHom_mem_slPi (a := ρ) (b := ρ) hK hρ hρ
  set w : projImage (slPi false 3 (2 ^ 3) K) := projOf _ ⟨t, ht⟩ with hwdef
  have hw : (w : ProjGenLinGroup (Fin 3) K) = pmk t := coe_projOf _ _
  have he₀d : (e₀ : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1) := by
    rw [he₀, diagTau_eq_diagUnits hτ hτ0]
  have hw1 : MulAut.conj e₀ w = w := Subtype.ext (by
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀d, hw,
      ← map_inv, ← map_mul, ← map_mul, Sec12.KS128Move.diagUnits_comm, mul_inv_cancel_right])
  have hw2 : γ w = w := Subtype.ext (by
    rw [hwdef, hγ, coe_projOf, frobGL_diagUnits, Sec12.KS128Move.diagUnits_comm,
      mul_inv_cancel_right, ← frobGL_diagUnits]
    exact mk_frob_diag_eq hN hσ hρ9)
  have hfix : ∀ x, α x w = w := fun x => fixed_of_mem_sup hw1 hw2 (hgen x)
  have hw3 : w ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hw, ← map_pow, htdef, Sec12.KS128Move.diagUnits_pow]
    apply ProjGenLinGroup.mk_eq_one.mpr
    rw [GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨ρ ^ 3, ?_⟩
    rw [Sec12.KS128Move.scalar_eq_diagUnits]
    congr 1
    calc ρ ^ 3 = (ρ * ρ)⁻¹ ^ 3 * ρ ^ 9 := by group
      _ = (ρ * ρ)⁻¹ ^ 3 := by rw [hρ9, mul_one])
  have hmem := hc.hF3 w hw3 hfix
  have he₀3 : e₀ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, he₀, ← map_pow, diagTau_pow_three hτ, map_one]; rfl)
  have hρ3 : ρ ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hρo]; norm_num)
  rcases RonanK432.mem_zpowers_cases_of_pow_three he₀3 hmem with h | h | h
  · have h' := congrArg Subtype.val h
    rw [hw, Subgroup.coe_one, ← map_one pmk, ← Sec12.KS128Move.diagUnits_one] at h'
    obtain ⟨u, h1, -, h3⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    apply hρ3
    have hu : u = ρ⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [hu] at h3
    calc ρ ^ 3 = ((ρ * ρ)⁻¹ * ρ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h3, inv_one]
  · have h' := congrArg Subtype.val h
    rw [hw, he₀d] at h'
    obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    apply hτ1
    have h12 : Units.mk0 τ hτ0 = Units.mk0 τ hτ0 ^ 2 := h1.symm.trans h2
    have := congrArg Units.val h12
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    have h0 : τ * (τ - 1) = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hτ0)
  · have h' := congrArg Subtype.val h
    rw [hw, Subgroup.coe_inv, he₀d, ← map_inv, Sec12.KS128Move.diagUnits_inv] at h'
    obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    apply hτ1
    have h12 : (Units.mk0 τ hτ0)⁻¹ = (Units.mk0 τ hτ0 ^ 2)⁻¹ := h1.symm.trans h2
    rw [_root_.inv_inj] at h12
    have := congrArg Units.val h12
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val] at this
    have h0 : τ * (τ - 1) = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hτ0)

theorem pow_nine_of_diagUnits_mem (hK : PiField false 2 3 K) {d₀ d₁ d₂ : Kˣ}
    (h : diagUnits d₀ d₁ d₂ ∈ glPi false 3 (2 ^ 3) K) :
    d₀ ^ 9 = 1 ∧ d₁ ^ 9 = 1 ∧ d₂ ^ 9 = 1 := by
  have hU := hK.unitary
  have h' := (mem_glPi_false hU).mp h
  rw [coe_diagUnits, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal] at h'
  have key : ∀ i : Fin 3, hU.bar ((![(d₀ : K), d₁, d₂]) i) * (![(d₀ : K), d₁, d₂]) i = 1 := by
    intro i
    have := congrFun (congrFun h' i) i
    simpa [Matrix.diagonal_apply_eq] using this
  have hp : ∀ u : Kˣ, hU.bar (u : K) * u = 1 → u ^ 9 = 1 := by
    intro u hu
    apply Units.ext
    rw [hU.bar_apply, ← pow_succ] at hu
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hu
  exact ⟨hp _ (key 0), hp _ (key 1), hp _ (key 2)⟩

theorem entry_two_eq_one {A B C : K} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (N : ℕ)
    (hR : B * A ^ N * C ^ (N ^ 2) = C * B ^ N * A ^ (N ^ 2)) :
    C * (B * A⁻¹ * (A * C⁻¹) ^ N) ^ N * B⁻¹ = 1 := by
  have hA' : A ^ N * A⁻¹ ^ N = 1 := by rw [← mul_pow, mul_inv_cancel₀ hA, one_pow]
  have hC' : C ^ (N ^ 2) * C⁻¹ ^ (N ^ 2) = 1 := by rw [← mul_pow, mul_inv_cancel₀ hC, one_pow]
  have hB' : B * B⁻¹ = 1 := mul_inv_cancel₀ hB
  calc C * (B * A⁻¹ * (A * C⁻¹) ^ N) ^ N * B⁻¹ =
      (C * B ^ N * A ^ (N ^ 2)) * (A⁻¹ ^ N * C⁻¹ ^ (N ^ 2) * B⁻¹) := by ring
    _ = (B * A ^ N * C ^ (N ^ 2)) * (A⁻¹ ^ N * C⁻¹ ^ (N ^ 2) * B⁻¹) := by rw [hR]
    _ = (A ^ N * A⁻¹ ^ N) * (C ^ (N ^ 2) * C⁻¹ ^ (N ^ 2)) * (B * B⁻¹) := by ring
    _ = 1 := by rw [hA', hC', hB', one_mul, one_mul]

theorem det_witness_eq {A B C : K} (hA : A ≠ 0) (N : ℕ) :
    (A * C⁻¹) * (B * A⁻¹ * (A * C⁻¹) ^ N) = B * A ^ N / (C * C ^ N) := by
  calc (A * C⁻¹) * (B * A⁻¹ * (A * C⁻¹) ^ N) = B * A ^ N * (C⁻¹ * C⁻¹ ^ N) * (A * A⁻¹) := by
        ring
    _ = B * A ^ N / (C * C ^ N) := by rw [mul_inv_cancel₀ hA, mul_one, div_eq_mul_inv, mul_inv,
        inv_pow]

theorem CentConfig.false_of_field_mono (hK : PiField false 2 3 K)
    (hc : CentConfig false 2 3 K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    {γ : MulAut (projImage (slPi false 3 (2 ^ 3) K))} (hγ3 : γ ^ 3 = 1)
    (hgen : ∀ x, α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ)
    {σ : K ≃+* K} {N : ℕ} (hN : N = 4 ∨ N = 16) (hσ : ∀ c, σ c = c ^ N) {d₀ d₁ d₂ : Kˣ}
    (hgH : diagUnits d₀ d₁ d₂ * cycThree ∈ glPi false 3 (2 ^ 3) K)
    (hγ : ∀ s (hs : s ∈ slPi false 3 (2 ^ 3) K),
      (γ (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
        pmk ((diagUnits d₀ d₁ d₂ * cycThree) * frobGL σ s *
          (diagUnits d₀ d₁ d₂ * cycThree)⁻¹)) : False := by
  have hU := hK.unitary
  have hπ : false = false → UnitaryFieldData 2 3 K := fun _ => hU
  have hq : ModThree false (2 ^ 3) := rfl
  have hq2 : 2 < 2 ^ 3 := by norm_num
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 3) K, g = diagUnits d₀ d₁ d₂ * cycThree := ⟨_, rfl⟩
  rw [← hg] at hgH hγ
  have hσu : ∀ u : Kˣ, Units.map (σ : K →* K) u = u ^ N := fun u => Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσ u)
  have hcH : (cycThree : GL (Fin 3) K) ∈ glPi false 3 (2 ^ 3) K :=
    slPi_le_glPi hπ (cycThree_mem_slPi hπ)
  have hDH : diagUnits d₀ d₁ d₂ ∈ glPi false 3 (2 ^ 3) K := by
    have := mul_mem hgH (inv_mem hcH)
    rwa [hg, mul_inv_cancel_right] at this
  obtain ⟨h0, h1, h2⟩ := pow_nine_of_diagUnits_mem hK hDH
  have hcube : ∀ A : GL (Fin 3) K, frobGL σ (frobGL σ (frobGL σ A)) = A := frobGL_cube hK hN hσ
  have hNsc : g * frobGL σ g * frobGL σ (frobGL σ g) ∈ StatedScalars (Fin 3) K := by
    have := Sec13.isPerfect_projImage_slPi hK hq2
    refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
    rw [← mk_eq_one_iff_mem_statedScalars]
    have hs1 : g * frobGL σ s * g⁻¹ ∈ slPi false 3 (2 ^ 3) K :=
      conj_mem_slPi hπ hgH (frobGL_mem_slPi hK σ hs)
    have hs2 : g * frobGL σ (g * frobGL σ s * g⁻¹) * g⁻¹ ∈ slPi false 3 (2 ^ 3) K :=
      conj_mem_slPi hπ hgH (frobGL_mem_slPi hK σ hs1)
    have hγ1 : γ (projOf _ ⟨s, hs⟩) = projOf _ ⟨_, hs1⟩ := Subtype.ext (by rw [hγ, coe_projOf])
    have hγ2 : γ (projOf _ ⟨_, hs1⟩) = projOf _ ⟨_, hs2⟩ := Subtype.ext (by rw [hγ, coe_projOf])
    have h3 := congrArg (fun β : MulAut (projImage (slPi false 3 (2 ^ 3) K)) =>
      ((β (projOf _ ⟨s, hs⟩) : projImage (slPi false 3 (2 ^ 3) K)) :
        ProjGenLinGroup (Fin 3) K)) hγ3
    simp only [MulAut.one_apply, coe_projOf] at h3
    rw [_root_.pow_three γ, MulAut.mul_apply, MulAut.mul_apply, hγ1, hγ2, hγ] at h3
    have hexp : g * frobGL σ (g * frobGL σ (g * frobGL σ s * g⁻¹) * g⁻¹) * g⁻¹ =
        (g * frobGL σ g * frobGL σ (frobGL σ g)) * s *
          (g * frobGL σ g * frobGL σ (frobGL σ g))⁻¹ := by
      simp only [map_mul, map_inv, hcube]
      group
    rw [hexp] at h3
    calc pmk ((g * frobGL σ g * frobGL σ (frobGL σ g)) * s *
          (g * frobGL σ g * frobGL σ (frobGL σ g))⁻¹ * s⁻¹) =
        pmk ((g * frobGL σ g * frobGL σ (frobGL σ g)) * s *
          (g * frobGL σ g * frobGL σ (frobGL σ g))⁻¹) * pmk s⁻¹ := map_mul _ _ _
      _ = pmk s * (pmk s)⁻¹ := by rw [h3, map_inv]
      _ = 1 := mul_inv_cancel _
  have hpow2 : ∀ u : Kˣ, Units.map (σ : K →* K) (Units.map (σ : K →* K) u) = u ^ (N ^ 2) := by
    intro u
    rw [hσu, hσu, ← pow_mul, sq]
  have hNm : g * frobGL σ g * frobGL σ (frobGL σ g) =
      diagUnits (d₀ * d₂ ^ N * d₁ ^ (N ^ 2)) (d₁ * d₀ ^ N * d₂ ^ (N ^ 2))
        (d₂ * d₁ ^ N * d₀ ^ (N ^ 2)) := by
    have hsq : ∀ u : Kˣ, (u ^ N) ^ N = u ^ (N ^ 2) := fun u => by rw [← pow_mul, sq]
    rw [hg]
    simp only [map_mul, frobGL_cycThree, frobGL_diagUnits, hσu, hsq]
    calc diagUnits d₀ d₁ d₂ * cycThree * (diagUnits (d₀ ^ N) (d₁ ^ N) (d₂ ^ N) * cycThree) *
          (diagUnits (d₀ ^ (N ^ 2)) (d₁ ^ (N ^ 2)) (d₂ ^ (N ^ 2)) * cycThree) =
        diagUnits d₀ d₁ d₂ * (cycThree * diagUnits (d₀ ^ N) (d₁ ^ N) (d₂ ^ N) * cycThree⁻¹) *
          (cycThree * (cycThree * diagUnits (d₀ ^ (N ^ 2)) (d₁ ^ (N ^ 2)) (d₂ ^ (N ^ 2)) *
            cycThree⁻¹) * cycThree⁻¹) * cycThree ^ 3 := by group
      _ = _ := by
        rw [cycThree_conj_diagUnits, cycThree_conj_diagUnits, cycThree_conj_diagUnits,
          RonanK432.L3Hard.cycThree_cube, mul_one, diagUnits_mul, diagUnits_mul]
  rw [hNm] at hNsc
  obtain ⟨μ, hμ⟩ := hNsc
  rw [Sec12.KS128Move.scalar_eq_diagUnits, Sec12.KS128Move.diagUnits_eq_iff] at hμ
  have hR : d₁ * d₀ ^ N * d₂ ^ (N ^ 2) = d₂ * d₁ ^ N * d₀ ^ (N ^ 2) := hμ.2.1.symm.trans hμ.2.2
  have hR' : (d₁ : K) * (d₀ : K) ^ N * (d₂ : K) ^ (N ^ 2) =
      (d₂ : K) * (d₁ : K) ^ N * (d₀ : K) ^ (N ^ 2) := by
    have := congrArg Units.val hR
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using this
  have hK9 : ∀ u : Kˣ, u ^ 9 = 1 → (u : K) ^ 9 = 1 := fun u hu => by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  obtain ⟨x, hx⟩ : ∃ x : Kˣ, x = d₀ * d₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Kˣ, y = d₁ * d₀⁻¹ * x ^ N := ⟨_, rfl⟩
  have hx9 : x ^ 9 = 1 := by rw [hx, mul_pow, inv_pow, h0, h2, inv_one, mul_one]
  have hy9 : y ^ 9 = 1 := by
    have : (x ^ N) ^ 9 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx9, one_pow]
    rw [hy, mul_pow, mul_pow, this, h1, inv_pow, h0, inv_one, mul_one, mul_one]
  have hkey : g * frobGL σ (diagUnits x y 1 * cycThree) * g⁻¹ = diagUnits x y 1 * cycThree := by
    rw [map_mul, frobGL_cycThree, frobGL_diagUnits, hσu, hσu, map_one, hg]
    calc diagUnits d₀ d₁ d₂ * cycThree * (diagUnits (x ^ N) (y ^ N) 1 * cycThree) *
          (diagUnits d₀ d₁ d₂ * cycThree)⁻¹ =
        diagUnits d₀ d₁ d₂ * (cycThree * diagUnits (x ^ N) (y ^ N) 1 * cycThree⁻¹) *
          (cycThree * (diagUnits d₀ d₁ d₂)⁻¹ * cycThree⁻¹) * cycThree := by group
      _ = diagUnits (d₀ * 1 * d₂⁻¹) (d₁ * x ^ N * d₀⁻¹) (d₂ * y ^ N * d₁⁻¹) * cycThree := by
        rw [cycThree_conj_diagUnits, Sec12.KS128Move.diagUnits_inv, cycThree_conj_diagUnits,
          diagUnits_mul, diagUnits_mul]
      _ = diagUnits x y 1 * cycThree := by
        congr 1
        rw [Sec12.KS128Move.diagUnits_eq_iff]
        refine ⟨by rw [hx, mul_one], by rw [hy, mul_right_comm], ?_⟩
        apply Units.ext
        rw [hy, hx]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
          Units.val_one]
        exact entry_two_eq_one d₀.ne_zero d₁.ne_zero d₂.ne_zero N hR'
  have hX3 : (x * y) ^ 3 = 1 := by
    apply Units.ext
    have hxy : ((x * y : Kˣ) : K) = (d₁ : K) * (d₀ : K) ^ N / ((d₂ : K) * (d₂ : K) ^ N) := by
      rw [hy, hx]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      exact det_witness_eq d₀.ne_zero N
    rw [Units.val_pow_eq_pow_val, hxy, Units.val_one]
    exact pow_three_det_witness (hK9 _ h0) (hK9 _ h1) (hK9 _ h2) hN hR'
  have := hK.finite
  have hcard9 : Nat.card (rootsOfUnity 9 K) = 9 :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (by
      rw [hK.card]
      change 9 ∣ (2 ^ 3) ^ 2 - 1
      norm_num)
  have hxy9 : (x * y)⁻¹ ∈ rootsOfUnity 9 K := by
    rw [mem_rootsOfUnity, inv_pow, show 9 = 3 * 3 from rfl, pow_mul, hX3, one_pow, inv_one]
  obtain ⟨lam, hlam⟩ := exists_pow_eq_of_pow_div (G := rootsOfUnity 9 K) (M := 3)
    (by rw [hcard9]; norm_num) (t := ⟨(x * y)⁻¹, hxy9⟩) (by
      apply Subtype.ext
      rw [hcard9, show 9 / 3 = 3 from rfl, Subgroup.coe_pow]
      change ((x * y)⁻¹) ^ 3 = 1
      rw [inv_pow, hX3, inv_one])
  have hlam3 : (lam : Kˣ) ^ 3 = (x * y)⁻¹ := by
    have := congrArg Subtype.val hlam
    rwa [Subgroup.coe_pow] at this
  set s₀ : GL (Fin 3) K :=
    GeneralLinearGroup.scalar (Fin 3) (lam : Kˣ) * (diagUnits x y 1 * cycThree) with hs₀def
  have hs₀ : s₀ ∈ slPi false 3 (2 ^ 3) K := by
    rw [mem_slPi_iff hπ]
    refine ⟨mul_mem ((scalar_mem_glPi_iff hK _).mpr lam.2) (mul_mem (diagUnits_mem_glPi hK
      ((mem_rootsOfUnity _ _).mpr hx9) ((mem_rootsOfUnity _ _).mpr hy9) (one_mem _)) hcH), ?_⟩
    have hdc : ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [coe_cycThree, det_fin_three]
      simp [Matrix.vecHead, Matrix.vecTail]
    have hdt : ((diagUnits x y 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
        (x : K) * (y : K) := by
      rw [coe_diagUnits, det_diagonal, Fin.prod_univ_three]
      simp
    rw [hs₀def, Units.val_mul, Units.val_mul, det_mul, det_mul, det_scalar, hdt, hdc, mul_one,
      ← Units.val_pow_eq_pow_val, hlam3, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  set w : projImage (slPi false 3 (2 ^ 3) K) := projOf _ ⟨s₀, hs₀⟩ with hwdef
  have hw : (w : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits x y 1 * cycThree) := by
    rw [hwdef, coe_projOf]
    change pmk s₀ = _
    rw [hs₀def, map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K), A * GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hw1 : MulAut.conj e₀ w = w := Subtype.ext (by
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hw,
      ← map_inv, ← map_mul, ← map_mul]
    have hdt : diagTau hτ * diagUnits x y 1 = diagUnits x y 1 * diagTau hτ := by
      rw [diagTau_eq_diagUnits hτ hτ0]
      exact Sec12.KS128Move.diagUnits_comm _ _ _ _ _ _
    have : diagTau hτ * (diagUnits x y 1 * cycThree) * (diagTau hτ)⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (diagUnits x y 1 * cycThree) := by
      calc diagTau hτ * (diagUnits x y 1 * cycThree) * (diagTau hτ)⁻¹ =
          (diagTau hτ * diagUnits x y 1) * cycThree * (diagTau hτ)⁻¹ := by group
        _ = diagUnits x y 1 * (diagTau hτ * cycThree * (diagTau hτ)⁻¹) := by rw [hdt]; group
        _ = _ := by rw [diagTau_conj_cycThree hτ hτ0, ← mul_assoc, hsc, mul_assoc]
    rw [this, map_mul, ProjGenLinGroup.mk_scalar, one_mul])
  have hw2 : γ w = w := by
    have hγs : (γ w : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s₀ * g⁻¹) := hγ s₀ hs₀
    set S' := GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) (lam : Kˣ)) with hS'
    set F := frobGL σ (diagUnits x y 1 * cycThree) with hF
    have e1 : frobGL σ s₀ = S' * F := by rw [hs₀def, map_mul, frobGL_scalar]
    have hcomp : g * frobGL σ s₀ * g⁻¹ = S' * (diagUnits x y 1 * cycThree) := by
      rw [e1, ← hkey]
      calc g * (S' * F) * g⁻¹ = (g * S') * F * g⁻¹ := by group
        _ = (S' * g) * F * g⁻¹ := by rw [hS', hsc]
        _ = S' * (g * F * g⁻¹) := by group
    apply Subtype.ext
    rw [hγs, hcomp, map_mul, hS', ProjGenLinGroup.mk_scalar, one_mul, hw]
  have hfix : ∀ x', α x' w = w := fun x' => fixed_of_mem_sup hw1 hw2 (hgen x')
  have hw3 : w ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hw, ← map_pow, Subgroup.coe_one]
    apply ProjGenLinGroup.mk_eq_one.mpr
    rw [GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨x * y, ?_⟩
    rw [Sec12.KS128Move.scalar_eq_diagUnits]
    calc diagUnits (x * y) (x * y) (x * y) =
        diagUnits x y 1 * diagUnits 1 x y * diagUnits y 1 x * cycThree ^ 3 := by
          rw [RonanK432.L3Hard.cycThree_cube, mul_one, diagUnits_mul, diagUnits_mul]
          exact Sec12.KS128Move.diagUnits_eq_iff.mpr ⟨by rw [mul_one], by rw [mul_one, mul_comm],
            by rw [one_mul, mul_comm]⟩
      _ = diagUnits x y 1 * (cycThree * diagUnits x y 1 * cycThree⁻¹) *
          (cycThree * (cycThree * diagUnits x y 1 * cycThree⁻¹) * cycThree⁻¹) * cycThree ^ 3 := by
          rw [cycThree_conj_diagUnits, cycThree_conj_diagUnits]
      _ = (diagUnits x y 1 * cycThree) ^ 3 := by
          simp only [pow_succ, pow_zero, one_mul]
          group)
  have hmem := hc.hF3 w hw3 hfix
  have he₀3 : e₀ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, he₀, ← map_pow, diagTau_pow_three hτ, map_one]; rfl)
  have he₀d : (e₀ : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1) := by
    rw [he₀, diagTau_eq_diagUnits hτ hτ0]
  rcases RonanK432.mem_zpowers_cases_of_pow_three he₀3 hmem with h | h | h
  · have h' := congrArg Subtype.val h
    rw [hw, Subgroup.coe_one, ← map_one pmk, ← Sec12.KS128Move.diagUnits_one] at h'
    exact mk_monomial_ne_mk_diagUnits x y 1 _ _ _ h'
  · have h' := congrArg Subtype.val h
    rw [hw, he₀d] at h'
    exact mk_monomial_ne_mk_diagUnits x y 1 _ _ _ h'
  · have h' := congrArg Subtype.val h
    rw [hw, Subgroup.coe_inv, he₀d, ← map_inv, Sec12.KS128Move.diagUnits_inv] at h'
    exact mk_monomial_ne_mk_diagUnits x y 1 _ _ _ h'

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
