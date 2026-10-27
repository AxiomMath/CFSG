module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockData
public import CFSG.HardMathSupport.Timmesfeld.Torality.A2Block

public section

namespace CFSG.StandardType.SmallExc

open scoped MatrixGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE TableBExc.E6Three NoOffTwE6Three

theorem coxSL3_pow_three {L : Type} [Field L] : (coxSL3 : SL(3, L)) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_coxSL3, Matrix.SpecialLinearGroup.coe_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pow_three, monoM₁, Matrix.mul_apply, Fin.sum_univ_three]

theorem frame_col_zero {τ : Tag}
    {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsA2Frame ρ σ) : σ 0 0 = 0 ∧ σ 1 0 = -σ 0 1 ∧ σ 2 0 = -(σ 0 1 + σ 1 2) := by
  refine ⟨by simpa using hfr.add 0 0 0, hfr.neg 0 1, ?_⟩
  rw [hfr.add 0 1 2]
  exact hfr.neg 0 2

section Block

variable {τ : Tag} {K : Type} [Field K]

theorem exists_conj_rootDiagUnit_of_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0)
    {ρ : SL(3, K) →* ModGL τ K} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ)
    (b : Fin τ.rank → Kˣ) {z : Kˣ}
    (hz : z ^ 3 * (rootChar b (σ 0 0) * rootChar b (σ 1 0) * rootChar b (σ 2 0)) = 1) :
    ∃ (g : SL(3, K)) (c : Fin τ.rank → Kˣ),
      ρ g * (ρ coxSL3 * rootDiagUnit τ b) * (ρ g)⁻¹ = rootDiagUnit τ c := by
  set dd : Fin 3 → Kˣ := fun j => rootChar b (σ j 0) with hdd
  have hddA : ∀ A, rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiag3 dd A) :=
    fun A => hfr.torus b A
  set d' : Fin 3 → Kˣ := fun j => z * dd j with hd'
  have hd'det : (d' 0 : K) * d' 1 * d' 2 = 1 := by
    have h1 := congrArg Units.val hz
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one] at h1
    simp only [hd', hdd, Units.val_mul]
    linear_combination h1
  set D' : SL(3, K) := diagSL3 d' hd'det with hD'
  obtain ⟨c₁, hc₁⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (hfr.diag D' fun i j hij => by simp [hD', coe_diagSL3, hij])
  set t₂ : ModGL τ K := (ρ D')⁻¹ * rootDiagUnit τ b with ht₂
  have ht₂c : ∀ A : SL(3, K), t₂ * ρ A = ρ A * t₂ := by
    intro A
    have h1 : rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ D' * ρ A * (ρ D')⁻¹ := by
      rw [hddA A, ← map_mul, ← map_inv, ← map_mul, diagSL3_conj dd z hd'det A]
    calc t₂ * ρ A = (ρ D')⁻¹ * (rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹) *
          rootDiagUnit τ b := by rw [ht₂]; group
      _ = (ρ D')⁻¹ * (ρ D' * ρ A * (ρ D')⁻¹) * rootDiagUnit τ b := by rw [h1]
      _ = ρ A * t₂ := by rw [ht₂]; group
  have hmD' : ((coxSL3 * D' : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      monoM₁ ((-1 : K) * (d' 0 : K)) ((-1 : K) * (d' 1 : K)) ((1 : K) * (d' 2 : K)) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_coxSL3, hD', coe_diagSL3, monoM₁]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  obtain ⟨g', hg'⟩ :=
    exists_sl3_conj_M₁ hω h3 (by linear_combination hd'det) (coxSL3 * D') hmD'
  obtain ⟨c₂, hc₂⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (hfr.diag (g'⁻¹ * (coxSL3 * D') * g') fun i j hij => by rw [hg']; simp [hij])
  refine ⟨g'⁻¹, c₂ * (c₁⁻¹ * b), ?_⟩
  have hx : ρ coxSL3 * rootDiagUnit τ b = ρ (coxSL3 * D') * t₂ := by
    rw [map_mul, ht₂]
    group
  have hc1 : ρ g'⁻¹ * t₂ * (ρ g'⁻¹)⁻¹ = t₂ := by
    rw [← ht₂c g'⁻¹, mul_inv_cancel_right]
  have hc2 : ρ g'⁻¹ * ρ (coxSL3 * D') * (ρ g'⁻¹)⁻¹ = ρ (g'⁻¹ * (coxSL3 * D') * g') := by
    simp only [map_mul, map_inv, inv_inv]
  rw [hx]
  calc ρ g'⁻¹ * (ρ (coxSL3 * D') * t₂) * (ρ g'⁻¹)⁻¹
      = (ρ g'⁻¹ * ρ (coxSL3 * D') * (ρ g'⁻¹)⁻¹) * (ρ g'⁻¹ * t₂ * (ρ g'⁻¹)⁻¹) := by group
    _ = rootDiagUnit τ c₂ * ((rootDiagUnit τ c₁)⁻¹ * rootDiagUnit τ b) := by
      rw [hc1, hc2, hc₂, ht₂, hc₁]
    _ = rootDiagUnit τ (c₂ * (c₁⁻¹ * b)) := by
      rw [rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_inv]

end Block

theorem orbit_sum_gE6 (i : Fin 3) : ∃ μ : Fin Tag.E6.rank → ℤ,
    (gE6 i)⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
        (gE6 i)⁻¹ • ((gE6 i)⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) +
        Pi.single 3 1 + (2 • (a2PairE6 i).1 + (a2PairE6 i).2) = μ + μ + μ := by
  refine ⟨(![![1, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 0, 0]] :
    Fin 3 → Fin Tag.E6.rank → ℤ) i, ?_⟩
  rw [gE6, ← CoxeterSystem.wordProd_reverse, TableBExc.wordProd_smul, TableBExc.wordProd_smul]
  revert i
  decide +kernel

theorem exists_cube_of_weylTuple
    {K : Type} [Field K] {ρ : SL(3, K) →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) {i : Fin 3}
    (h01 : σ 0 1 = (a2PairE6 i).1) (h12 : σ 1 2 = (a2PairE6 i).2) {b : Fin Tag.E6.rank → Kˣ}
    (hb : weylTuple (gE6 i) b * weylTuple (gE6 i) (weylTuple (gE6 i) b) * b = 1) :
    ∃ z : Kˣ, z ^ 3 * (rootChar b (σ 0 0) * rootChar b (σ 1 0) * rootChar b (σ 2 0)) = 1 := by
  obtain ⟨μ, hμ⟩ := orbit_sum_gE6 i
  obtain ⟨h0, h1, h2⟩ := frame_col_zero hfr
  have hmul : ∀ (a a' : Fin Tag.E6.rank → Kˣ) (u : Fin Tag.E6.rank → ℤ),
      rootChar (a * a') u = rootChar a u * rootChar a' u := fun a a' u => by
    simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  have hone : ∀ u : Fin Tag.E6.rank → ℤ, rootChar (1 : Fin Tag.E6.rank → Kˣ) u = 1 :=
    fun u => by simp [rootChar]
  have horb := congrArg (fun c => rootChar c (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) hb
  simp only [hmul, rootChar_weylTuple, hone] at horb
  have hv : μ + μ + μ + σ 0 0 + σ 1 0 + σ 2 0 =
      (gE6 i)⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) +
        (gE6 i)⁻¹ • ((gE6 i)⁻¹ • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ)) + Pi.single 3 1 := by
    rw [← hμ, h0, h1, h2, h01, h12]
    abel
  refine ⟨rootChar b μ, ?_⟩
  have e : rootChar b μ ^ 3 * (rootChar b (σ 0 0) * rootChar b (σ 1 0) * rootChar b (σ 2 0)) =
      rootChar b (μ + μ + μ + σ 0 0 + σ 1 0 + σ 2 0) := by
    simp only [rootChar_add, pow_three, mul_assoc]
  rw [e, hv, rootChar_add, rootChar_add]
  exact horb

end CFSG.StandardType.SmallExc

end
