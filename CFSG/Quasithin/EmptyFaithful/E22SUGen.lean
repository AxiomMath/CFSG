module

public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.Quasithin.E22S

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars)

variable {K : Type} [Field K]

theorem su3_exists_prime_pow [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ p f : ℕ, Fact p.Prime ∧ CharP K p ∧ q = p ^ f := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite K p
  have : NeZero p := ⟨hp0⟩
  have := CharP.char_is_prime_of_pos K p
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  have h1 : q ∣ p ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp h1
  exact ⟨p, f, inferInstance, hp, hf⟩

@[expose] def suStab (K : Type) [Field K] (q : ℕ) (k : Fin 3) : Subgroup (StatedSU 3 q K) where
  carrier := {x | ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k 1 : Fin 3 → K) =
    Pi.single k 1}
  mul_mem' {x y} hx hy := by
    show ((((x * y : StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [show ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k 1 : Fin 3 → K) =
      Pi.single k 1 from hy]
    exact hx
  one_mem' := by
    show ((((1 : StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  inv_mem' {x} hx := by
    show ((((x⁻¹ : StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ _ = _
    have hx' : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k 1 : Fin 3 → K) =
      Pi.single k 1 := hx
    calc ((((x⁻¹ : StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (Pi.single k 1 : Fin 3 → K)
        = ((((x⁻¹ : StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k 1 : Fin 3 → K)) := by
          rw [hx']
      _ = Pi.single k 1 := by
          rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, Matrix.one_mulVec]

theorem mem_suStab {q : ℕ} {k : Fin 3} {x : StatedSU 3 q K} :
    x ∈ suStab K q k ↔
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single k 1 : Fin 3 → K) =
        Pi.single k 1 :=
  Iff.rfl

section Involution

variable {σ : K ≃+* K}

def su3Plane : (Fin 2 → K) →ₗ[K] (Fin 3 → K) :=
  pairL (Pi.single 0 1) (Pi.single 1 1)

theorem su3Plane_apply (u : Fin 2 → K) : (su3Plane u : Fin 3 → K) = ![u 0, u 1, 0] := by
  funext i
  fin_cases i <;> simp [su3Plane, pairL]

theorem su3Plane_isometry (u v : Fin 2 → K) :
    herm σ (su3Plane u) (su3Plane v) = herm σ u v := by
  simp [su3Plane_apply, herm, Fin.sum_univ_three, Fin.sum_univ_two]

theorem su3_decomp (a : Fin 3 → K) :
    a = su3Plane ![a 0, a 1] + a 2 • (Pi.single 2 1 : Fin 3 → K) := by
  funext i
  fin_cases i <;> simp [su3Plane_apply]

theorem su3_exists_move (hσ : IsUnitaryInvolution σ) (a : Fin 3 → K)
    (ha : σ (a 0) * a 0 + σ (a 1) * a 1 ≠ 0) :
    ∃ m : SUid σ 3, m • (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 ∧ (m • a) 0 = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, a 0 = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, a 1 = y := ⟨_, rfl⟩
  rw [hx, hy] at ha
  obtain ⟨ν, hν⟩ : ∃ ν, ν = σ x * x + σ y * y := ⟨_, rfl⟩
  rw [← hν] at ha
  have hνσ : σ ν = ν := by
    rw [hν, map_add, map_mul, map_mul, hσ.invol, hσ.invol]
    ring
  have hν' : σ ν⁻¹ = ν⁻¹ := by rw [map_inv₀, hνσ]
  obtain ⟨l, hl⟩ := hσ.norm_surj ν⁻¹ hν' (inv_ne_zero ha)
  have hσβ : σ (σ l * σ x) = l * x := by rw [map_mul, hσ.invol, hσ.invol]
  have hN : σ (l * y) * (l * y) + σ (σ l * σ x) * (σ l * σ x) = 1 := by
    rw [hσβ, map_mul]
    have : ν⁻¹ * ν = 1 := inv_mul_cancel₀ ha
    linear_combination (σ y * y + σ x * x) * hl + this - ν⁻¹ * hν
  obtain ⟨A, hA⟩ : ∃ A : SUid σ 2, A = su2 hσ.invol hN := ⟨_, rfl⟩
  have hAT : A ∈ T σ 2 := by
    rw [T_two_eq_top hσ]
    exact Subgroup.mem_top _
  obtain ⟨m, -, hmφ, hmperp⟩ :=
    transport hσ.invol su3Plane (fun u v => su3Plane_isometry u v) hAT
  have hm2 : m • (Pi.single 2 1 : Fin 3 → K) = Pi.single 2 1 := by
    refine hmperp _ fun u => ?_
    rw [herm_single_right, su3Plane_apply]
    simp
  refine ⟨m, hm2, ?_⟩
  have hA0 : (A • (![x, y] : Fin 2 → K)) 0 = 0 := by
    rw [hA, su2, mkSU_smul]
    simp [mulVec, dotProduct, Fin.sum_univ_two, hσβ]
    ring
  conv_lhs => rw [su3_decomp a]
  rw [smul_add, hmφ, smul_comm, hm2, Pi.add_apply, su3Plane_apply, hx, hy]
  simp [hA0]

theorem su3_tvSet_mem (hσ : IsUnitaryInvolution σ) {t : SUid σ 3} (ht : t ∈ tvSet σ 3) :
    t ∈ ⨆ k : Fin 3, MulAction.stabilizer (SUid σ 3) (Pi.single k (1 : K) : Fin 3 → K) := by
  obtain ⟨a, c, ha, hc, h⟩ := ht
  by_cases ha2 : a 2 = 0
  · refine Subgroup.mem_iSup_of_mem 2 ?_
    rw [MulAction.mem_stabilizer_iff, h, herm_single_right, ha2, map_zero, zero_mul, mul_zero,
      zero_smul, add_zero]
  · have hN2 : σ (a 2) * a 2 ≠ 0 := mul_ne_zero ((map_ne_zero σ).mpr ha2) ha2
    have hν : σ (a 0) * a 0 + σ (a 1) * a 1 ≠ 0 := by
      intro h0
      apply hN2
      have := ha
      rw [herm, Fin.sum_univ_three] at this
      linear_combination this - h0
    obtain ⟨m, hm2, hm0⟩ := su3_exists_move hσ a hν
    have hm : m ∈ ⨆ k : Fin 3,
        MulAction.stabilizer (SUid σ 3) (Pi.single k (1 : K) : Fin 3 → K) :=
      Subgroup.mem_iSup_of_mem 2 (MulAction.mem_stabilizer_iff.mpr hm2)
    have h' := conj_smul_of_tv m t h
    have hfix : m * t * m⁻¹ ∈ MulAction.stabilizer (SUid σ 3)
        (Pi.single 0 (1 : K) : Fin 3 → K) := by
      rw [MulAction.mem_stabilizer_iff, h', herm_single_right, hm0, map_zero, zero_mul, mul_zero,
        zero_smul, add_zero]
    have ht : t = m⁻¹ * (m * t * m⁻¹) * m := by group
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm)
      (Subgroup.mem_iSup_of_mem 0 hfix)) hm

theorem su3_iSup_stabilizer_eq_top (hσ : IsUnitaryInvolution σ)
    (h3 : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) :
    (⨆ k : Fin 3, MulAction.stabilizer (SUid σ 3) (Pi.single k (1 : K) : Fin 3 → K)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← T_eq_top hσ (n := 3) (by norm_num) fun _ => h3]
  exact (Subgroup.closure_le _).mpr fun t ht => su3_tvSet_mem hσ ht

end Involution

end CFSG.Quasithin.E22S
