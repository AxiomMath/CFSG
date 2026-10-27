module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] noncomputable def sl3four : Subgroup (SpecialLinearGroup (Fin 6) F2) := (resSL 3).range

@[expose] noncomputable def sl3fourEquiv : SpecialLinearGroup (Fin 3) F4 ≃* sl3four :=
  MonoidHom.ofInjective (resSL_injective 3)

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem f2_cases (a : F2) : a = 0 ∨ a = 1 := by
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  by_cases hz : a = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq a hz).trans (huniq 1 one_ne_zero).symm)

private theorem resBlocks_surjective (n : ℕ) : Function.Surjective (resBlocks n) := by
  change Function.Surjective ((Matrix.reindexRingEquiv F2 (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))).toRingHom ∘
    (Matrix.compRingEquiv (Fin n) (Fin 2) F2).toRingHom)
  exact (Matrix.reindexRingEquiv F2 (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2))).surjective.comp
    (Matrix.compRingEquiv (Fin n) (Fin 2) F2).surjective

private theorem commutant_W (T : Matrix (Fin 2) (Fin 2) F2)
    (h : T * f4Eps f4Omega = f4Eps f4Omega * T) :
    ∃ a : F4, f4Eps a = T := by
  rw [f4Eps_omega] at h
  have h01 : T 0 1 = T 1 0 := by
    have hh := congr_fun (congr_fun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  have h11 : T 1 1 = T 0 0 + T 0 1 := by
    have hh := congr_fun (congr_fun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hh
    exact hh.symm
  have hT : T = !![T 0 0, T 0 1; T 0 1, T 0 0 + T 0 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h11]
  have hW2 : ((!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F2))^2 = !![1,1;1,0] := by
    rw [pow_two, Matrix.mul_fin_two]
    simp [one_add_one_f2]
  rcases f2_cases (T 0 0) with h00 | h00 <;> rcases f2_cases (T 0 1) with h01v | h01v
  · refine ⟨0, ?_⟩
    rw [map_zero, hT, h00, h01v]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp
  · refine ⟨f4Omega, ?_⟩
    rw [f4Eps_omega, hT, h00, h01v]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp
  · refine ⟨1, ?_⟩
    rw [map_one, hT, h00, h01v]
    ext i j <;> fin_cases i <;> fin_cases j <;> simp
  · refine ⟨f4Omega ^ 2, ?_⟩
    rw [map_pow, f4Eps_omega, hW2, hT, h00, h01v, one_add_one_f2]

private theorem exists_resMat_of_mem_centralizer (Y : SpecialLinearGroup (Fin 6) F2)
    (hY : Y ∈ Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))) :
    ∃ A : Matrix (Fin 3) (Fin 3) F4, (Y : Matrix (Fin 6) (Fin 6) F2) = resMat 3 A := by
  have hYmul : Y * zeta5 = zeta5 * Y := (Subgroup.mem_centralizer_singleton_iff).1 hY
  have hYmat : (Y : Matrix (Fin 6) (Fin 6) F2) * (zeta5 : Matrix (Fin 6) (Fin 6) F2) =
      (zeta5 : Matrix (Fin 6) (Fin 6) F2) * (Y : Matrix (Fin 6) (Fin 6) F2) := by
    simpa using congrArg (fun z : SpecialLinearGroup (Fin 6) F2 => (z : Matrix (Fin 6) (Fin 6) F2)) hYmul
  obtain ⟨B, hB⟩ := resBlocks_surjective 3 (Y : Matrix (Fin 6) (Fin 6) F2)
  let Zs : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) F2) :=
    Matrix.diagonal (fun _ : Fin 3 => f4Eps f4Omega)
  have hzeta : (zeta5 : Matrix (Fin 6) (Fin 6) F2) = resBlocks 3 Zs := by
    rw [zeta5_eq, coe_resGL]
    show resBlocks 3 (f4Eps.mapMatrix (omegaScalar : Matrix (Fin 3) (Fin 3) F4)) = resBlocks 3 Zs
    congr 1
    rw [show (omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.diagonal (fun _ : Fin 3 => f4Omega) by
      simp [omegaScalar, Matrix.scalar_apply]]
    ext i j
    by_cases hij : i = j <;> simp [Zs, RingHom.mapMatrix_apply, Matrix.diagonal_apply, hij]
  have hBZs : B * Zs = Zs * B := by
    apply resBlocks_injective 3
    rw [map_mul, map_mul, hB, ← hzeta]
    exact hYmat
  have hentry : ∀ i i' : Fin 3, B i i' * f4Eps f4Omega = f4Eps f4Omega * B i i' := by
    intro i i'
    have hh := congr_fun (congr_fun hBZs i) i'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    simpa [Zs] using hh
  choose A hA using fun i i' => commutant_W (B i i') (hentry i i')
  refine ⟨A, ?_⟩
  have hBA : B = f4Eps.mapMatrix A := by
    ext i i' j j'
    exact congr_fun (congr_fun (hA i i').symm j) j'
  rw [← hB, hBA]
  rfl

theorem centralizer_zeta5 :
    Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)) = (resGL 3).range := by
  apply le_antisymm
  · intro X hX
    obtain ⟨A, hA⟩ := exists_resMat_of_mem_centralizer X hX
    obtain ⟨A', hA'⟩ := exists_resMat_of_mem_centralizer X⁻¹ (Subgroup.inv_mem _ hX)
    have hAA' : A * A' = 1 := by
      apply resMat_injective 3
      rw [map_mul, map_one, ← hA, ← hA']
      exact congrArg Subtype.val (mul_inv_cancel X)
    have hA'A : A' * A = 1 := by
      apply resMat_injective 3
      rw [map_mul, map_one, ← hA', ← hA]
      exact congrArg Subtype.val (inv_mul_cancel X)
    refine ⟨Units.mk A A' hAA' hA'A, ?_⟩
    apply Subtype.ext
    rw [coe_resGL]
    exact hA.symm
  · intro X hX
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [MonoidHom.mem_range] at hX
    obtain ⟨g, rfl⟩ := hX
    rw [zeta5_eq, ← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    change (g : Matrix (Fin 3) (Fin 3) F4) * (Matrix.scalar (Fin 3) f4Omega) =
      (Matrix.scalar (Fin 3) f4Omega) * (g : Matrix (Fin 3) (Fin 3) F4)
    exact (Matrix.scalar_commute f4Omega (fun r' => mul_comm f4Omega r')
      (g : Matrix (Fin 3) (Fin 3) F4)).symm.eq

theorem sl3four_le_centralizer :
    sl3four ≤ Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)) := by
  rw [centralizer_zeta5, sl3four]
  intro x hx
  rw [MonoidHom.mem_range] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨SpecialLinearGroup.toGL a, rfl⟩

theorem card_sl3four : Nat.card sl3four = 60480 := by
  have h1 : Nat.card sl3four = Nat.card (SpecialLinearGroup (Fin 3) F4) :=
    (Nat.card_congr sl3fourEquiv.toEquiv).symm
  letI : Fintype F4 := Fintype.ofFinite F4
  rw [h1, Matrix.card_SL_field (𝔽 := F4) 3]
  have hF4 : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  rw [hF4]
  norm_num [Fin.prod_univ_three]

end CFSG.StandardType.GGHalf

end
