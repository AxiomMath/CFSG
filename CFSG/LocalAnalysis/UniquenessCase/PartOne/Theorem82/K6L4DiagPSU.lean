module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open

variable {K : Type} [Field K] [Finite K]

theorem d₀_le_su {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2) (h3 : r % 3 = 2)
    (ζ : CubeRoot K) : D₀ ζ ≤ StatedSU 4 r K := by
  rintro x ⟨v, rfl⟩
  have h_ufd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K :=
    ⟨hr, le_refl 1, by simpa using hK⟩
  have hpq : 3 ∣ r ^ 1 + 1 := by
    rw [pow_one]
    have h := Nat.div_add_mod r 3
    rw [h3] at h
    exact ⟨r / 3 + 1, by omega⟩
  rw [← pow_one r]
  rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h_ufd]
  refine ⟨det_stdDiagHom ζ v, ?_⟩
  have hd : ∀ i : Fin 4,
      h_ufd.bar ((ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : Kˣ) : K) *
      ((ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : Kˣ) : K) = 1 := by
    intro i
    apply CFSG.RankThree.PartOne.KCUnitaryPlane.bar_eq_inv_of_pow_eq_one h_ufd hpq
    have h3' : (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j)) ^ 3 = 1 := by
      simp only [CubeRoot.pow]
      rw [← pow_mul, mul_comm, pow_mul, ζ.pow_three, one_pow]
    have := congrArg (fun u : Kˣ => (u : K)) h3'
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hcoe : ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i =>
        (ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : K)) := rfl
  rw [hcoe, Matrix.diagonal_map (map_zero h_ufd.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact hd i

private theorem isDiag_commute {A B : Matrix (Fin 4) (Fin 4) K}
    (hA : A.IsDiag) (hB : B.IsDiag) : A * B = B * A := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem exists_unitary_conj_diag_su_le {r : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K) :
    StatedSU 4 r K ≤ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4) := by
  intro x hx
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
  simp only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one]
  have hx' : x ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU r 1 K 4 := by
    show x ∈ StatedSU 4 (r ^ 1) K
    rw [pow_one]
    exact hx
  exact ((CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).mp hx').2

private theorem exists_unitary_conj_diag_su_det {r : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K)
    {P : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4)} :
    h.bar ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det *
      ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.norm_det_eq_one h
    (1 : GL (Fin 4) K) P.2
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm] at h1
  rw [mul_comm] at h1
  exact h1

private theorem conj_eq_of_diag {D Yg : GL (Fin 4) K}
    (hD : (D : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hY : (Yg : Matrix (Fin 4) (Fin 4) K).IsDiag) : D⁻¹ * Yg * D = Yg := by
  have hcomm : D * Yg = Yg * D := by
    apply Units.ext
    exact isDiag_commute hD hY
  rw [mul_assoc, hcomm.symm, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem exists_unitary_conj_diag_su_Q {r : ℕ}
    (h_ufd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K)
    (P : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h_ufd
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4)) :
    ∃ D : GL (Fin 4) K, (D : Matrix (Fin 4) (Fin 4) K).IsDiag ∧
      (P : GL (Fin 4) K) * D ∈ StatedSU 4 r K := by
  let δ : K := ((P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det
  have hδ : h_ufd.bar δ * δ = 1 := exists_unitary_conj_diag_su_det h_ufd
  have hδ_ne : δ ≠ 0 := (Matrix.isUnits_det_units (P : GL (Fin 4) K)).ne_zero
  have hc : (h_ufd.bar δ)⁻¹ * δ⁻¹ = 1 := by rw [← mul_inv, hδ, inv_one]
  let D : GL (Fin 4) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![δ⁻¹, 1, 1, 1])
    (by rw [Matrix.det_diagonal, Fin.prod_univ_four]; simpa using inv_ne_zero hδ_ne)
  have hD : (D : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![δ⁻¹, 1, 1, 1] := rfl
  have hDdiag : (D : Matrix (Fin 4) (Fin 4) K).IsDiag := by
    rw [hD]; exact Matrix.isDiag_diagonal _
  have hDU : D ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h_ufd
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    simp only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one]
    rw [hD, Matrix.diagonal_map (map_zero h_ufd.bar), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hc]
  have hdetD : (D : Matrix (Fin 4) (Fin 4) K).det = δ⁻¹ := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_four]; simp
  refine ⟨D, hDdiag, ?_⟩
  have hQU : (P : GL (Fin 4) K) * D ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h_ufd
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4) := mul_mem P.2 hDU
  have hdetQ : (((P : GL (Fin 4) K) * D : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hdetD]
    change δ * δ⁻¹ = 1
    exact mul_inv_cancel₀ hδ_ne
  let Q : GL (Fin 4) K := (P : GL (Fin 4) K) * D
  have hQSU : Q ∈ StatedSU 4 r K := by
    have hQU' : Q ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU r 1 K 4 := by
      rw [CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h_ufd]
      refine ⟨?_, ?_⟩
      · rw [show Q = (P : GL (Fin 4) K) * D from rfl]; exact hdetQ
      · rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hQU
        simpa only [show Q = (P : GL (Fin 4) K) * D from rfl,
          CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one] using hQU
    rw [← pow_one r]
    exact hQU'
  exact hQSU

private theorem exists_unitary_conj_diag_su_conj {D P x Y : GL (Fin 4) K}
    (hY : Y = P⁻¹ * x * P) (hD : (D : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hYd : (Y : Matrix (Fin 4) (Fin 4) K).IsDiag) :
    (P * D)⁻¹ * x * (P * D) = Y := by
  rw [hY] at hYd ⊢
  rw [mul_inv_rev]
  rw [show (D⁻¹ * P⁻¹) * x * (P * D) = D⁻¹ * (P⁻¹ * x * P) * D by group]
  rw [conj_eq_of_diag hD hYd]

theorem exists_unitary_conj_diag_su {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (h3 : r % 3 = 2) (A : Subgroup (StatedSU 4 r K)) (hA : IsElemAbelian 3 A) :
    ∃ g : StatedSU 4 r K, ∀ x ∈ A,
      (((g * x * g⁻¹ : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  have h_ufd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K :=
    ⟨hr, le_refl 1, by simpa using hK⟩
  have hpq : 3 ∣ r ^ 1 + 1 := by
    rw [pow_one]
    have h := Nat.div_add_mod r 3
    rw [h3] at h
    exact ⟨r / 3 + 1, by omega⟩
  have hle := exists_unitary_conj_diag_su_le (K := K) h_ufd
  let G : Subgroup (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h_ufd
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 4)) := A.map (Subgroup.inclusion hle)
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := congrArg (fun z : A => Subgroup.inclusion hle (z : StatedSU 4 r K))
      (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    simpa using h
  have hpow : ∀ x ∈ G, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag
    (h := h_ufd) (n := 4) (p := 3) (by norm_num) hpq G hcomm hpow
  obtain ⟨D, hDdiag, hQSU⟩ := exists_unitary_conj_diag_su_Q h_ufd P
  let Q : GL (Fin 4) K := (P : GL (Fin 4) K) * D
  let g : StatedSU 4 r K := ⟨Q⁻¹, inv_mem hQSU⟩
  refine ⟨g, ?_⟩
  intro x hx
  have hxG : Subgroup.inclusion hle x ∈ G := Subgroup.mem_map_of_mem _ hx
  have hPx := hP (Subgroup.inclusion hle x) hxG
  set Yg : GL (Fin 4) K := (P : GL (Fin 4) K)⁻¹ * (x : GL (Fin 4) K) * (P : GL (Fin 4) K)
    with hYg
  have hYdiag : (Yg : Matrix (Fin 4) (Fin 4) K).IsDiag := by
    rw [hYg]
    simpa only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv] using hPx
  have hQeq : Q⁻¹ * (x : GL (Fin 4) K) * Q = Yg := by
    rw [show Q = (P : GL (Fin 4) K) * D from rfl]
    exact exists_unitary_conj_diag_su_conj hYg hDdiag hYdiag
  have hgoal : (((g * x * g⁻¹ : StatedSU 4 r K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (Yg : Matrix (Fin 4) (Fin 4) K) := by
    apply congrArg (fun h : GL (Fin 4) K => (h : Matrix (Fin 4) (Fin 4) K))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [show (g : GL (Fin 4) K) = Q⁻¹ from rfl, inv_inv]
    exact hQeq
  rw [hgoal]
  exact hYdiag

private theorem conjFact_su_le {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (h3 : r % 3 = 2) (ζ : CubeRoot K) (A : Subgroup (StatedSU 4 r K))
    (hA : IsElemAbelian 3 A) (g : StatedSU 4 r K)
    (hg : ∀ x ∈ A, (((g * x * g⁻¹ : StatedSU 4 r K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).IsDiag) :
    A.map (MulAut.conj g).toMonoidHom ≤ (D₀ ζ).subgroupOf (StatedSU 4 r K) := by
  rintro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  show (MulAut.conj g) x ∈ (D₀ ζ).subgroupOf (StatedSU 4 r K)
  rw [MulAut.conj_apply, Subgroup.mem_subgroupOf]
  refine mem_D₀_of_diag ζ (hg x hx) ?_ ?_
  · have h3' : (g * x * g⁻¹ : StatedSU 4 r K) ^ 3 = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hA.2 x hx, map_one]
    rw [← Subgroup.coe_pow, h3', Subgroup.coe_one]
  · exact CFSG.Open.StatedAPI.det_of_mem_statedSU (g * x * g⁻¹ : StatedSU 4 r K).2

theorem conjFact_su {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2) (h3 : r % 3 = 2)
    (ζ : CubeRoot K) : ConjFact (StatedSU 4 r K) ζ := by
  refine ⟨d₀_le_su hr hK h3 ζ, ?_⟩
  intro A hA hAcard
  obtain ⟨g, hg⟩ := exists_unitary_conj_diag_su hr hK h3 A hA
  refine ⟨g, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (conjFact_su_le hr hK h3 ζ A hA g hg) ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (d₀_le_su hr hK h3 ζ)).toEquiv,
      card_D₀ ζ, hAcard]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
