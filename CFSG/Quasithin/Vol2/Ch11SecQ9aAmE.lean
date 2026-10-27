module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar Matrix

variable {K : Type} [Field K]

abbrev dvec (ω : K) : Fin 3 → K := ![1, ω, ω ^ 2]

@[expose] def yDiag (ω : K) (hω : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal (dvec ω), by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [dvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_mul]
    rw [← pow_succ']
    exact hω⟩

theorem coe_yDiag (ω : K) (hω : ω ^ 3 = 1) :
    ((yDiag ω hω : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (dvec ω) := rfl

theorem yDiag_mem_upperTriangular (ω : K) (hω : ω ^ 3 = 1) :
    yDiag ω hω ∈ upperTriangular 3 K := fun i j hij => by
  rw [coe_yDiag]
  exact diagonal_apply_ne _ (ne_of_gt hij)

theorem dvec_injective {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    Function.Injective (dvec ω) := by
  have h0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have h2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have : ω ^ 3 = ω ^ 2 * ω := by ring
    rw [hω, h, one_mul] at this
    exact this.symm
  have h12 : ω ≠ ω ^ 2 := by
    intro h
    apply hω1
    have : ω ^ 2 = ω * ω := by ring
    rw [this] at h
    exact (mul_eq_left₀ h0).mp h.symm
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [dvec, eq_comm]

theorem single_mem_flagSpace {d : ℕ} {k : Fin 3} (hk : (k : ℕ) < d) :
    (Pi.single k (1 : K) : Fin 3 → K) ∈ flagSpace 3 K d :=
  mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (fun h => by subst h; omega) _

theorem eq_one_of_mem_radU {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {d : ℕ} (hd1 : 1 ≤ d)
    {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ radU K (flagSpace 3 K d)) {c : K}
    (hc : (u : Matrix (Fin 3) (Fin 3) K) * diagonal (dvec ω) =
      c • (diagonal (dvec ω) * (u : Matrix (Fin 3) (Fin 3) K))) : u = 1 := by
  set U : Matrix (Fin 3) (Fin 3) K := (u : Matrix (Fin 3) (Fin 3) K) with hU
  set D : Matrix (Fin 3) (Fin 3) K := diagonal (dvec ω) with hD
  have hDe : ∀ k : Fin 3, D *ᵥ Pi.single k 1 = dvec ω k • Pi.single k (1 : K) := fun k => by
    rw [hD, diagonal_mulVec_single, mul_one, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hfix : ∀ k : Fin 3, (k : ℕ) < d → U *ᵥ Pi.single k 1 = Pi.single k 1 := fun k hk =>
    hu.2 _ (single_mem_flagSpace hk)
  have hc1 : c = 1 := by
    have h := congrArg (fun M => M *ᵥ Pi.single (0 : Fin 3) (1 : K)) hc
    rw [← mulVec_mulVec, hDe, mulVec_smul, hfix 0 (by simp; omega), smul_mulVec,
      ← mulVec_mulVec, hfix 0 (by simp; omega), hDe] at h
    have h0 := congrFun h 0
    simp [dvec] at h0
    exact h0.symm
  rw [hc1, one_smul] at hc
  have hcol : ∀ k : Fin 3, U *ᵥ Pi.single k 1 = Pi.single k 1 := by
    intro k
    set w : Fin 3 → K := U *ᵥ Pi.single k 1 - Pi.single k 1 with hw
    have hwW : w ∈ flagSpace 3 K d := hu.1 _
    have hDw : D *ᵥ w = dvec ω k • w := by
      rw [hw, mulVec_sub, mulVec_mulVec, ← hc, ← mulVec_mulVec, hDe, mulVec_smul, smul_sub]
    have hwi : ∀ i, w i = 0 := by
      intro i
      by_cases hik : i = k
      · subst hik
        by_cases hkd : (i : ℕ) < d
        · rw [hw, hfix i hkd, sub_self, Pi.zero_apply]
        · exact mem_flagSpace.mp hwW i (by omega)
      · have h := congrFun hDw i
        rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
        have h' : (dvec ω i - dvec ω k) * w i = 0 := by rw [sub_mul, h, sub_self]
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd (dvec_injective hω hω1 (sub_eq_zero.mp h'')) hik
        · exact h''
    have : w = 0 := funext hwi
    rwa [hw, sub_eq_zero] at this
  ext i k
  have h := congrFun (hcol k) i
  rw [mulVec_single_one] at h
  simpa [Matrix.col_apply, Pi.single_apply, Matrix.one_apply, eq_comm] using h

theorem exists_cubeRoot [Finite K] (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hu]
    norm_num
  obtain ⟨u, hu1⟩ := exists_ne (1 : Kˣ)
  refine ⟨u, ?_, fun h => hu1 (Units.ext h)⟩
  have h3 : u ^ 3 = 1 := by rw [← hu]; exact pow_card_eq_one'
  have := congrArg Units.val h3
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

theorem exists_fpf_parab34 [Finite K] [CharP K 2] (hK : Nat.card K = 4) (j : Fin 2) :
    ∃ y ∈ C11P9A.parab34 K j, orderOf y = 3 ∧
      ∀ b ∈ pCoreOf 2 (C11P9A.parab34 K j), y * b * y⁻¹ = b → b = 1 := by
  obtain ⟨ω, hω, hω1⟩ := exists_cubeRoot hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨proj 3 K (yDiag ω hω), ⟨yDiag ω hω, upperTriangular_le_stabilizer_flagSpace _
    (yDiag_mem_upperTriangular ω hω), rfl⟩, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have h6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
      have h3 : yDiag ω hω ^ 3 = 1 := by
        have hm : ((yDiag ω hω ^ 3 : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) = 1 := by
          rw [Matrix.SpecialLinearGroup.coe_pow, coe_yDiag, diagonal_pow, ← diagonal_one]
          congr 1
          funext i
          fin_cases i <;> simp [dvec, hω, h6]
        ext i k
        simp [hm]
      rw [h3, map_one]
    · intro h1
      have hmem : yDiag ω hω ∈ scalars 3 K := (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨c, -, hc⟩ := hmem
      have h00 := congrFun (congrFun hc 0) 0
      have h11 := congrFun (congrFun hc 1) 1
      simp [coe_yDiag, dvec, scalar_apply] at h00 h11
      exact hω1 (h11.trans h00.symm)
  · intro b hb hyb
    rw [C11P9A.pCoreOf_parab34 hK j] at hb
    obtain ⟨u, hu, rfl⟩ := hb
    set y := yDiag ω hω with hy
    have hq : proj 3 K (y * u * y⁻¹) = proj 3 K u := by
      rw [map_mul, map_mul, map_inv]
      exact hyb
    have hz : (y * u * y⁻¹)⁻¹ * u ∈ scalars 3 K := QuotientGroup.eq.mp hq
    set z := (y * u * y⁻¹)⁻¹ * u with hzdef
    have hzc : y⁻¹ * z * y = z := by
      have := Subgroup.mem_center_iff.mp (scalars_le_center 3 K hz) y
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have huy : u * y = y * u * z := by
      have hu' : u = y * u * y⁻¹ * z := by rw [hzdef, mul_inv_cancel_left]
      calc u * y = y * u * y⁻¹ * z * y := by rw [← hu']
        _ = y * u * (y⁻¹ * z * y) := by group
        _ = y * u * z := by rw [hzc]
    obtain ⟨c, -, hc⟩ := hz
    have hUD : (u : Matrix (Fin 3) (Fin 3) K) * diagonal (dvec ω) =
        (c : K) • (diagonal (dvec ω) * (u : Matrix (Fin 3) (Fin 3) K)) := by
      have hm : (u : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
          (y : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) *
            (z : Matrix (Fin 3) (Fin 3) K) := by
        simpa using
          congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) huy
      have hyD : (y : Matrix (Fin 3) (Fin 3) K) = diagonal (dvec ω) := coe_yDiag ω hω
      rw [hc, hyD] at hm
      rw [hm]
      ext i k
      simp [scalar_apply, Matrix.mul_diagonal, mul_comm]
    rw [eq_one_of_mem_radU hω hω1 (by omega) hu hUD, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
