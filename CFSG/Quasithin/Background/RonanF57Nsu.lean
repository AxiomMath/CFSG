module

public import CFSG.Quasithin.Background.RonanF57Mat
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SemilinearConj
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CentralizerScalars
public import CFSG.Quasithin.Background.RonanF57Unitary

public section

namespace CFSG.Quasithin.RonanF57

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {K : Type} [Field K]

theorem unitary_of_isometry (h : UnitaryFieldData 2 1 K) {A : Matrix (Fin 4) (Fin 4) K}
    (hA : ∀ x y : Fin 4 → K, CFSG.LinearGroups.stdHermForm h 4 (A *ᵥ x) (A *ᵥ y) =
      CFSG.LinearGroups.stdHermForm h 4 x y) :
    (A.map h.bar)ᵀ * A = 1 := by
  ext i j
  have := hA (Pi.single i 1) (Pi.single j 1)
  rw [CFSG.LinearGroups.stdHermForm_single] at this
  simpa [CFSG.LinearGroups.stdHermForm_apply, Matrix.mulVec_single_one, Matrix.mul_apply,
    Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem center_su4_eq (hK : Nat.card K = 4) :
    Subgroup.center ↥(StatedSU 4 2 K) =
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 2 K) := by
  haveI := finite_of_card_four hK
  have h := unitaryFieldData_of_card hK
  ext z
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hz
    obtain ⟨κ, hκ⟩ := eq_scalar_of_commute_unitarySU h hK (n := 4) (by norm_num)
      (M := ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) fun g => by
        have := hz g
        have h2 := congrArg
          (fun x : ↥(StatedSU 4 2 K) => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) this
        simp only [Subgroup.coe_mul, Units.val_mul] at h2
        exact h2.symm
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      have h1 := congrArg (fun N : Matrix (Fin 4) (Fin 4) K => N *
        (((z : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hκ
      simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, map_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 0) 0
      simp at this
    exact ⟨Units.mk0 κ hκ0, Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hκ.symm)⟩
  · rintro ⟨c, hc⟩ g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hc]
    exact ((commute_scalar c (g : GL (Fin 4) K)).eq)

theorem exists_unitary_scalar_of_mem_NSU (hK : Nat.card K = 4) {g : GL (Fin 4) K}
    (hg : g ∈ NSU K) :
    ∃ (c : K) (u : GL (Fin 4) K), c ≠ 0 ∧
      ((u : Matrix (Fin 4) (Fin 4) K).map (unitaryFieldData_of_card hK).bar)ᵀ *
        (u : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = c • (u : Matrix (Fin 4) (Fin 4) K) := by
  classical
  haveI := finite_of_card_four hK
  have h := unitaryFieldData_of_card hK
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let e : ↥(StatedSU 4 2 K) ⧸ Subgroup.center ↥(StatedSU 4 2 K) ≃* StatedProj (StatedSU 4 2 K) :=
    QuotientGroup.quotientMulEquivOfEq (center_su4_eq hK)
  have hρe : ∀ s : ↥(StatedSU 4 2 K),
      e (QuotientGroup.mk ((MonoidHom.id ↥(StatedSU 4 2 K)) s)) =
        (QuotientGroup.mk s : StatedProj (StatedSU 4 2 K)) := fun s => rfl
  obtain ⟨φ, A, -, hAiso, -, hact⟩ := exists_semilinear_conj_of_normalizer
    (Y := GL (Fin 4) K) (L := StatedSU 4 2 K) (n := 4) (by norm_num) hK'
    (MonoidHom.id ↥(StatedSU 4 2 K)) e hρe hg
  have hAu := unitary_of_isometry h hAiso
  by_cases hφ : φ = 1
  · subst hφ
    have hAA' : ∀ s : ↥(StatedSU 4 2 K),
        A * (s : GL (Fin 4) K) * A⁻¹ = g * (s : GL (Fin 4) K) * g⁻¹ := by
      intro s
      obtain ⟨s', hs', hgs⟩ := hact s
      simp only [map_one, MulAut.one_apply, MonoidHom.id_apply] at hs' hgs
      rw [← hs', hgs]
    have hsc := scalar_of_conj_eq hK' (n := 4) (by norm_num) A g hAA'
    obtain ⟨c, hc⟩ := hsc
    refine ⟨(c : K), A, c.ne_zero, hAu, ?_⟩
    have hg' : g = A * Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
      rw [hc, mul_inv_cancel_left]
    rw [hg', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]
  · exfalso
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hφ (RingEquiv.ext hcon)
    have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
    have hx1 : x ≠ 1 := fun h1 => hx (by rw [h1, map_one])
    have hx3 : x ^ 3 = 1 := by
      have := h.finite
      have := Fintype.ofFinite K
      have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
      have := FiniteField.pow_card_sub_one_eq_one x hx0
      rwa [hc] at this
    have hx2 : x * x ^ 2 = 1 := by linear_combination hx3
    have hxxx : x * x * x = 1 := by linear_combination hx3
    set D : Matrix (Fin 4) (Fin 4) K :=
      Matrix.diagonal (fun i : Fin 4 => if i = 3 then (1 : K) else x) with hD
    set D' : Matrix (Fin 4) (Fin 4) K :=
      Matrix.diagonal (fun i : Fin 4 => if i = 3 then (1 : K) else x ^ 2) with hD'
    have hDD' : D * D' = 1 := by
      rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      ext i
      by_cases hi : i = 3 <;> simp [hi, hx2]
    have hD'D : D' * D = 1 := by
      rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      ext i
      by_cases hi : i = 3 <;> simp [hi, mul_comm, hx2]
    let s : GL (Fin 4) K := ⟨D, D', hDD', hD'D⟩
    have hs : s ∈ StatedSU 4 2 K := by
      rw [mem_su4_iff h]
      refine ⟨?_, ?_⟩
      · show D.det = 1
        rw [hD, Matrix.det_diagonal, Fin.prod_univ_four]
        simpa using hxxx
      · show (D.map h.bar)ᵀ * D = 1
        rw [hD, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
          Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        ext i
        by_cases hi : i = 3
        · simp [hi]
        · simp only [hi, if_false, bar_eq_sq h]
          linear_combination hx3
    obtain ⟨s', hs', hgs⟩ := hact ⟨s, hs⟩
    simp only [MonoidHom.id_apply] at hs' hgs
    have hgs' : g * s * g⁻¹ = A * UnitaryHigher.glAut φ s * A⁻¹ := by rw [hgs, hs']
    have hX : A⁻¹ * g * s = UnitaryHigher.glAut φ s * (A⁻¹ * g) := by
      calc A⁻¹ * g * s = A⁻¹ * (g * s * g⁻¹) * g := by group
        _ = A⁻¹ * (A * UnitaryHigher.glAut φ s * A⁻¹) * g := by rw [hgs']
        _ = UnitaryHigher.glAut φ s * (A⁻¹ * g) := by group
    set X : Matrix (Fin 4) (Fin 4) K := ((A⁻¹ * g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      with hXdef
    have hglφ : ((UnitaryHigher.glAut φ s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal (fun i : Fin 4 => if i = 3 then (1 : K) else φ x) := by
      rw [UnitaryHigher.coe_glAut]
      show D.map φ = _
      rw [hD, Matrix.diagonal_map (map_zero _)]
      congr 1
      ext i
      by_cases hi : i = 3 <;> simp [hi]
    have hXm : X * D = Matrix.diagonal (fun i : Fin 4 => if i = 3 then (1 : K) else φ x) * X := by
      have := congrArg (fun y : GL (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K)) hX
      simp only [Units.val_mul] at this
      rw [← hglφ]
      simpa [hXdef, Matrix.mul_assoc] using this
    have hcol : ∀ i, X i 0 = 0 := by
      intro i
      have h1 := congrFun (congrFun hXm i) 0
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      have h0 : (0 : Fin 4) ≠ 3 := by decide
      by_cases hi : i = 3
      · subst hi
        simp only [hD, Matrix.diagonal_apply_eq, h0, if_false, if_true] at h1
        have : (x - 1) * X 3 0 = 0 := by linear_combination h1
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx1)
      · simp only [hD, Matrix.diagonal_apply_eq, h0, hi, if_false] at h1
        have : (x - φ x) * X i 0 = 0 := by linear_combination h1
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hx))
    have hz : X *ᵥ (Pi.single 0 1) = 0 := by
      ext i
      simp [Matrix.mulVec_single_one, hcol i]
    have hinv : ((g⁻¹ * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * X = 1 := by
      rw [hXdef, ← Units.val_mul]
      have : g⁻¹ * A * (A⁻¹ * g) = 1 := by group
      rw [this, Units.val_one]
    have h1 := congrArg (fun v => ((g⁻¹ * A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) hz
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    have := congrFun h1 0
    simp at this

end CFSG.Quasithin.RonanF57
