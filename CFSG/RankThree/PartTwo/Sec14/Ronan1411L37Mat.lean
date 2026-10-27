module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1411L37

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank
open Matrix (ProjGenLinGroup)

section Mat

variable {K : Type} [Field K]

private theorem block_zero_of_comm {ε : K} (hε : ε ≠ 1) {X : Matrix (Fin 3) (Fin 3) K}
    (h : diagonal ![ε, 1, 1] * X = X * diagonal ![ε, 1, 1]) :
    X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 1 0 = 0 ∧ X 2 0 = 0 := by
  have hk : ∀ i j, (![ε, 1, 1] i) * X i j = X i j * (![ε, 1, 1] j) := fun i j => by
    have := congrFun (congrFun h i) j
    rwa [diagonal_mul, mul_diagonal] at this
  have hε' : ε - 1 ≠ 0 := sub_ne_zero.mpr hε
  have h01 := hk 0 1
  have h02 := hk 0 2
  have h10 := hk 1 0
  have h20 := hk 2 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, mul_one, one_mul] at h01 h02 h10 h20
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (show (ε - 1) * X 0 1 = 0 by linear_combination h01)).resolve_left hε'
  · exact (mul_eq_zero.mp (show (ε - 1) * X 0 2 = 0 by linear_combination h02)).resolve_left hε'
  · exact (mul_eq_zero.mp (show (ε - 1) * X 1 0 = 0 by linear_combination -h10)).resolve_left hε'
  · exact (mul_eq_zero.mp (show (ε - 1) * X 2 0 = 0 by linear_combination -h20)).resolve_left hε'

private theorem sl2_involution {a b c d : K} (h2 : (2 : K) ≠ 0) (h₁ : a * a + b * c = 1)
    (h₂ : a * b + b * d = 0) (h₃ : c * a + d * c = 0) (h₄ : c * b + d * d = 1)
    (hdet : a * d - b * c = 1) : b = 0 ∧ c = 0 ∧ ((a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1)) := by
  have had : a + d ≠ 0 := by
    intro h
    apply h2
    linear_combination (-1 : K) * h₁ - hdet + a * h
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination h₂
    exact (mul_eq_zero.mp this).resolve_right had
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination h₃
    exact (mul_eq_zero.mp this).resolve_right had
  subst hb hc
  have ha2 : a * a = 1 := by linear_combination h₁
  have hda : d = a := by
    have h' : a * d = 1 := by linear_combination hdet
    have : d = a * (a * d) := by linear_combination (-d) * ha2
    rw [this, h', mul_one]
  subst hda
  refine ⟨rfl, rfl, ?_⟩
  have : (d - 1) * (d + 1) = 0 := by linear_combination ha2
  rcases mul_eq_zero.mp this with h | h
  · left; constructor <;> linear_combination h
  · right; constructor <;> linear_combination h

private theorem mul_apply_zero_zero {X Y : Matrix (Fin 3) (Fin 3) K} (hX1 : X 0 1 = 0)
    (hX2 : X 0 2 = 0) : (X * Y) 0 0 = X 0 0 * Y 0 0 := by
  rw [mul_apply, Fin.sum_univ_three, hX1, hX2]
  ring

theorem false_of_type2_mat {ε : K} (hε : ε ≠ 1) (h2 : (2 : K) ≠ 0)
    {T₁ T₂ B : Matrix (Fin 3) (Fin 3) K} (hT₁ : T₁ * T₁ = 1) (hT₂ : T₂ * T₂ = 1)
    (hd₁ : T₁.det = 1) (hd₂ : T₂.det = 1) (hT₁1 : T₁ ≠ 1) (hT₂1 : T₂ ≠ 1) (hne : T₁ ≠ T₂)
    (hc₁ : diagonal ![ε, 1, 1] * T₁ = T₁ * diagonal ![ε, 1, 1])
    (hc₂ : diagonal ![ε, 1, 1] * T₂ = T₂ * diagonal ![ε, 1, 1])
    (hcB : diagonal ![ε, 1, 1] * B = B * diagonal ![ε, 1, 1]) (hB : B.det ≠ 0)
    (hB₁ : B * T₁ = T₂ * B) (hB₂ : B * T₂ = T₁ * T₂ * B) : False := by
  obtain ⟨a01, a02, a10, a20⟩ := block_zero_of_comm hε hc₁
  obtain ⟨b01, b02, b10, b20⟩ := block_zero_of_comm hε hc₂
  obtain ⟨c01, c02, c10, c20⟩ := block_zero_of_comm hε hcB
  have hdet3 : ∀ X : Matrix (Fin 3) (Fin 3) K, X 0 1 = 0 → X 0 2 = 0 → X 1 0 = 0 → X 2 0 = 0 →
      X.det = X 0 0 * (X 1 1 * X 2 2 - X 1 2 * X 2 1) := fun X h01 h02 h10 h20 => by
    rw [det_fin_three, h01, h02, h10, h20]
    ring
  have hB0 : B 0 0 ≠ 0 := by
    intro h
    apply hB
    rw [hdet3 B c01 c02 c10 c20, h, zero_mul]
  have hT20 : T₂ 0 0 ≠ 0 := by
    intro h
    have := hdet3 T₂ b01 b02 b10 b20
    rw [hd₂, h, zero_mul] at this
    exact one_ne_zero this
  have e1 := congrFun (congrFun hB₁ 0) 0
  rw [mul_apply_zero_zero c01 c02, mul_apply_zero_zero b01 b02] at e1
  have e2 := congrFun (congrFun hB₂ 0) 0
  have h12_01 : (T₁ * T₂) 0 1 = 0 := by
    rw [mul_apply, Fin.sum_univ_three, a01, a02, b01]
    ring
  have h12_02 : (T₁ * T₂) 0 2 = 0 := by
    rw [mul_apply, Fin.sum_univ_three, a01, a02, b02]
    ring
  rw [mul_apply_zero_zero c01 c02, mul_apply_zero_zero h12_01 h12_02,
    mul_apply_zero_zero a01 a02] at e2
  have hT1T2 : T₁ 0 0 = T₂ 0 0 := by
    have : B 0 0 * (T₁ 0 0 - T₂ 0 0) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hB0)
  have hT1one : T₁ 0 0 = 1 := by
    have : B 0 0 * T₂ 0 0 * (1 - T₁ 0 0) = 0 := by linear_combination e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hB0 hT20)
    · exact (sub_eq_zero.mp h).symm
  have hT2one : T₂ 0 0 = 1 := hT1T2 ▸ hT1one
  have hblock : ∀ X : Matrix (Fin 3) (Fin 3) K, X * X = 1 → X.det = 1 → X 0 0 = 1 →
      X 0 1 = 0 → X 0 2 = 0 → X 1 0 = 0 → X 2 0 = 0 → X ≠ 1 →
      X 1 1 = -1 ∧ X 2 2 = -1 ∧ X 1 2 = 0 ∧ X 2 1 = 0 := by
    intro X hX hXd hX00 h01 h02 h10 h20 hX1
    have q11 := congrFun (congrFun hX 1) 1
    have q12 := congrFun (congrFun hX 1) 2
    have q21 := congrFun (congrFun hX 2) 1
    have q22 := congrFun (congrFun hX 2) 2
    simp only [mul_apply, Fin.sum_univ_three, h10, h20, h01, h02, zero_mul, mul_zero, zero_add,
      one_apply_eq, one_apply_ne (show (1 : Fin 3) ≠ 2 by decide),
      one_apply_ne (show (2 : Fin 3) ≠ 1 by decide)] at q11 q12 q21 q22
    have hdet := hdet3 X h01 h02 h10 h20
    rw [hXd, hX00, one_mul] at hdet
    obtain ⟨hb, hc, hpm⟩ := sl2_involution h2 q11 q12 q21 q22 hdet.symm
    rcases hpm with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · exfalso
      apply hX1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h20, hX00, ha, hd, hb, hc]
    · exact ⟨ha, hd, hb, hc⟩
  obtain ⟨p11, p22, p12, p21⟩ := hblock T₁ hT₁ hd₁ hT1one a01 a02 a10 a20 hT₁1
  obtain ⟨r11, r22, r12, r21⟩ := hblock T₂ hT₂ hd₂ hT2one b01 b02 b10 b20 hT₂1
  apply hne
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a01, a02, a10, a20, b01, b02, b10, b20, hT1one, hT2one, p11, p22, p12, p21, r11, r22,
      r12, r21]

end Mat


section Lift

variable {K : Type} [Field K]

private theorem eq_one_of_sq_cube {κ : Kˣ} (h2 : κ ^ 2 = 1) (h3 : κ ^ 3 = 1) : κ = 1 := by
  calc κ = κ ^ 3 * (κ ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, mul_one]

private theorem coe_scalar_eq (κ : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) κ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (κ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  rfl

private theorem eq_one_of_scalar_eq_one {κ : Kˣ}
    (h : (GeneralLinearGroup.scalar (Fin 3) κ : GL (Fin 3) K) = 1) : κ = 1 := by
  have h1 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_scalar_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Units.val_one] at h1
  exact Units.ext h1

private theorem det_scalar_eq (κ : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) κ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (κ : K) ^ 3 := by
  rw [coe_scalar_eq, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]

private theorem exists_involution_lift {w : GL (Fin 3) K}
    (hw : (w : Matrix (Fin 3) (Fin 3) K).det = 1) (hw2 : w * w ∈ StatedScalars (Fin 3) K) :
    ∃ T : GL (Fin 3) K, ProjGenLinGroup.mk T = ProjGenLinGroup.mk w ∧ T * T = 1 ∧
      (T : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  obtain ⟨lam, hlam⟩ := hw2
  have hdet : ((lam : K)) ^ 3 = 1 := by
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).det) hlam
    simp only [det_scalar_eq, Units.val_mul, Matrix.det_mul, hw, mul_one] at this
    exact this
  refine ⟨GeneralLinearGroup.scalar (Fin 3) lam * w, ?_, ?_, ?_⟩
  · rw [map_mul, (mk_eq_one_iff_mem_statedScalars).mpr ⟨lam, rfl⟩, one_mul]
  · have hc : w * GeneralLinearGroup.scalar (Fin 3) lam =
        GeneralLinearGroup.scalar (Fin 3) lam * w :=
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar lam w).eq
    calc GeneralLinearGroup.scalar (Fin 3) lam * w * (GeneralLinearGroup.scalar (Fin 3) lam * w) =
        GeneralLinearGroup.scalar (Fin 3) lam * GeneralLinearGroup.scalar (Fin 3) lam *
          (w * w) := by
          rw [mul_assoc, ← mul_assoc w, hc]; group
      _ = GeneralLinearGroup.scalar (Fin 3) (lam ^ 3) := by
          rw [← hlam, ← map_mul, ← map_mul]; congr 1; rw [pow_succ, sq]
      _ = 1 := by
          rw [show lam ^ 3 = 1 from Units.ext (by simpa using hdet), map_one]
  · rw [Units.val_mul, Matrix.det_mul, det_scalar_eq, hw, mul_one, hdet]

private theorem conj_eq_of_mk_eq {g T T' : GL (Fin 3) K} (hT : T * T = 1) (hT' : T' * T' = 1)
    (hdT : (T : Matrix (Fin 3) (Fin 3) K).det = 1) (hdT' : (T' : Matrix (Fin 3) (Fin 3) K).det = 1)
    (h : ProjGenLinGroup.mk (g * T * g⁻¹) = ProjGenLinGroup.mk T') : g * T * g⁻¹ = T' := by
  have hs : (g * T * g⁻¹)⁻¹ * T' ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨κ, hκ⟩ := hs
  have hT'eq : T' = g * T * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) κ := by rw [hκ]; group
  have hc : ∀ A : GL (Fin 3) K, A * GeneralLinearGroup.scalar (Fin 3) κ =
      GeneralLinearGroup.scalar (Fin 3) κ * A :=
    fun A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar κ A).eq
  have h2 : κ ^ 2 = 1 := by
    apply eq_one_of_scalar_eq_one
    have : T' * T' = GeneralLinearGroup.scalar (Fin 3) (κ ^ 2) := by
      rw [hT'eq, map_pow]
      calc g * T * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) κ *
            (g * T * g⁻¹ * GeneralLinearGroup.scalar (Fin 3) κ) =
          g * (T * T) * g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) κ *
            GeneralLinearGroup.scalar (Fin 3) κ) := by
            rw [mul_assoc (g * T * g⁻¹), ← mul_assoc (GeneralLinearGroup.scalar (Fin 3) κ),
              ← hc (g * T * g⁻¹)]
            group
        _ = GeneralLinearGroup.scalar (Fin 3) κ ^ 2 := by
            rw [hT, mul_one, mul_inv_cancel, one_mul, sq]
    rw [← this, hT']
  have h3 : κ ^ 3 = 1 := by
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).det) hT'eq
    simp only [Units.val_mul, Matrix.det_mul, det_scalar_eq, hdT, hdT', mul_one] at this
    have hgg : (g : Matrix (Fin 3) (Fin 3) K).det * (↑g⁻¹ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rw [hgg, one_mul] at this
    exact Units.ext (by simpa using this.symm)
  rw [hT'eq, eq_one_of_sq_cube h2 h3, map_one, mul_one]

end Lift

section Types

variable {K : Type} [Field K] {p f : ℕ}

private theorem eq_zero_of_mulVec_eq_zero {M : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ v : Fin 3 → K, M *ᵥ v = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

private theorem false_of_type3_comm (h2 : (2 : K) ≠ 0) {y T : GL (Fin 3) K}
    (hy : Type123 true (p ^ f) K y 3) (hT : T * T = 1)
    (hdT : (T : Matrix (Fin 3) (Fin 3) K).det = 1) (hT1 : T ≠ 1) (hyT : y * T = T * y) :
    False := by
  obtain ⟨-, -, hirr⟩ := hy
  set N : Matrix (Fin 3) (Fin 3) K := (T : Matrix (Fin 3) (Fin 3) K) - 1 with hN
  have hyM : (y : Matrix (Fin 3) (Fin 3) K) * (T : Matrix (Fin 3) (Fin 3) K) =
      (T : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg Units.val hyT
    simpa using this
  have hTM : (T : Matrix (Fin 3) (Fin 3) K) * (T : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have := congrArg Units.val hT
    simpa using this
  have hNy : N * (y : Matrix (Fin 3) (Fin 3) K) = (y : Matrix (Fin 3) (Fin 3) K) * N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hyM]
  rcases hirr (LinearMap.ker (Matrix.mulVecLin N)) (fun v hv => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hNy, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]) with h | h
  ·
    have hall : ∀ v : Fin 3 → K, ((T : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ v = 0 := by
      intro v
      have hmem : ((T : Matrix (Fin 3) (Fin 3) K) + 1) *ᵥ v ∈
          LinearMap.ker (Matrix.mulVecLin N) := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN,
          show ((T : Matrix (Fin 3) (Fin 3) K) - 1) * ((T : Matrix (Fin 3) (Fin 3) K) + 1) = 0 by
            rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, hTM, Matrix.mul_one,
              Matrix.one_mul, Matrix.one_mul]
            abel, Matrix.zero_mulVec]
      rw [h] at hmem
      exact (Submodule.mem_bot K).mp hmem
    have hTm : (T : Matrix (Fin 3) (Fin 3) K) = -1 := by
      have := eq_zero_of_mulVec_eq_zero hall
      exact eq_neg_of_add_eq_zero_left this
    rw [hTm, Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at hdT
    apply h2
    linear_combination -hdT
  ·
    apply hT1
    have hall : ∀ v : Fin 3 → K, N *ᵥ v = 0 := by
      intro v
      have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin N) := by rw [h]; trivial
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
    have := eq_zero_of_mulVec_eq_zero hall
    exact Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp this)

private theorem false_of_type2_comm (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    (h2 : (2 : K) ≠ 0) {y T₁ T₂ B : GL (Fin 3) K} (hy : Type123 true (p ^ f) K y 2)
    (hT₁ : T₁ * T₁ = 1) (hT₂ : T₂ * T₂ = 1) (hd₁ : (T₁ : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hd₂ : (T₂ : Matrix (Fin 3) (Fin 3) K).det = 1) (hT₁1 : T₁ ≠ 1) (hT₂1 : T₂ ≠ 1)
    (hne : T₁ ≠ T₂) (hy₁ : y * T₁ = T₁ * y) (hy₂ : y * T₂ = T₂ * y)
    (hyB : y * B * y⁻¹ * B⁻¹ ∈ StatedScalars (Fin 3) K) (hB₁ : B * T₁ = T₂ * B)
    (hB₂ : B * T₂ = T₁ * T₂ * B) : False := by
  have hπ : true = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨ε, hε3, hε1, z, hz, g, -, hD⟩ := hy
  have hzs : z ∈ StatedScalars (Fin 3) K := by
    rw [zPi_eq hπ hq' hτ hτ1] at hz
    exact hz.2
  have hzc : ∀ A : GL (Fin 3) K, A * z = z * A := fun A => commute_of_mem_statedScalars hzs A
  set D := diagE ε with hDdef
  have hconj : ∀ T : GL (Fin 3) K, y * T = T * y →
      D * (g⁻¹ * T * g) = (g⁻¹ * T * g) * D := by
    intro T hT
    rw [← hD]
    calc g⁻¹ * (y * z) * g * (g⁻¹ * T * g) = g⁻¹ * (y * (z * T)) * g := by group
      _ = g⁻¹ * (y * T * z) * g := by rw [← hzc T]; group
      _ = g⁻¹ * (T * y * z) * g := by rw [hT]
      _ = g⁻¹ * T * g * (g⁻¹ * (y * z) * g) := by group
  obtain ⟨ρ, hρ⟩ := hyB
  have hyB' : y * B = GeneralLinearGroup.scalar (Fin 3) ρ * B * y := by
    rw [hρ]; group
  have hsc : ∀ A : GL (Fin 3) K, A * GeneralLinearGroup.scalar (Fin 3) ρ =
      GeneralLinearGroup.scalar (Fin 3) ρ * A :=
    fun A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ρ A).eq
  set B' := g⁻¹ * B * g with hB'
  have key : y * z * B = GeneralLinearGroup.scalar (Fin 3) ρ * B * y * z := by
    calc y * z * B = y * (z * B) := by group
      _ = y * (B * z) := by rw [hzc B]
      _ = y * B * z := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ρ * B * y * z := by rw [hyB']
  have hDB : D * B' = GeneralLinearGroup.scalar (Fin 3) ρ * B' * D := by
    rw [← hD, hB']
    calc g⁻¹ * (y * z) * g * (g⁻¹ * B * g) = g⁻¹ * (y * z * B) * g := by group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ρ * B * y * z) * g := by rw [key]
      _ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) ρ * (B * y * z) * g := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ρ * g⁻¹ * (B * y * z) * g := by rw [hsc g⁻¹]
      _ = GeneralLinearGroup.scalar (Fin 3) ρ * (g⁻¹ * B * g) * (g⁻¹ * (y * z) * g) := by group
  have hρ1 : ρ = 1 := by
    have h1 : B'⁻¹ * D * B' = D * GeneralLinearGroup.scalar (Fin 3) ρ := by
      calc B'⁻¹ * D * B' = B'⁻¹ * (D * B') := by group
        _ = B'⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ρ * B' * D) := by rw [hDB]
        _ = B'⁻¹ * (B' * GeneralLinearGroup.scalar (Fin 3) ρ * D) := by rw [hsc B']
        _ = GeneralLinearGroup.scalar (Fin 3) ρ * D := by group
        _ = D * GeneralLinearGroup.scalar (Fin 3) ρ := by rw [hsc D]
    have htr := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).trace) h1
    simp only [trace_inv_conj, trace_mul_scalar, hDdef, trace_diagE] at htr
    have h3K := hK.three_ne_zero hq
    have hne0 : (ε : K) + 2 ≠ 0 := by
      intro h0
      apply h3K
      have he : (ε : K) = -2 := by linear_combination h0
      have : ((ε : K)) ^ 3 = 1 := hε3
      rw [he] at this
      have h9 : (3 : K) * 3 = 0 := by linear_combination -this
      exact (mul_self_eq_zero.mp h9)
    have : ((ρ : K) - 1) * ((ε : K) + 2) = 0 := by linear_combination -htr
    exact Units.ext ((sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne0)))
  rw [hρ1, map_one, one_mul] at hDB
  have hDm : ((D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(ε : K), 1, 1] :=
    coe_diagE ε
  have hval : ∀ X Y : GL (Fin 3) K, X * Y = Y * X →
      (X : Matrix (Fin 3) (Fin 3) K) * (Y : Matrix (Fin 3) (Fin 3) K) =
        (Y : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) := fun X Y h => by
    have := congrArg Units.val h
    simpa using this
  have hdetc : ∀ T : GL (Fin 3) K, ((g⁻¹ * T * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = (T : Matrix (Fin 3) (Fin 3) K).det := fun T => by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  have hsq : ∀ T : GL (Fin 3) K, T * T = 1 →
      ((g⁻¹ * T * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ * T * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := fun T hT => by
    rw [← Units.val_mul, show g⁻¹ * T * g * (g⁻¹ * T * g) = g⁻¹ * (T * T) * g by group, hT]
    simp
  have hne1 : ∀ T : GL (Fin 3) K, T ≠ 1 →
      ((g⁻¹ * T * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := fun T hT h => by
    apply hT
    have h' : g⁻¹ * T * g = 1 := Units.ext (by rw [Units.val_one]; exact h)
    calc T = g * (g⁻¹ * T * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hc₁ : diagonal ![(ε : K), 1, 1] * ((g⁻¹ * T₁ * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ * T₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![(ε : K), 1, 1] := by
    rw [← hDm]; exact hval _ _ (hconj T₁ hy₁)
  have hc₂ : diagonal ![(ε : K), 1, 1] * ((g⁻¹ * T₂ * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ * T₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![(ε : K), 1, 1] := by
    rw [← hDm]; exact hval _ _ (hconj T₂ hy₂)
  have hcB : diagonal ![(ε : K), 1, 1] * (B' : Matrix (Fin 3) (Fin 3) K) =
      (B' : Matrix (Fin 3) (Fin 3) K) * diagonal ![(ε : K), 1, 1] := by
    rw [← hDm]; exact hval _ _ hDB
  have hdB : (B' : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    have := (GeneralLinearGroup.det B').ne_zero
    rwa [GeneralLinearGroup.val_det_apply] at this
  have hBT₁ : (B' : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * T₁ * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ * T₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (B' : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, hB',
      show g⁻¹ * B * g * (g⁻¹ * T₁ * g) = g⁻¹ * (B * T₁) * g by group,
      show g⁻¹ * T₂ * g * (g⁻¹ * B * g) = g⁻¹ * (T₂ * B) * g by group, hB₁]
  have hBT₂ : (B' : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ * T₂ * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ * T₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ * T₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (B' : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hB',
      show g⁻¹ * B * g * (g⁻¹ * T₂ * g) = g⁻¹ * (B * T₂) * g by group,
      show g⁻¹ * T₁ * g * (g⁻¹ * T₂ * g) * (g⁻¹ * B * g) = g⁻¹ * (T₁ * T₂ * B) * g by group,
      hB₂]
  have hne' : ((g⁻¹ * T₁ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      ((g⁻¹ * T₂ * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro h
    apply hne
    have h' : g⁻¹ * T₁ * g = g⁻¹ * T₂ * g := Units.ext h
    calc T₁ = g * (g⁻¹ * T₁ * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * T₂ * g) * g⁻¹ := by rw [h']
      _ = T₂ := by group
  exact false_of_type2_mat (fun h => hε1 (Units.ext h)) h2 (hsq T₁ hT₁) (hsq T₂ hT₂)
    (by rw [hdetc, hd₁]) (by rw [hdetc, hd₂]) (hne1 T₁ hT₁1) (hne1 T₂ hT₂1) hne' hc₁ hc₂ hcB hdB
    hBT₁ hBT₂

end Types

section Fix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ}

theorem false_of_fix_four (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    (h2 : (2 : K) ≠ 0) [Group.IsPerfect (projImage (slPi true 3 (p ^ f) K))]
    (e : L ≃* projImage (slPi true 3 (p ^ f) K)) {a : G} {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) (ha3 : a ^ 3 = 1) (haC : a ∉ Subgroup.centralizer (L : Set G))
    (hnin : ¬ ∃ l ∈ slPi true 3 (p ^ f) K, ∀ m ∈ slPi true 3 (p ^ f) K,
      y * m * y⁻¹ = l * m * l⁻¹)
    {t₁ t₂ b : G} (ht₁ : t₁ ∈ L) (ht₂ : t₂ ∈ L) (hb : b ∈ L) (ht₁2 : t₁ ^ 2 = 1)
    (ht₂2 : t₂ ^ 2 = 1) (ht₁1 : t₁ ≠ 1) (ht₂1 : t₂ ≠ 1) (h12 : t₁ ≠ t₂)
    (hc12 : t₁ * t₂ = t₂ * t₁) (ha₁ : a * t₁ = t₁ * a) (ha₂ : a * t₂ = t₂ * a)
    (hab : a * b = b * a) (hb₁ : b * t₁ * b⁻¹ = t₂) (hb₂ : b * t₂ * b⁻¹ = t₁ * t₂) : False := by
  have hlift : ∀ (t : G) (ht : t ∈ L), t ^ 2 = 1 → ∃ T : GL (Fin 3) K,
      ProjGenLinGroup.mk T = ((e ⟨t, ht⟩ : projImage (slPi true 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) ∧ T * T = 1 ∧ (T : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro t ht ht2
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp (e ⟨t, ht⟩).2
    have hwd : (w : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      CFSG.Open.StatedAPI.mem_statedSL_iff.mp hw
    have hw2 : w * w ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, hwe]
      have h1 : e ⟨t, ht⟩ * e ⟨t, ht⟩ = 1 := by
        rw [← map_mul, ← map_one e]
        congr 1
        exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ht2, Subgroup.coe_one])
      exact congrArg Subtype.val h1
    obtain ⟨T, hTw, hT2, hTd⟩ := exists_involution_lift hwd hw2
    exact ⟨T, hTw.trans hwe, hT2, hTd⟩
  obtain ⟨T₁, hT₁e, hT₁2, hT₁d⟩ := hlift t₁ ht₁ ht₁2
  obtain ⟨T₂, hT₂e, hT₂2, hT₂d⟩ := hlift t₂ ht₂ ht₂2
  obtain ⟨B, -, hBe⟩ := Subgroup.mem_map.mp (e ⟨b, hb⟩).2
  have hconj_a : ∀ (t : G) (ht : t ∈ L),
      ((e ⟨a * t * a⁻¹, hLn.conj_mem t ht a⟩ : projImage (slPi true 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y *
          ((e ⟨t, ht⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
            (ProjGenLinGroup.mk y)⁻¹ := by
    intro t ht
    have h := hy.2 (e ⟨t, ht⟩)
    rw [coe_slAct_eqP] at h
    simpa using h
  have hconj_b : ∀ (t : G) (ht : t ∈ L),
      ((e ⟨b * t * b⁻¹, hLn.conj_mem t ht b⟩ : projImage (slPi true 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk B *
          ((e ⟨t, ht⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
            (ProjGenLinGroup.mk B)⁻¹ := by
    intro t ht
    have h1 : (⟨b * t * b⁻¹, hLn.conj_mem t ht b⟩ : L) = ⟨b, hb⟩ * ⟨t, ht⟩ * (⟨b, hb⟩ : L)⁻¹ :=
      rfl
    rw [h1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ← hBe]
  have he_eq : ∀ (u v : G) (hu : u ∈ L) (hv : v ∈ L), u = v →
      ((e ⟨u, hu⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((e ⟨v, hv⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
    rintro u v hu hv rfl
    rfl
  have hyT : ∀ (t : G) (ht : t ∈ L) (T : GL (Fin 3) K), ProjGenLinGroup.mk T =
      ((e ⟨t, ht⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) →
      T * T = 1 → (T : Matrix (Fin 3) (Fin 3) K).det = 1 → a * t = t * a → y * T = T * y := by
    intro t ht T hTe hT2 hTd hat
    have h1 : ProjGenLinGroup.mk (y * T * y⁻¹) = ProjGenLinGroup.mk T := by
      rw [map_mul, map_mul, map_inv, hTe, ← hconj_a t ht]
      exact he_eq _ _ _ _ (by rw [hat, mul_inv_cancel_right])
    have h2' := conj_eq_of_mk_eq hT2 hT2 hTd hTd h1
    calc y * T = y * T * y⁻¹ * y := by group
      _ = T * y := by rw [h2']
  have hy₁ := hyT t₁ ht₁ T₁ hT₁e hT₁2 hT₁d ha₁
  have hy₂ := hyT t₂ ht₂ T₂ hT₂e hT₂2 hT₂d ha₂
  have hT12 : T₁ * T₂ = T₂ * T₁ := by
    have h1 : ProjGenLinGroup.mk (T₁ * T₂ * T₁⁻¹) = ProjGenLinGroup.mk T₂ := by
      rw [map_mul, map_mul, map_inv, hT₁e, hT₂e]
      have h3 : e ⟨t₁, ht₁⟩ * e ⟨t₂, ht₂⟩ * (e ⟨t₁, ht₁⟩)⁻¹ = e ⟨t₂, ht₂⟩ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hc12, mul_inv_cancel_right])
      have := congrArg Subtype.val h3
      simpa using this
    have h2' := conj_eq_of_mk_eq hT₂2 hT₂2 hT₂d hT₂d h1
    calc T₁ * T₂ = T₁ * T₂ * T₁⁻¹ * T₁ := by group
      _ = T₂ * T₁ := by rw [h2']
  have hT12sq : T₁ * T₂ * (T₁ * T₂) = 1 := by
    calc T₁ * T₂ * (T₁ * T₂) = T₁ * (T₂ * T₁) * T₂ := by group
      _ = T₁ * (T₁ * T₂) * T₂ := by rw [hT12]
      _ = (T₁ * T₁) * (T₂ * T₂) := by group
      _ = 1 := by rw [hT₁2, hT₂2, mul_one]
  have hT12d : ((T₁ * T₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hT₁d, hT₂d, mul_one]
  have hB₁ : B * T₁ = T₂ * B := by
    have h1 : ProjGenLinGroup.mk (B * T₁ * B⁻¹) = ProjGenLinGroup.mk T₂ := by
      rw [map_mul, map_mul, map_inv, hT₁e, hT₂e, ← hconj_b t₁ ht₁]
      exact he_eq _ _ _ _ hb₁
    have h2' := conj_eq_of_mk_eq hT₁2 hT₂2 hT₁d hT₂d h1
    calc B * T₁ = B * T₁ * B⁻¹ * B := by group
      _ = T₂ * B := by rw [h2']
  have hB₂ : B * T₂ = T₁ * T₂ * B := by
    have h1 : ProjGenLinGroup.mk (B * T₂ * B⁻¹) = ProjGenLinGroup.mk (T₁ * T₂) := by
      rw [map_mul, map_mul, map_inv, hT₂e, ← hconj_b t₂ ht₂, map_mul, hT₁e, hT₂e]
      have h3 : ((e ⟨t₁ * t₂, mul_mem ht₁ ht₂⟩ : projImage (slPi true 3 (p ^ f) K)) :
          ProjGenLinGroup (Fin 3) K) =
          ((e ⟨t₁, ht₁⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) *
            ((e ⟨t₂, ht₂⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
        rw [← Subgroup.coe_mul, ← map_mul]
        rfl
      rw [← h3]
      exact he_eq _ _ _ _ hb₂
    have h2' := conj_eq_of_mk_eq hT₂2 hT12sq hT₂d hT12d h1
    calc B * T₂ = B * T₂ * B⁻¹ * B := by group
      _ = T₁ * T₂ * B := by rw [h2']
  have hyB : y * B * y⁻¹ * B⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars]
    have h1 : ProjGenLinGroup.mk (y * B * y⁻¹) = ProjGenLinGroup.mk B := by
      rw [map_mul, map_mul, map_inv, hBe, ← hconj_a b hb]
      exact he_eq _ _ _ _ (by rw [hab, mul_inv_cancel_right])
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  have hne1 : ∀ (t : G) (ht : t ∈ L) (T : GL (Fin 3) K), ProjGenLinGroup.mk T =
      ((e ⟨t, ht⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) → t ≠ 1 →
      T ≠ 1 := by
    intro t ht T hTe ht1 hT1
    rw [hT1, map_one] at hTe
    apply ht1
    have h1 : e ⟨t, ht⟩ = 1 := Subtype.ext hTe.symm
    have h2'' : (⟨t, ht⟩ : L) = 1 := by rw [← map_eq_one_iff e e.injective]; exact h1
    exact congrArg Subtype.val h2''
  have hT₁1 := hne1 t₁ ht₁ T₁ hT₁e ht₁1
  have hT₂1 := hne1 t₂ ht₂ T₂ hT₂e ht₂1
  have hT₁₂ : T₁ ≠ T₂ := by
    intro h
    apply h12
    have h1 : ((e ⟨t₁, ht₁⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ((e ⟨t₂, ht₂⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) := by
      rw [← hT₁e, ← hT₂e, h]
    have h2'' := e.injective (Subtype.ext h1)
    exact congrArg Subtype.val h2''
  have hyZ := not_mem_zPi_of_isPGLAtP hK hq haC hy
  have hy3 := pow_three_mem_zPiP hK hq ha3 hy
  rcases type123_exhaust hK hq hy.1 hyZ hy3 with h1 | h2' | h3
  · exact hnin (exists_inner_of_type1 hK hq hy.1 h1)
  · exact false_of_type2_comm hK hq h2 h2' hT₁2 hT₂2 hT₁d hT₂d hT₁1 hT₂1 hT₁₂ hy₁ hy₂ hyB hB₁ hB₂
  · exact false_of_type3_comm h2 h3 hT₁2 hT₁d hT₁1 hy₁

end Fix

end CFSG.RankThree.PartTwo.Sec14.Ronan1411L37
