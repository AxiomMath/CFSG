module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

variable {F : Type} [Field F]

@[expose] def burnsideA315y_qa (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F :=
  !![0, -1; 1, 0]

@[expose] def burnsideA315y_qb (x y : F) : Matrix (Fin 2) (Fin 2) F :=
  !![x, y; y, -x]

theorem burnsideA315y_commutant (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ≠ 0 ∨ y ≠ 0)
    (hc : c ≠ 0) {M : Matrix (Fin 3) (Fin 3) F}
    (hz : M * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * M)
    (ha : M * blkMat (burnsideA315y_qa F) 1 = blkMat (burnsideA315y_qa F) 1 * M)
    (hb : M * blkMat (c • burnsideA315y_qb x y) 1 = blkMat (c • burnsideA315y_qb x y) 1 * M) :
    M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = M 0 0 ∧ M 0 2 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧
      M 2 1 = 0 := by
  obtain ⟨h02, h12, h20, h21⟩ := block_eq_zero_of_commute_negDiag h2 hz
  have a00 := congrFun (congrFun ha 0) 0
  have a01 := congrFun (congrFun ha 0) 1
  have b00 := congrFun (congrFun hb 0) 0
  have b01 := congrFun (congrFun hb 0) 1
  simp [blkMat, burnsideA315y_qa, burnsideA315y_qb, Matrix.mul_apply, Fin.sum_univ_three,
    h02, h12, h20, h21] at a00 a01 b00 b01
  have e1 : M 1 1 = M 0 0 := by linear_combination -a01
  have e2 : M 1 0 = -M 0 1 := by linear_combination a00
  have hv1 : c * (2 * (M 0 1 * y)) = 0 := by linear_combination b00 + c * y * e2
  have hv2 : c * (2 * (M 0 1 * x)) = 0 := by linear_combination -b01 - c * y * e1
  have hv1' : M 0 1 * y = 0 := by
    have := (mul_eq_zero.mp hv1).resolve_left hc
    exact (mul_eq_zero.mp this).resolve_left h2
  have hv2' : M 0 1 * x = 0 := by
    have := (mul_eq_zero.mp hv2).resolve_left hc
    exact (mul_eq_zero.mp this).resolve_left h2
  have hM01 : M 0 1 = 0 := by
    rcases hxy with hx | hy
    · exact (mul_eq_zero.mp hv2').resolve_right hx
    · exact (mul_eq_zero.mp hv1').resolve_right hy
  refine ⟨hM01, ?_, e1, h02, h12, h20, h21⟩
  rw [e2, hM01, neg_zero]

@[expose] def burnsideA315y_W (F : Type) [Field F] : Submodule F (Fin 3 → F) :=
  LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2)

@[expose] def burnsideA315y_l (F : Type) [Field F] : Submodule F (Fin 3 → F) :=
  LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 0) ⊓
    LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 1)

theorem burnsideA315y_mem_W {v : Fin 3 → F} : v ∈ burnsideA315y_W F ↔ v 2 = 0 := by
  simp [burnsideA315y_W]

theorem burnsideA315y_mem_l {v : Fin 3 → F} : v ∈ burnsideA315y_l F ↔ v 0 = 0 ∧ v 1 = 0 := by
  simp [burnsideA315y_l]

theorem burnsideA315y_W_le {X : Submodule F (Fin 3 → F)} {w t : Fin 3 → F} (hw : w ∈ X)
    (ht : t ∈ X) (hw2 : w 2 = 0) (ht2 : t 2 = 0) (hD : w 0 * t 1 - w 1 * t 0 ≠ 0) :
    burnsideA315y_W F ≤ X := by
  intro v hv
  rw [burnsideA315y_mem_W] at hv
  set D := w 0 * t 1 - w 1 * t 0 with hDdef
  have hcomb : v = ((v 0 * t 1 - v 1 * t 0) / D) • w + ((w 0 * v 1 - w 1 * v 0) / D) • t := by
    funext i
    fin_cases i
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one]
      field_simp
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
      rw [hv, hw2, ht2]
      ring
  rw [hcomb]
  exact X.add_mem (X.smul_mem _ hw) (X.smul_mem _ ht)

theorem burnsideA315y_invariant (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) (X : Submodule F (Fin 3 → F))
    (hz : ∀ v ∈ X, (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ X)
    (ha : ∀ v ∈ X, blkMat (burnsideA315y_qa F) 1 *ᵥ v ∈ X)
    (hb : ∀ v ∈ X, blkMat (c • burnsideA315y_qb x y) 1 *ᵥ v ∈ X) :
    X = ⊥ ∨ X = burnsideA315y_l F ∨ X = burnsideA315y_W F ∨ X = ⊤ := by
  have hsplitW : ∀ v ∈ X, ![v 0, v 1, 0] ∈ X := by
    intro v hv
    have h := X.sub_mem hv (hz v hv)
    have h' := X.smul_mem (2⁻¹ : F) h
    convert h' using 1
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal] <;>
      field_simp <;> ring
  have hsplitl : ∀ v ∈ X, ![0, 0, v 2] ∈ X := by
    intro v hv
    have h := X.add_mem hv (hz v hv)
    have h' := X.smul_mem (2⁻¹ : F) h
    convert h' using 1
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal] <;>
      field_simp <;> ring
  have hW : ∀ w : Fin 3 → F, w ∈ X → w 2 = 0 → (w 0 ≠ 0 ∨ w 1 ≠ 0) →
      burnsideA315y_W F ≤ X := by
    intro w hw hw2 hne
    have haw := ha w hw
    have hbw := hb w hw
    by_cases hn : w 0 ^ 2 + w 1 ^ 2 = 0
    · refine burnsideA315y_W_le hw hbw hw2 ?_ ?_
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blkMat, hw2]
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blkMat, burnsideA315y_qb,
          Matrix.smul_apply, smul_eq_mul]
        simp [hw2]
        intro hD
        have hw0 : w 0 ≠ 0 := by
          intro h0
          rw [h0] at hn
          have : w 1 ^ 2 = 0 := by linear_combination hn
          rcases hne with h | h
          · exact h h0
          · exact h (pow_eq_zero_iff (by norm_num) |>.mp this)
        have h3 : c * (2 * w 0 * (y * w 0 - x * w 1)) = 0 := by
          linear_combination hD + c * y * hn
        have h4 : y * w 0 - x * w 1 = 0 := by
          have := (mul_eq_zero.mp h3).resolve_left hc
          have h22 : (2 : F) * w 0 ≠ 0 := mul_ne_zero h2 hw0
          rw [mul_assoc] at this
          exact (mul_eq_zero.mp (by simpa [mul_assoc] using this)).resolve_left h22
        apply hxy
        have h5 : (x ^ 2 + y ^ 2) * w 0 ^ 2 = 0 := by
          linear_combination (y * w 0 + x * w 1) * h4 + x ^ 2 * hn
        exact (mul_eq_zero.mp h5).resolve_right (pow_ne_zero 2 hw0)
    · refine burnsideA315y_W_le hw haw hw2 ?_ ?_
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blkMat, hw2]
      · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, blkMat, burnsideA315y_qa]
        simp [hw2]
        intro hD
        apply hn
        linear_combination hD
  have hl : ∀ v ∈ X, v 2 ≠ 0 → burnsideA315y_l F ≤ X := by
    intro v hv hv2
    have h := X.smul_mem (v 2)⁻¹ (hsplitl v hv)
    intro u hu
    rw [burnsideA315y_mem_l] at hu
    have hu' : u = u 2 • ((v 2)⁻¹ • ![0, 0, v 2]) := by
      funext i
      fin_cases i
      · simp [hu.1]
      · simp [hu.2]
      · simp [hv2]
    rw [hu']
    exact X.smul_mem _ h
  by_cases hX2 : ∃ v ∈ X, v 2 ≠ 0
  · obtain ⟨v, hv, hv2⟩ := hX2
    have hlX := hl v hv hv2
    by_cases hXW : ∃ v ∈ X, v 0 ≠ 0 ∨ v 1 ≠ 0
    · obtain ⟨u, hu, hu01⟩ := hXW
      have hWX := hW _ (hsplitW u hu) (by simp) (by simpa using hu01)
      right; right; right
      rw [eq_top_iff]
      intro w _
      have hw : w = ![w 0, w 1, 0] + ![0, 0, w 2] := by
        funext i
        fin_cases i <;> simp
      rw [hw]
      exact X.add_mem (hWX (by simp [burnsideA315y_mem_W])) (hlX (by simp [burnsideA315y_mem_l]))
    · push Not at hXW
      right; left
      refine le_antisymm (fun u hu => ?_) hlX
      rw [burnsideA315y_mem_l]
      exact hXW u hu
  · push Not at hX2
    by_cases hXW : ∃ v ∈ X, v 0 ≠ 0 ∨ v 1 ≠ 0
    · obtain ⟨u, hu, hu01⟩ := hXW
      have hWX := hW _ (hsplitW u hu) (by simp) (by simpa using hu01)
      right; right; left
      refine le_antisymm (fun w hw => ?_) hWX
      rw [burnsideA315y_mem_W]
      exact hX2 w hw
    · push Not at hXW
      left
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_bot]
      funext i
      fin_cases i
      · exact (hXW u hu).1
      · exact (hXW u hu).2
      · exact hX2 u hu

theorem burnsideA315y_scalar_eq_one_of_trace {g h : GL (Fin 3) F} {μ : Fˣ}
    (hgh : g * h * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * h)
    (htr : trace (h : Matrix (Fin 3) (Fin 3) F) ≠ 0) : μ = 1 := by
  have h1 := congrArg (fun k : GL (Fin 3) F => trace (k : Matrix (Fin 3) (Fin 3) F)) hgh
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h1
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul] at h1
  have h2 : ((μ : F) - 1) * trace (h : Matrix (Fin 3) (Fin 3) F) = 0 := by
    linear_combination -h1
  have h3 : (μ : F) = 1 := by
    have := (mul_eq_zero.mp h2).resolve_right htr
    linear_combination this
  exact Units.ext h3

theorem burnsideA315y_scalar_comm (μ : Fˣ) (g : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) μ * g = g * Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨μ, rfl⟩
  exact (Subgroup.mem_center_iff.mp hz g).symm

theorem burnsideA315y_scalar_eq_one_of_pow {g h : GL (Fin 3) F} {μ ν : Fˣ} {m : ℕ}
    (hgh : g * h * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * h)
    (hm : h ^ m = Matrix.GeneralLinearGroup.scalar (Fin 3) ν) (hm3 : Nat.Coprime m 3) :
    μ = 1 := by
  have hdet := congrArg Matrix.GeneralLinearGroup.det hgh
  simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hμ3 : μ ^ 3 = 1 := by
    have : Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det h *
        (Matrix.GeneralLinearGroup.det g)⁻¹ = Matrix.GeneralLinearGroup.det h := by
      rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this] at hdet
    have h2 := congrArg (· * (Matrix.GeneralLinearGroup.det h)⁻¹) hdet
    simp only [mul_inv_cancel, mul_assoc, mul_one] at h2
    exact h2.symm
  have hpow := congrArg (· ^ m) hgh
  simp only [conj_pow, hm] at hpow
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) μ) h :=
    burnsideA315y_scalar_comm μ h
  rw [hcomm.mul_pow, hm] at hpow
  have hsc : g * Matrix.GeneralLinearGroup.scalar (Fin 3) ν * g⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
    rw [← burnsideA315y_scalar_comm ν g, mul_inv_cancel_right]
  rw [hsc, ← map_pow] at hpow
  have hμm : μ ^ m = 1 := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 3) (μ ^ m) = 1 := by
      have h3 := congrArg (· * (Matrix.GeneralLinearGroup.scalar (Fin 3) ν)⁻¹) hpow
      simp only [mul_inv_cancel, mul_assoc, mul_one] at h3
      exact h3.symm
    have h2 := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F) 0 0) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  have hd : orderOf μ ∣ Nat.gcd m 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hμm)
    (orderOf_dvd_of_pow_eq_one hμ3)
  rw [hm3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

@[expose] def burnsideA315y_IsUW (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  g 0 0 = 1 ∧ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = 1 ∧ g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 2 2 = 1

@[expose] def burnsideA315y_IsUl (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  g 0 0 = 1 ∧ g 0 1 = 0 ∧ g 0 2 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = 1 ∧ g 1 2 = 0 ∧ g 2 2 = 1

@[expose] def burnsideA315y_fixSp (E : Set (GL (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ e ∈ E, (e : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := by
    intro v w hv hw e he
    rw [Matrix.mulVec_add, hv e he, hw e he]
  zero_mem' := by
    intro e _
    rw [Matrix.mulVec_zero]
  smul_mem' := by
    intro c v hv e he
    rw [Matrix.mulVec_smul, hv e he]

theorem burnsideA315y_mem_fixSp {E : Set (GL (Fin 3) F)} {v : Fin 3 → F} :
    v ∈ burnsideA315y_fixSp E ↔ ∀ e ∈ E, (e : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
  Iff.rfl

theorem burnsideA315y_ulBlock_pow {g : Matrix (Fin 3) (Fin 3) F} (hg : g 0 2 = 0 ∧ g 1 2 = 0)
    (k : ℕ) : ulBlock (g ^ k) = ulBlock g ^ k := by
  induction k with
  | zero => simp [ulBlock_one]
  | succ k ih => rw [pow_succ', ulBlock_mul hg, ih, pow_succ']

theorem burnsideA315y_isUl_of_fix (h2 : (2 : F) ≠ 0) {e : GL (Fin 3) F}
    (hinv : negDiag3 F * e * negDiag3 F = e⁻¹) (hodd : Odd (orderOf e))
    (h02 : (e : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (h12 : (e : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h22 : (e : Matrix (Fin 3) (Fin 3) F) 2 2 = 1) :
    burnsideA315y_IsUl (e : Matrix (Fin 3) (Fin 3) F) := by
  set M := (e : Matrix (Fin 3) (Fin 3) F) with hM
  have hsq : (e * negDiag3 F) * (e * negDiag3 F) = 1 := by
    have : negDiag3 F * e * negDiag3 F * e = 1 := by rw [hinv, inv_mul_cancel]
    calc (e * negDiag3 F) * (e * negDiag3 F) = e * (negDiag3 F * e * negDiag3 F * e) *
          e⁻¹ := by group
      _ = 1 := by rw [this, mul_one, mul_inv_cancel]
  have hsqM := congrArg (fun k : GL (Fin 3) F => ulBlock (k : Matrix (Fin 3) (Fin 3) F)) hsq
  rw [Units.val_mul (e * negDiag3 F) (e * negDiag3 F), Units.val_one, ulBlock_one] at hsqM
  have hzc : ((e * negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      ((e * negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    simp [coe_negDiag3, Matrix.mul_apply, Fin.sum_univ_three, ← hM, h02, h12]
  have hA : ulBlock ((e * negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = -ulBlock M := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ulBlock, coe_negDiag3, Matrix.mul_apply, Fin.sum_univ_three, ← hM]
  rw [ulBlock_mul hzc, hA, neg_mul_neg] at hsqM
  set m := orderOf e with hm
  obtain ⟨k, hk⟩ := hodd
  have hpow : ulBlock M ^ m = 1 := by
    rw [← burnsideA315y_ulBlock_pow ⟨h02, h12⟩, hM, ← Units.val_pow_eq_pow_val,
      pow_orderOf_eq_one, Units.val_one, ulBlock_one]
  have hα : ulBlock M = 1 := by
    have h1 : ulBlock M ^ m = ulBlock M := by
      rw [hk, pow_succ, pow_mul, sq, hsqM, one_pow, one_mul]
    rw [← h1, hpow]
  have e00 := congrFun (congrFun hα 0) 0
  have e01 := congrFun (congrFun hα 0) 1
  have e10 := congrFun (congrFun hα 1) 0
  have e11 := congrFun (congrFun hα 1) 1
  simp [ulBlock] at e00 e01 e10 e11
  exact ⟨e00, e01, h02, e10, e11, h12, h22⟩

theorem burnsideA315y_isUW_of_fix {e : Matrix (Fin 3) (Fin 3) F} (hdet : e.det = 1)
    (h1 : e *ᵥ ![1, 0, 0] = ![1, 0, 0]) (h2 : e *ᵥ ![0, 1, 0] = ![0, 1, 0]) :
    burnsideA315y_IsUW e := by
  have a0 := congrFun h1 0
  have a1 := congrFun h1 1
  have a2 := congrFun h1 2
  have b0 := congrFun h2 0
  have b1 := congrFun h2 1
  have b2 := congrFun h2 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a0 a1 a2 b0 b1 b2
  refine ⟨a0, b0, a1, b1, a2, b2, ?_⟩
  rw [Matrix.det_fin_three, a0, b0, a1, b1, a2, b2] at hdet
  simpa using hdet

theorem burnsideA315y_fix_of_mem_W {e : GL (Fin 3) F}
    (hinv : negDiag3 F * e * negDiag3 F = e⁻¹) (hodd : Odd (orderOf e)) {w : Fin 3 → F}
    (hw : w 2 = 0) (hew : ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 2 = 0) :
    (e : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
  have hzW : ∀ u : Fin 3 → F, u 2 = 0 →
      (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) F) *ᵥ u = -u := by
    intro u hu
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal, hu]
  have hinvw : ((e⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
      (e : Matrix (Fin 3) (Fin 3) F) *ᵥ w := by
    rw [← hinv]
    simp only [Units.val_mul, coe_negDiag3, ← Matrix.mulVec_mulVec]
    rw [hzW w hw, Matrix.mulVec_neg, Matrix.mulVec_neg, hzW _ hew, neg_neg]
  have hsq : ((e ^ 2 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    have : (e : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((e⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hinvw, Matrix.mulVec_mulVec] at this
    rw [sq, Units.val_mul]
    exact this
  have hsqj : ∀ j : ℕ, ((e ^ (2 * j) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [mul_add, mul_one, pow_add, Units.val_mul, ← Matrix.mulVec_mulVec, hsq, ih]
  obtain ⟨k, hk⟩ := hodd
  have h1 := hsqj k
  have h2 : ((e ^ orderOf e : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    rw [pow_orderOf_eq_one, Units.val_one, Matrix.one_mulVec]
  rw [hk, pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, h1] at h2
  exact h2

theorem burnsideA315y_finrank_W : Module.finrank F (burnsideA315y_W F) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2)
  have hr : LinearMap.range (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    exact ⟨fun _ => a, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  change Module.finrank F (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin 3 => F) 2)) = 2
  omega

theorem burnsideA315y_det_negDiag3 : ((negDiag3 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  rw [coe_negDiag3, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem burnsideA315y_exists_fix_W [Finite F] (h2 : (2 : F) ≠ 0) {e : GL (Fin 3) F}
    (hinv : negDiag3 F * e * negDiag3 F = e⁻¹)
    (hdet : (e : Matrix (Fin 3) (Fin 3) F).det = 1) (hne : e ≠ negDiag3 F) :
    ∃ w : Fin 3 → F, w ≠ 0 ∧ w 2 = 0 ∧ (e : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
  classical
  have hz2 : negDiag3 F * negDiag3 F = (1 : GL (Fin 3) F) := by
    apply Units.ext
    rw [Units.val_mul, coe_negDiag3, Matrix.diagonal_mul_diagonal, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  set t : GL (Fin 3) F := negDiag3 F * e with ht
  have htt : t * t = 1 := by
    rw [ht]
    calc negDiag3 F * e * (negDiag3 F * e) = (negDiag3 F * e * negDiag3 F) * e := by group
      _ = 1 := by rw [hinv, inv_mul_cancel]
  set f : Module.End F (Fin 3 → F) := Matrix.toLin' (t : Matrix (Fin 3) (Fin 3) F) with hf
  have hinvol : Function.Involutive f := by
    intro v
    rw [hf, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, htt,
      Units.val_one, Matrix.one_mulVec]
  have hdetf : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_toLin', ht, Units.val_mul, Matrix.det_mul, burnsideA315y_det_negDiag3,
      hdet, mul_one]
  have hfne : f ≠ LinearMap.id := by
    intro h
    apply hne
    have h1 : (t : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.toLin'_one] at h
      exact Matrix.toLin'.injective (by rw [← hf, h])
    have h2 : t = 1 := Units.ext h1
    rw [ht] at h2
    calc e = negDiag3 F * (negDiag3 F * e) := by rw [← mul_assoc, hz2, one_mul]
      _ = negDiag3 F := by rw [h2, mul_one]
  obtain ⟨hm, -⟩ := CFSG.Wreathed.OddLinearThreeCentralizerCore.involution_finrank_three h2 f
    hinvol (by simp) hdetf hfne
  set Y := CFSG.Wreathed.OddLinearThreeCentralizerCore.minusSpace f with hY
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (burnsideA315y_W F) Y
  have hle : Module.finrank F ↥(burnsideA315y_W F ⊔ Y) ≤ 3 := by
    have := Submodule.finrank_le (burnsideA315y_W F ⊔ Y)
    simpa using this
  rw [burnsideA315y_finrank_W, hm] at hsum
  have hpos : 0 < Module.finrank F ↥(burnsideA315y_W F ⊓ Y) := by omega
  have hne' : burnsideA315y_W F ⊓ Y ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  obtain ⟨hwW, hwY⟩ := Submodule.mem_inf.mp hwmem
  rw [burnsideA315y_mem_W] at hwW
  have hfw : f w = -w := by
    have := Module.End.mem_eigenspace_iff.mp hwY
    rw [this, neg_one_smul]
  rw [hf, Matrix.toLin'_apply, ht, Units.val_mul, ← Matrix.mulVec_mulVec] at hfw
  refine ⟨w, hw0, hwW, ?_⟩
  have hzw : (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ ((e : Matrix (Fin 3) (Fin 3) F) *ᵥ w)) =
      (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ (-w) := by rw [hfw]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, hz2, Units.val_one, Matrix.one_mulVec] at hzw
  rw [hzw, Matrix.mulVec_neg, coe_negDiag3]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal, hwW]

theorem burnsideA315y_not_commute_Ul_UW {M N : Matrix (Fin 3) (Fin 3) F}
    (hM : burnsideA315y_IsUl M) (hN : burnsideA315y_IsUW N) (hMW : ¬ burnsideA315y_IsUW M)
    (hNl : ¬ burnsideA315y_IsUl N) : M * N ≠ N * M := by
  intro hc
  obtain ⟨m00, m01, m02, m10, m11, m12, m22⟩ := hM
  obtain ⟨n00, n01, n10, n11, n20, n21, n22⟩ := hN
  have c00 := congrFun (congrFun hc 0) 0
  have c01 := congrFun (congrFun hc 0) 1
  have c10 := congrFun (congrFun hc 1) 0
  have c11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, m00, m01, m02, m10, m11, m12, m22, n00, n01, n10,
    n11, n20, n21, n22] at c00 c01 c10 c11
  have hab : M 2 0 ≠ 0 ∨ M 2 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hMW ⟨m00, m01, m10, m11, h.1, h.2, m22⟩
  have hcd : N 0 2 ≠ 0 ∨ N 1 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hNl ⟨n00, n01, h.1, n10, n11, h.2, n22⟩
  rcases hab with ha | hb <;> rcases hcd with hc' | hd
  · exact ha (c00.resolve_left hc')
  · exact ha (c10.resolve_left hd)
  · exact hb (c01.resolve_left hc')
  · exact hb (c11.resolve_left hd)

theorem burnsideA315y_E1 [Finite F] (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) {Da Db : GL (Fin 3) F}
    (hDa : (Da : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (hDb : (Db : Matrix (Fin 3) (Fin 3) F) = blkMat (c • burnsideA315y_qb x y) 1)
    (E : Subgroup (GL (Fin 3) F)) (hdet : ∀ e ∈ E, (e : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hab : ∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ * e₂ = e₂ * e₁)
    (hinv : ∀ e ∈ E, negDiag3 F * e * negDiag3 F = e⁻¹) (hodd : ∀ e ∈ E, Odd (orderOf e))
    (hDaE : ∀ e ∈ E, Da⁻¹ * e * Da ∈ E) (hDbE : ∀ e ∈ E, Db⁻¹ * e * Db ∈ E) :
    (∀ e ∈ E, burnsideA315y_IsUW (e : Matrix (Fin 3) (Fin 3) F)) ∨
      (∀ e ∈ E, burnsideA315y_IsUl (e : Matrix (Fin 3) (Fin 3) F)) := by
  classical
  have hz2 : negDiag3 F * negDiag3 F = (1 : GL (Fin 3) F) := by
    apply Units.ext
    rw [Units.val_mul, coe_negDiag3, Matrix.diagonal_mul_diagonal, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hzinv : (negDiag3 F)⁻¹ = negDiag3 F := inv_eq_of_mul_eq_one_right hz2
  have hcase : ∀ e ∈ E, burnsideA315y_IsUW (e : Matrix (Fin 3) (Fin 3) F) ∨
      burnsideA315y_IsUl (e : Matrix (Fin 3) (Fin 3) F) := by
    intro e₀ he₀
    by_contra hcon
    push Not at hcon
    obtain ⟨hnW, hnl⟩ := hcon
    set Y := burnsideA315y_fixSp ({e₀} : Set (GL (Fin 3) F)) with hY
    have hmemY : ∀ v, v ∈ Y ↔ (e₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
      intro v
      rw [hY, burnsideA315y_mem_fixSp]
      simp
    have hYW : ∀ v ∈ Y, v 2 = 0 := by
      intro v hv
      by_contra hv2
      have hzv : (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Y := by
        rw [hmemY]
        have h1 : (e₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ ((negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
            = (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ
              (((e₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
          rw [← hinv e₀ he₀, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
            ← Units.val_mul]
          congr 2
          calc e₀ * negDiag3 F = negDiag3 F * negDiag3 F * e₀ * negDiag3 F := by
                rw [hz2, one_mul]
            _ = negDiag3 F * (negDiag3 F * e₀ * negDiag3 F) := by group
        have h2 : ((e₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
          have hv' := (hmemY v).mp hv
          calc ((e₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
              ((e₀⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
                ((e₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by rw [hv']
            _ = v := by rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
                Units.val_one, Matrix.one_mulVec]
        rw [h1, h2]
      have hu : ![0, 0, v 2] ∈ Y := by
        have h := Y.smul_mem (2⁻¹ : F) (Y.add_mem hv hzv)
        convert h using 1
        funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal,
          coe_negDiag3] <;> field_simp <;> ring
      have he3 := (hmemY _).mp hu
      have c0 := congrFun he3 0
      have c1 := congrFun he3 1
      have c2 := congrFun he3 2
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at c0 c1 c2
      have h02 : (e₀ : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
        rcases c0 with h | h
        · exact h
        · exact absurd h hv2
      have h12 : (e₀ : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
        rcases c1 with h | h
        · exact h
        · exact absurd h hv2
      have h22 : (e₀ : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
        have : ((e₀ : Matrix (Fin 3) (Fin 3) F) 2 2 - 1) * v 2 = 0 := by linear_combination c2
        have := (mul_eq_zero.mp this).resolve_right hv2
        linear_combination this
      exact hnl (burnsideA315y_isUl_of_fix h2 (hinv e₀ he₀) (hodd e₀ he₀) h02 h12 h22)
    have hfixE : burnsideA315y_fixSp (E : Set (GL (Fin 3) F)) = Y := by
      apply le_antisymm
      · intro v hv
        rw [hmemY]
        exact (burnsideA315y_mem_fixSp.mp hv) e₀ he₀
      · intro v hv
        rw [burnsideA315y_mem_fixSp]
        intro e he
        have hev : (e : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Y := by
          rw [hmemY, Matrix.mulVec_mulVec, ← Units.val_mul, ← hab e he e₀ he₀, Units.val_mul,
            ← Matrix.mulVec_mulVec, (hmemY v).mp hv]
        exact burnsideA315y_fix_of_mem_W (hinv e he) (hodd e he) (hYW v hv) (hYW _ hev)
    have hinvar : ∀ D : GL (Fin 3) F, (∀ e ∈ E, D⁻¹ * e * D ∈ E) →
        ∀ v ∈ burnsideA315y_fixSp (E : Set (GL (Fin 3) F)),
          (D : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ burnsideA315y_fixSp (E : Set (GL (Fin 3) F)) := by
      intro D hD v hv
      rw [burnsideA315y_mem_fixSp]
      intro e he
      have h1 := (burnsideA315y_mem_fixSp.mp hv) _ (hD e he)
      have h2 : (e : Matrix (Fin 3) (Fin 3) F) * (D : Matrix (Fin 3) (Fin 3) F) =
          (D : Matrix (Fin 3) (Fin 3) F) * ((D⁻¹ * e * D : GL (Fin 3) F) : Matrix _ _ F) := by
        rw [← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      rw [Matrix.mulVec_mulVec, h2, ← Matrix.mulVec_mulVec, h1]
    have hzE : ∀ e ∈ E, (negDiag3 F)⁻¹ * e * negDiag3 F ∈ E := by
      intro e he
      rw [hzinv, hinv e he]
      exact E.inv_mem he
    have hcls := burnsideA315y_invariant h2 hxy hc
      (burnsideA315y_fixSp (E : Set (GL (Fin 3) F)))
      (fun v hv => by simpa [coe_negDiag3] using hinvar _ hzE v hv)
      (fun v hv => by simpa [hDa] using hinvar _ hDaE v hv)
      (fun v hv => by simpa [hDb] using hinvar _ hDbE v hv)
    rw [hfixE] at hcls
    have he₀z : e₀ ≠ negDiag3 F := by
      intro h
      have h1 := hodd e₀ he₀
      have h2' : orderOf e₀ = 2 := by
        rw [h]
        apply orderOf_eq_prime
        · rw [sq, hz2]
        · intro h1'
          have := congrArg (fun k : GL (Fin 3) F => (k : Matrix (Fin 3) (Fin 3) F) 0 0) h1'
          simp [coe_negDiag3] at this
          apply h2
          linear_combination -this
      rw [h2'] at h1
      exact absurd h1 (by decide)
    obtain ⟨w, hw0, hw2, hew⟩ := burnsideA315y_exists_fix_W h2 (hinv e₀ he₀) (hdet e₀ he₀) he₀z
    have hwY : w ∈ Y := (hmemY w).mpr hew
    rcases hcls with hbot | hl | hW | htop
    · rw [hbot, Submodule.mem_bot] at hwY
      exact hw0 hwY
    · have : ![0, 0, 1] ∈ Y := by
        rw [hl, burnsideA315y_mem_l]
        simp
      have := hYW _ this
      simp at this
    · have h1 : ![1, 0, 0] ∈ Y := by
        rw [hW, burnsideA315y_mem_W]
        simp
      have h2' : ![0, 1, 0] ∈ Y := by
        rw [hW, burnsideA315y_mem_W]
        simp
      exact hnW (burnsideA315y_isUW_of_fix (hdet e₀ he₀) ((hmemY _).mp h1) ((hmemY _).mp h2'))
    · have : ![0, 0, 1] ∈ Y := by
        rw [htop]
        trivial
      have := hYW _ this
      simp at this
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨e₁, he₁, h₁⟩, ⟨e₂, he₂, h₂⟩⟩ := hcon
  have h₁l := (hcase e₁ he₁).resolve_left h₁
  have h₂W := (hcase e₂ he₂).resolve_right h₂
  apply burnsideA315y_not_commute_Ul_UW h₁l h₂W h₁ h₂
  rw [← Units.val_mul, ← Units.val_mul, hab e₁ he₁ e₂ he₂]

theorem burnsideA315y_negDiag3_sq : negDiag3 F * negDiag3 F = (1 : GL (Fin 3) F) := by
  apply Units.ext
  rw [Units.val_mul, coe_negDiag3, Matrix.diagonal_mul_diagonal, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem burnsideA315y_mulVec_e3 (h2 : (2 : F) ≠ 0) {g : GL (Fin 3) F}
    (hg : g * negDiag3 F = negDiag3 F * g) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 • ![0, 0, 1] := by
  have hgm : (g : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, hg, Units.val_mul]
  obtain ⟨h02, h12, -, -⟩ := block_eq_zero_of_commute_negDiag h2 hgm
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h02, h12]

theorem burnsideA315y_frame (h2 : (2 : F) ≠ 0) {a b t : GL (Fin 3) F}
    (hat : a * negDiag3 F = negDiag3 F * a) (ht : t = b * negDiag3 F * b⁻¹)
    (hta : a * t = t * a) (hab : a * b = b * a) (htz : t * negDiag3 F = negDiag3 F * t)
    (ht1 : t ≠ negDiag3 F) (hbt : b * t * b⁻¹ = negDiag3 F * t) :
    (a : Matrix (Fin 3) (Fin 3) F) = (a : Matrix (Fin 3) (Fin 3) F) 2 2 • 1 := by
  set w := (a : Matrix (Fin 3) (Fin 3) F) 2 2 with hw
  have hz2 := burnsideA315y_negDiag3_sq (F := F)
  have htt : t * t = 1 := by
    rw [ht]
    calc b * negDiag3 F * b⁻¹ * (b * negDiag3 F * b⁻¹) = b * (negDiag3 F * negDiag3 F) * b⁻¹ := by
          group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  have hae3 := burnsideA315y_mulVec_e3 h2 hat
  have hal : ∀ u : Fin 3 → F, u 0 = 0 → u 1 = 0 → (a : Matrix (Fin 3) (Fin 3) F) *ᵥ u = w • u := by
    intro u hu0 hu1
    have hu : u = u 2 • ![0, 0, 1] := by
      funext i
      fin_cases i <;> simp [hu0, hu1]
    rw [hu, Matrix.mulVec_smul, hae3, smul_comm]
  have hfixz : ∀ u : Fin 3 → F, (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u →
      u 0 = 0 ∧ u 1 = 0 := by
    intro u hu
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    simp [coe_negDiag3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal] at h0 h1
    constructor
    · have : (2 : F) * u 0 = 0 := by linear_combination -h0
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : F) * u 1 = 0 := by linear_combination -h1
      exact (mul_eq_zero.mp this).resolve_left h2
  have hat1 : ∀ v : Fin 3 → F, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v →
      (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w • v := by
    intro v hv
    set u := ((b⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hu
    have hvu : v = (b : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hzu : (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
      have h1 : ((b⁻¹ * t * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = negDiag3 F := by
        rw [ht]
        congr 1
        group
      rw [← h1, hu, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Units.val_mul b, mul_inv_cancel, Units.val_one, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hv]
    obtain ⟨hu0, hu1⟩ := hfixz u hzu
    rw [hvu, Matrix.mulVec_mulVec, ← Units.val_mul, hab, Units.val_mul, ← Matrix.mulVec_mulVec,
      hal u hu0 hu1, Matrix.mulVec_smul]
  have hazt : ∀ v : Fin 3 → F, ((negDiag3 F * t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v →
      (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w • v := by
    intro v hv
    set u := ((b⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v with hu
    have hvu : v = (b : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have htu : (t : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
      have h1 : ((b⁻¹ * (negDiag3 F * t) * b : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = t := by
        rw [← hbt]
        congr 1
        group
      rw [← h1, hu, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ← Units.val_mul b, mul_inv_cancel, Units.val_one, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, hv]
    rw [hvu, Matrix.mulVec_mulVec, ← Units.val_mul, hab, Units.val_mul, ← Matrix.mulVec_mulVec,
      hat1 u htu, Matrix.mulVec_smul]
  have htm : (t : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * (t : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, htz, Units.val_mul]
  obtain ⟨t02, t12, t20, t21⟩ := block_eq_zero_of_commute_negDiag h2 htm
  have haW : ∀ v : Fin 3 → F, v 2 = 0 → (a : Matrix (Fin 3) (Fin 3) F) *ᵥ v = w • v := by
    intro v hv2
    set tv := (t : Matrix (Fin 3) (Fin 3) F) *ᵥ v with htv
    have htv2 : tv 2 = 0 := by
      simp [htv, Matrix.mulVec, dotProduct, Fin.sum_univ_three, t20, t21, hv2]
    have httv : (t : Matrix (Fin 3) (Fin 3) F) *ᵥ tv = v := by
      rw [htv, Matrix.mulVec_mulVec, ← Units.val_mul, htt, Units.val_one, Matrix.one_mulVec]
    set vp := (2⁻¹ : F) • (v + tv) with hvp
    set vm := (2⁻¹ : F) • (v - tv) with hvm
    have hsplit : v = vp + vm := by
      rw [hvp, hvm, ← smul_add]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    have hvp1 : (t : Matrix (Fin 3) (Fin 3) F) *ᵥ vp = vp := by
      rw [hvp, Matrix.mulVec_smul, Matrix.mulVec_add, httv, add_comm]
    have hvm1 : ((negDiag3 F * t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ vm = vm := by
      rw [hvm, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_sub, httv, ← htv, coe_negDiag3]
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal, hv2,
        htv2] <;> ring
    rw [hsplit, Matrix.mulVec_add, hat1 vp hvp1, hazt vm hvm1, smul_add]
  have c0 : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = w • Pi.single 0 1 :=
    haW _ (by simp)
  have c1 : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 = w • Pi.single 1 1 :=
    haW _ (by simp)
  have c2 : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 = w • Pi.single 2 1 := by
    have : (Pi.single (2 : Fin 3) (1 : F) : Fin 3 → F) = ![0, 0, 1] := by
      funext i
      fin_cases i <;> simp
    rw [this]
    exact hal _ (by simp) (by simp)
  ext i j
  have hcol : (a : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 = w • Pi.single j 1 := by
    fin_cases j
    · exact c0
    · exact c1
    · exact c2
  have := congrFun hcol i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

@[expose] def burnsideA315y_fix22 (A : Set (GL (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ g ∈ A, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = (g : Matrix (Fin 3) (Fin 3) F) 2 2 • v}
  add_mem' := by
    intro v w hv hw g hg
    rw [Matrix.mulVec_add, hv g hg, hw g hg, smul_add]
  zero_mem' := by
    intro g _
    rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' := by
    intro c v hv g hg
    rw [Matrix.mulVec_smul, hv g hg, smul_comm]

@[expose] def burnsideA315y_comm22 (A : Set (GL (Fin 3) F)) : Submodule F (Fin 3 → F) :=
  Submodule.span F {u | ∃ g ∈ A, ∃ v : Fin 3 → F,
    u = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - (g : Matrix (Fin 3) (Fin 3) F) 2 2 • v}

theorem burnsideA315y_blkMat_e3 (A : Matrix (Fin 2) (Fin 2) F) :
    blkMat A 1 *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  funext i
  fin_cases i <;> simp [blkMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideA315y_inv_e3 {D : GL (Fin 3) F}
    (hD : (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1]) :
    ((D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
  conv_lhs => rw [← hD]
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem burnsideA315y_conj_22 (h2 : (2 : F) ≠ 0) {D g : GL (Fin 3) F}
    (hD : (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1])
    (hg : g * negDiag3 F = negDiag3 F * g)
    (hg' : D * g * D⁻¹ * negDiag3 F = negDiag3 F * (D * g * D⁻¹)) :
    ((D * g * D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  have h1 := burnsideA315y_mulVec_e3 h2 hg'
  have h3 : ((D * g * D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 • ![0, 0, 1] := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      burnsideA315y_inv_e3 hD, burnsideA315y_mulVec_e3 h2 hg, Matrix.mulVec_smul, hD]
  rw [h1] at h3
  have := congrFun h3 2
  simpa using this

theorem burnsideA315y_caseII1 (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) {Da Db : GL (Fin 3) F}
    (hDa : (Da : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (hDb : (Db : Matrix (Fin 3) (Fin 3) F) = blkMat (c • burnsideA315y_qb x y) 1)
    (A : Set (GL (Fin 3) F)) (hAz : ∀ g ∈ A, g * negDiag3 F = negDiag3 F * g)
    (hAns : ∃ g ∈ A, ∃ v : Fin 3 → F,
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ≠ (g : Matrix (Fin 3) (Fin 3) F) 2 2 • v)
    (hAa : ∀ g ∈ A, Da⁻¹ * g * Da ∈ A ∧ Da * g * Da⁻¹ ∈ A)
    (hAb : ∀ g ∈ A, Db⁻¹ * g * Db ∈ A ∧ Db * g * Db⁻¹ ∈ A)
    (b : GL (Fin 3) F) (hb : ∀ g ∈ A, b * g = g * b) :
    b * negDiag3 F = negDiag3 F * b := by
  classical
  have hDae3 : (Da : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [hDa]; exact burnsideA315y_blkMat_e3 _
  have hDbe3 : (Db : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [hDb]; exact burnsideA315y_blkMat_e3 _
  have h22 : ∀ D : GL (Fin 3) F, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] →
      ∀ g ∈ A, D * g * D⁻¹ ∈ A →
        ((D * g * D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
          (g : Matrix (Fin 3) (Fin 3) F) 2 2 :=
    fun D hD g hg hg' => burnsideA315y_conj_22 h2 hD (hAz g hg) (hAz _ hg')
  have h22' : ∀ D : GL (Fin 3) F, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] →
      ∀ g ∈ A, D⁻¹ * g * D ∈ A →
        ((D⁻¹ * g * D : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
          (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    intro D hD g hg hg'
    have := burnsideA315y_conj_22 h2 (burnsideA315y_inv_e3 hD) (hAz g hg)
      (by rw [inv_inv]; exact hAz _ hg')
    rwa [inv_inv] at this
  have hblk : ∀ g ∈ A, (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    intro g hg
    apply block_eq_zero_of_commute_negDiag h2
    rw [← coe_negDiag3, ← Units.val_mul, hAz g hg, Units.val_mul]
  set Fx := burnsideA315y_fix22 A with hFx
  set Cm := burnsideA315y_comm22 A with hCm
  have hlFx : ∀ u : Fin 3 → F, u 0 = 0 → u 1 = 0 → u ∈ Fx := by
    intro u hu0 hu1 g hg
    have hu : u = u 2 • ![0, 0, 1] := by
      funext i
      fin_cases i <;> simp [hu0, hu1]
    rw [hu, Matrix.mulVec_smul, burnsideA315y_mulVec_e3 h2 (hAz g hg), smul_comm]
  have hFxD : ∀ D : GL (Fin 3) F, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] →
      (∀ g ∈ A, D⁻¹ * g * D ∈ A) → ∀ v ∈ Fx, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Fx := by
    intro D hD hDA v hv g hg
    have hmul : (g : Matrix (Fin 3) (Fin 3) F) * (D : Matrix (Fin 3) (Fin 3) F) =
        (D : Matrix (Fin 3) (Fin 3) F) * ((D⁻¹ * g * D : GL (Fin 3) F) : Matrix _ _ F) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec, hmul, ← Matrix.mulVec_mulVec, hv _ (hDA g hg), Matrix.mulVec_smul,
      h22' D hD g hg (hDA g hg)]
  have hFxz : ∀ v ∈ Fx, (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Fx := by
    intro v hv g hg
    have hmul : (g : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
        diagonal ![-1, -1, 1] * (g : Matrix (Fin 3) (Fin 3) F) := by
      rw [← coe_negDiag3, ← Units.val_mul, hAz g hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hmul, ← Matrix.mulVec_mulVec, hv g hg, Matrix.mulVec_smul]
  have hFxcls := burnsideA315y_invariant h2 hxy hc Fx hFxz
    (fun v hv => by rw [← hDa]; exact hFxD Da hDae3 (fun g hg => (hAa g hg).1) v hv)
    (fun v hv => by rw [← hDb]; exact hFxD Db hDbe3 (fun g hg => (hAb g hg).1) v hv)
  have he3Fx : ![0, 0, 1] ∈ Fx := hlFx _ (by simp) (by simp)
  obtain ⟨g₀, hg₀, v₀, hv₀⟩ := hAns
  have hFxl : Fx = burnsideA315y_l F := by
    rcases hFxcls with h | h | h | h
    · rw [h, Submodule.mem_bot] at he3Fx
      have := congrFun he3Fx 2
      simp at this
    · exact h
    · rw [h, burnsideA315y_mem_W] at he3Fx
      simp at he3Fx
    · exfalso
      have : v₀ ∈ Fx := by rw [h]; trivial
      exact hv₀ (this g₀ hg₀)
  have hCmD : ∀ D : GL (Fin 3) F, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] →
      (∀ g ∈ A, D * g * D⁻¹ ∈ A) → ∀ u ∈ Cm, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Cm := by
    intro D hD hDA u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, hg, v, rfl⟩ := hu
      apply Submodule.subset_span
      refine ⟨D * g * D⁻¹, hDA g hg, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ v, ?_⟩
      rw [h22 D hD g hg (hDA g hg), Matrix.mulVec_sub, Matrix.mulVec_smul]
      congr 1
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    | zero => rw [Matrix.mulVec_zero]; exact Cm.zero_mem
    | add u w _ _ hu hw => rw [Matrix.mulVec_add]; exact Cm.add_mem hu hw
    | smul a u _ hu => rw [Matrix.mulVec_smul]; exact Cm.smul_mem a hu
  have hCmz : ∀ u ∈ Cm, (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Cm := by
    have hz3 : (negDiag3 F : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
      funext i
      fin_cases i <;> simp [coe_negDiag3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, diagonal]
    have hzA : ∀ g ∈ A, negDiag3 F * g * (negDiag3 F)⁻¹ ∈ A := by
      intro g hg
      rw [← hAz g hg, mul_inv_cancel_right]
      exact hg
    intro u hu
    rw [← coe_negDiag3]
    exact hCmD _ hz3 hzA u hu
  have hCmW : ∀ u ∈ Cm, u 2 = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, hg, v, rfl⟩ := hu
      obtain ⟨-, -, h20, h21⟩ := hblk g hg
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21]
    | zero => rfl
    | add u w _ _ hu hw => simp [hu, hw]
    | smul a u _ hu => simp [hu]
  have hCmcls := burnsideA315y_invariant h2 hxy hc Cm hCmz
    (fun v hv => by rw [← hDa]; exact hCmD Da hDae3 (fun g hg => (hAa g hg).2) v hv)
    (fun v hv => by rw [← hDb]; exact hCmD Db hDbe3 (fun g hg => (hAb g hg).2) v hv)
  have hu₀ : (g₀ : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ - (g₀ : Matrix (Fin 3) (Fin 3) F) 2 2 • v₀ ∈ Cm :=
    Submodule.subset_span ⟨g₀, hg₀, v₀, rfl⟩
  have hCmW' : Cm = burnsideA315y_W F := by
    rcases hCmcls with h | h | h | h
    · exfalso
      rw [h, Submodule.mem_bot, sub_eq_zero] at hu₀
      exact hv₀ hu₀
    · exfalso
      have : ![0, 0, 1] ∈ Cm := by rw [h, burnsideA315y_mem_l]; simp
      have := hCmW _ this
      simp at this
    · exact h
    · exfalso
      have : ![0, 0, 1] ∈ Cm := by rw [h]; trivial
      have := hCmW _ this
      simp at this
  have hbFx : ∀ v ∈ Fx, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Fx := by
    intro v hv g hg
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← hb g hg, Units.val_mul, ← Matrix.mulVec_mulVec,
      hv g hg, Matrix.mulVec_smul]
  have hbCm : ∀ u ∈ Cm, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ Cm := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨g, hg, v, rfl⟩ := hu
      apply Submodule.subset_span
      refine ⟨g, hg, (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v, ?_⟩
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        ← Units.val_mul, ← Units.val_mul, hb g hg]
    | zero => rw [Matrix.mulVec_zero]; exact Cm.zero_mem
    | add u w _ _ hu hw => rw [Matrix.mulVec_add]; exact Cm.add_mem hu hw
    | smul a u _ hu => rw [Matrix.mulVec_smul]; exact Cm.smul_mem a hu
  have hbe3 := hbFx _ he3Fx
  rw [hFxl, burnsideA315y_mem_l] at hbe3
  have hbe1 := hbCm ![1, 0, 0] (by rw [hCmW', burnsideA315y_mem_W]; simp)
  have hbe2 := hbCm ![0, 1, 0] (by rw [hCmW', burnsideA315y_mem_W]; simp)
  rw [hCmW', burnsideA315y_mem_W] at hbe1 hbe2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hbe3 hbe1 hbe2
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_negDiag3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, hbe3.1, hbe3.2, hbe1, hbe2]

theorem burnsideA315y_mulVec_e3_apply (g : Matrix (Fin 3) (Fin 3) F) (i : Fin 3) :
    (g *ᵥ ![0, 0, 1]) i = g i 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideA315y_eq_one_of_isUW {g : GL (Fin 3) F}
    (hg : burnsideA315y_IsUW (g : Matrix (Fin 3) (Fin 3) F))
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0) (h1 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) :
    g = 1 := by
  obtain ⟨a00, a01, a10, a11, a20, a21, a22⟩ := hg
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a10, a11, a20, a21, a22, h0, h1]

theorem burnsideA315y_eq_one_of_isUl {g : GL (Fin 3) F}
    (hg : burnsideA315y_IsUl (g : Matrix (Fin 3) (Fin 3) F))
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h1 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    g = 1 := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a22⟩ := hg
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a02, a10, a11, a12, a22, h0, h1]

theorem burnsideA315y_basis_of_ne (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) {u₀ u₁ : F} (hu : u₀ ≠ 0 ∨ u₁ ≠ 0) :
    u₀ * u₀ - u₁ * (-u₁) ≠ 0 ∨
      u₀ * (c * (y * u₀ - x * u₁)) - u₁ * (c * (x * u₀ + y * u₁)) ≠ 0 := by
  by_cases hn : u₀ ^ 2 + u₁ ^ 2 = 0
  · right
    intro hD
    have hu0 : u₀ ≠ 0 := by
      intro h0
      rw [h0] at hn
      have : u₁ ^ 2 = 0 := by linear_combination hn
      rcases hu with h | h
      · exact h h0
      · exact h (pow_eq_zero_iff (by norm_num) |>.mp this)
    have h3 : c * (2 * u₀ * (y * u₀ - x * u₁)) = 0 := by
      linear_combination hD + c * y * hn
    have h4 : y * u₀ - x * u₁ = 0 := by
      have := (mul_eq_zero.mp h3).resolve_left hc
      have h22 : (2 : F) * u₀ ≠ 0 := mul_ne_zero h2 hu0
      exact (mul_eq_zero.mp this).resolve_left h22
    apply hxy
    have h5 : (x ^ 2 + y ^ 2) * u₀ ^ 2 = 0 := by
      linear_combination (y * u₀ + x * u₁) * h4 + x ^ 2 * hn
    exact (mul_eq_zero.mp h5).resolve_right (pow_ne_zero 2 hu0)
  · left
    intro hD
    apply hn
    linear_combination hD

theorem burnsideA315y_UW_basis (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) {Da Db : GL (Fin 3) F}
    (hDa : (Da : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (hDb : (Db : Matrix (Fin 3) (Fin 3) F) = blkMat (c • burnsideA315y_qb x y) 1)
    (E : Subgroup (GL (Fin 3) F)) (hE : ∀ e ∈ E, burnsideA315y_IsUW (e : Matrix (Fin 3) (Fin 3) F))
    (hne : E ≠ ⊥) (hDaE : ∀ e ∈ E, Da * e * Da⁻¹ ∈ E) (hDbE : ∀ e ∈ E, Db * e * Db⁻¹ ∈ E) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, (e₁ : Matrix (Fin 3) (Fin 3) F) 0 2 * (e₂ : Matrix (Fin 3) (Fin 3) F) 1 2 -
      (e₁ : Matrix (Fin 3) (Fin 3) F) 1 2 * (e₂ : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 := by
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have he1' : (e : GL (Fin 3) F) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hu : (e : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 ∨ (e : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0 := by
    by_contra h
    push Not at h
    exact he1' (burnsideA315y_eq_one_of_isUW (hE e he) h.1 h.2)
  have hcol : ∀ D : GL (Fin 3) F, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] →
      ∀ g : GL (Fin 3) F, ((D * g * D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
        (D : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1]) := by
    intro D hD g
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      burnsideA315y_inv_e3 hD]
  have hDae3 : (Da : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [hDa]; exact burnsideA315y_blkMat_e3 _
  have hDbe3 : (Db : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    rw [hDb]; exact burnsideA315y_blkMat_e3 _
  obtain ⟨-, -, -, -, h20, h21, h22⟩ := hE e he
  have ha0 : ((Da * e * Da⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 =
      -(e : Matrix (Fin 3) (Fin 3) F) 1 2 := by
    rw [← burnsideA315y_mulVec_e3_apply ((Da * e * Da⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0,
      hcol Da hDae3 e, hDa]
    simp [blkMat, burnsideA315y_qa, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h22]
  have ha1 : ((Da * e * Da⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
      (e : Matrix (Fin 3) (Fin 3) F) 0 2 := by
    rw [← burnsideA315y_mulVec_e3_apply ((Da * e * Da⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1,
      hcol Da hDae3 e, hDa]
    simp [blkMat, burnsideA315y_qa, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h22]
  have hb0 : ((Db * e * Db⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 =
      c * (x * (e : Matrix (Fin 3) (Fin 3) F) 0 2 + y * (e : Matrix (Fin 3) (Fin 3) F) 1 2) := by
    rw [← burnsideA315y_mulVec_e3_apply ((Db * e * Db⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0,
      hcol Db hDbe3 e, hDb]
    simp [blkMat, burnsideA315y_qb, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h22]
    ring
  have hb1 : ((Db * e * Db⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
      c * (y * (e : Matrix (Fin 3) (Fin 3) F) 0 2 - x * (e : Matrix (Fin 3) (Fin 3) F) 1 2) := by
    rw [← burnsideA315y_mulVec_e3_apply ((Db * e * Db⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1,
      hcol Db hDbe3 e, hDb]
    simp [blkMat, burnsideA315y_qb, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h22]
    ring
  rcases burnsideA315y_basis_of_ne h2 hxy hc hu with hd | hd
  · refine ⟨e, he, Da * e * Da⁻¹, hDaE e he, ?_⟩
    rw [ha0, ha1]
    exact hd
  · refine ⟨e, he, Db * e * Db⁻¹, hDbE e he, ?_⟩
    rw [hb0, hb1]
    exact hd

theorem burnsideA315y_centralizer_UW {e₁ e₂ g : Matrix (Fin 3) (Fin 3) F}
    (h1 : burnsideA315y_IsUW e₁) (h2' : burnsideA315y_IsUW e₂)
    (hD : e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2 ≠ 0) (hg1 : g * e₁ = e₁ * g) (hg2 : g * e₂ = e₂ * g) :
    g 0 0 = g 2 2 ∧ g 1 1 = g 2 2 ∧ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  obtain ⟨a00, a01, a10, a11, a20, a21, a22⟩ := h1
  obtain ⟨b00, b01, b10, b11, b20, b21, b22⟩ := h2'
  have p00 := congrFun (congrFun hg1 0) 0
  have p01 := congrFun (congrFun hg1 0) 1
  have p02 := congrFun (congrFun hg1 0) 2
  have p10 := congrFun (congrFun hg1 1) 0
  have p11 := congrFun (congrFun hg1 1) 1
  have p12 := congrFun (congrFun hg1 1) 2
  have q00 := congrFun (congrFun hg2 0) 0
  have q01 := congrFun (congrFun hg2 0) 1
  have q02 := congrFun (congrFun hg2 0) 2
  have q10 := congrFun (congrFun hg2 1) 0
  have q11 := congrFun (congrFun hg2 1) 1
  have q12 := congrFun (congrFun hg2 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a10, a11, a20, a21, a22, b00, b01, b10,
    b11, b20, b21, b22] at p00 p01 p02 p10 p11 p12 q00 q01 q02 q10 q11 q12
  have hg20 : g 2 0 = 0 := by
    by_contra h
    apply hD
    rw [p00.resolve_right h, p10.resolve_right h]
    ring
  have hg21 : g 2 1 = 0 := by
    by_contra h
    apply hD
    rw [p01.resolve_right h, p11.resolve_right h]
    ring
  have r0 : (g 0 0 - g 2 2) * (e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2) = 0 := by
    linear_combination e₂ 1 2 * p02 - e₁ 1 2 * q02
  have r1 : g 0 1 * (e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2) = 0 := by
    linear_combination e₁ 0 2 * q02 - e₂ 0 2 * p02
  have r2 : g 1 0 * (e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2) = 0 := by
    linear_combination e₂ 1 2 * p12 - e₁ 1 2 * q12
  have r3 : (g 1 1 - g 2 2) * (e₁ 0 2 * e₂ 1 2 - e₁ 1 2 * e₂ 0 2) = 0 := by
    linear_combination e₁ 0 2 * q12 - e₂ 0 2 * p12
  refine ⟨?_, ?_, (mul_eq_zero.mp r1).resolve_right hD, (mul_eq_zero.mp r2).resolve_right hD,
    hg20, hg21⟩
  · linear_combination (mul_eq_zero.mp r0).resolve_right hD
  · linear_combination (mul_eq_zero.mp r3).resolve_right hD

theorem burnsideA315y_vecMul_e3_apply (g : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) :
    (![0, 0, 1] ᵥ* g) j = g 2 j := by
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem burnsideA315y_blkMat_e3_row (A : Matrix (Fin 2) (Fin 2) F) :
    ![0, 0, 1] ᵥ* blkMat A 1 = ![0, 0, 1] := by
  funext i
  fin_cases i <;> simp [blkMat, Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem burnsideA315y_inv_e3_row {D : GL (Fin 3) F}
    (hD : ![0, 0, 1] ᵥ* (D : Matrix (Fin 3) (Fin 3) F) = ![0, 0, 1]) :
    ![0, 0, 1] ᵥ* ((D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = ![0, 0, 1] := by
  conv_lhs => rw [← hD]
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem burnsideA315y_Ul_basis (h2 : (2 : F) ≠ 0) {x y c : F} (hxy : x ^ 2 + y ^ 2 ≠ 0)
    (hc : c ≠ 0) {Da Db : GL (Fin 3) F}
    (hDa : (Da : Matrix (Fin 3) (Fin 3) F) = blkMat (burnsideA315y_qa F) 1)
    (hDb : (Db : Matrix (Fin 3) (Fin 3) F) = blkMat (c • burnsideA315y_qb x y) 1)
    (E : Subgroup (GL (Fin 3) F)) (hE : ∀ e ∈ E, burnsideA315y_IsUl (e : Matrix (Fin 3) (Fin 3) F))
    (hne : E ≠ ⊥) (hDaE : ∀ e ∈ E, Da⁻¹ * e * Da ∈ E) (hDbE : ∀ e ∈ E, Db⁻¹ * e * Db ∈ E) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, (e₁ : Matrix (Fin 3) (Fin 3) F) 2 0 * (e₂ : Matrix (Fin 3) (Fin 3) F) 2 1 -
      (e₁ : Matrix (Fin 3) (Fin 3) F) 2 1 * (e₂ : Matrix (Fin 3) (Fin 3) F) 2 0 ≠ 0 := by
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have he1' : (e : GL (Fin 3) F) ≠ 1 := fun h => he1 (Subtype.ext h)
  have hu : (e : Matrix (Fin 3) (Fin 3) F) 2 0 ≠ 0 ∨ (e : Matrix (Fin 3) (Fin 3) F) 2 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact he1' (burnsideA315y_eq_one_of_isUl (hE e he) h.1 h.2)
  have hrow : ∀ D : GL (Fin 3) F, ![0, 0, 1] ᵥ* (D : Matrix (Fin 3) (Fin 3) F) = ![0, 0, 1] →
      ∀ g : GL (Fin 3) F, ![0, 0, 1] ᵥ* ((D⁻¹ * g * D : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (![0, 0, 1] ᵥ* (g : Matrix (Fin 3) (Fin 3) F)) ᵥ* (D : Matrix (Fin 3) (Fin 3) F) := by
    intro D hD g
    rw [Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      burnsideA315y_inv_e3_row hD]
  have hDae3 : ![0, 0, 1] ᵥ* (Da : Matrix (Fin 3) (Fin 3) F) = ![0, 0, 1] := by
    rw [hDa]; exact burnsideA315y_blkMat_e3_row _
  have hDbe3 : ![0, 0, 1] ᵥ* (Db : Matrix (Fin 3) (Fin 3) F) = ![0, 0, 1] := by
    rw [hDb]; exact burnsideA315y_blkMat_e3_row _
  obtain ⟨-, -, h02, -, -, h12, h22⟩ := hE e he
  have ha0 : ((Da⁻¹ * e * Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 =
      (e : Matrix (Fin 3) (Fin 3) F) 2 1 := by
    rw [← burnsideA315y_vecMul_e3_apply ((Da⁻¹ * e * Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0,
      hrow Da hDae3 e, hDa]
    simp [blkMat, burnsideA315y_qa, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22]
  have ha1 : ((Da⁻¹ * e * Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 =
      -(e : Matrix (Fin 3) (Fin 3) F) 2 0 := by
    rw [← burnsideA315y_vecMul_e3_apply ((Da⁻¹ * e * Da : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1,
      hrow Da hDae3 e, hDa]
    simp [blkMat, burnsideA315y_qa, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22]
  have hb0 : ((Db⁻¹ * e * Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 =
      c * (x * (e : Matrix (Fin 3) (Fin 3) F) 2 0 + y * (e : Matrix (Fin 3) (Fin 3) F) 2 1) := by
    rw [← burnsideA315y_vecMul_e3_apply ((Db⁻¹ * e * Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0,
      hrow Db hDbe3 e, hDb]
    simp [blkMat, burnsideA315y_qb, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22]
    ring
  have hb1 : ((Db⁻¹ * e * Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 =
      c * (y * (e : Matrix (Fin 3) (Fin 3) F) 2 0 - x * (e : Matrix (Fin 3) (Fin 3) F) 2 1) := by
    rw [← burnsideA315y_vecMul_e3_apply ((Db⁻¹ * e * Db : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1,
      hrow Db hDbe3 e, hDb]
    simp [blkMat, burnsideA315y_qb, Matrix.vecMul, dotProduct, Fin.sum_univ_three, h22]
    ring
  rcases burnsideA315y_basis_of_ne h2 hxy hc hu with hd | hd
  · refine ⟨e, he, Da⁻¹ * e * Da, hDaE e he, ?_⟩
    rw [ha0, ha1]
    intro h
    apply hd
    linear_combination -h
  · refine ⟨e, he, Db⁻¹ * e * Db, hDbE e he, ?_⟩
    rw [hb0, hb1]
    exact hd

theorem burnsideA315y_centralizer_Ul {e₁ e₂ g : Matrix (Fin 3) (Fin 3) F}
    (h1 : burnsideA315y_IsUl e₁) (h2' : burnsideA315y_IsUl e₂)
    (hD : e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0 ≠ 0) (hg1 : g * e₁ = e₁ * g) (hg2 : g * e₂ = e₂ * g) :
    g 0 0 = g 2 2 ∧ g 1 1 = g 2 2 ∧ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 0 2 = 0 ∧ g 1 2 = 0 := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a22⟩ := h1
  obtain ⟨b00, b01, b02, b10, b11, b12, b22⟩ := h2'
  have p00 := congrFun (congrFun hg1 0) 0
  have p02 := congrFun (congrFun hg1 0) 2
  have p11 := congrFun (congrFun hg1 1) 1
  have p12 := congrFun (congrFun hg1 1) 2
  have p20 := congrFun (congrFun hg1 2) 0
  have p21 := congrFun (congrFun hg1 2) 1
  have q00 := congrFun (congrFun hg2 0) 0
  have q02 := congrFun (congrFun hg2 0) 2
  have q11 := congrFun (congrFun hg2 1) 1
  have q12 := congrFun (congrFun hg2 1) 2
  have q20 := congrFun (congrFun hg2 2) 0
  have q21 := congrFun (congrFun hg2 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, a10, a11, a12, a22, b00, b01, b02,
    b10, b11, b12, b22] at p00 p02 p11 p12 p20 p21 q00 q02 q11 q12 q20 q21
  have hg02 : g 0 2 = 0 := by
    by_contra h
    apply hD
    rw [p00.resolve_left h, q00.resolve_left h]
    ring
  have hg12 : g 1 2 = 0 := by
    by_contra h
    apply hD
    rw [p11.resolve_left h, q11.resolve_left h]
    ring
  have r0 : (g 0 0 - g 2 2) * (e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0) = 0 := by
    linear_combination (-e₂ 2 1) * p20 + e₁ 2 1 * q20
  have r1 : g 1 0 * (e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0) = 0 := by
    linear_combination (-e₁ 2 0) * q20 + e₂ 2 0 * p20
  have r2 : g 0 1 * (e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0) = 0 := by
    linear_combination (-e₂ 2 1) * p21 + e₁ 2 1 * q21
  have r3 : (g 1 1 - g 2 2) * (e₁ 2 0 * e₂ 2 1 - e₁ 2 1 * e₂ 2 0) = 0 := by
    linear_combination (-e₁ 2 0) * q21 + e₂ 2 0 * p21
  refine ⟨?_, ?_, (mul_eq_zero.mp r2).resolve_right hD, (mul_eq_zero.mp r1).resolve_right hD,
    hg02, hg12⟩
  · linear_combination (mul_eq_zero.mp r0).resolve_right hD
  · linear_combination (mul_eq_zero.mp r3).resolve_right hD

theorem burnsideA315y_conj_22' (h2 : (2 : F) ≠ 0) {g h : GL (Fin 3) F}
    (hg : g * negDiag3 F = negDiag3 F * g) (hh : h * negDiag3 F = negDiag3 F * h) :
    ((g * h * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (h : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  have hgi : g⁻¹ * negDiag3 F = negDiag3 F * g⁻¹ := Commute.inv_left hg
  have h1 := burnsideA315y_mulVec_e3 h2 hg
  have h2' := burnsideA315y_mulVec_e3 h2 hh
  have h3 := burnsideA315y_mulVec_e3 h2 hgi
  have hgg : (g : Matrix (Fin 3) (Fin 3) F) 2 2 * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2
      = 1 := by
    have : ((g * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
      rw [mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h3, Matrix.mulVec_smul, h1, smul_smul] at this
    have := congrFun this 2
    simpa [mul_comm] using this
  have hc : ((g * h * g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] =
      (h : Matrix (Fin 3) (Fin 3) F) 2 2 • ![0, 0, 1] := by
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h3,
      Matrix.mulVec_smul, Matrix.mulVec_smul, h2', Matrix.mulVec_smul, h1, smul_smul, smul_smul]
    congr 1
    linear_combination (h : Matrix (Fin 3) (Fin 3) F) 2 2 * hgg
  have := congrFun hc 2
  rw [burnsideA315y_mulVec_e3_apply] at this
  simpa using this

theorem burnsideA315y_diag_comm_block {D N : Matrix (Fin 3) (Fin 3) F}
    (hD : D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = D 0 0 ∧ D 0 2 = 0 ∧ D 1 2 = 0 ∧ D 2 0 = 0 ∧ D 2 1 = 0)
    (hN : N 0 2 = 0 ∧ N 1 2 = 0 ∧ N 2 0 = 0 ∧ N 2 1 = 0) : D * N = N * D := by
  obtain ⟨d01, d10, d11, d02, d12, d20, d21⟩ := hD
  obtain ⟨n02, n12, n20, n21⟩ := hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, d01, d10, d11, d02, d12, d20, d21, n02, n12, n20,
      n21] <;> ring

@[expose] noncomputable def burnsideA315y_dgl (s : Fˣ) : GL (Fin 3) F :=
  ⟨blkMat ((s : F) • 1) 1, blkMat (((s⁻¹ : Fˣ) : F) • 1) 1, by
    rw [blkMat_mul, smul_mul_smul_comm, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, mul_one, blkMat_one], by
    rw [blkMat_mul, smul_mul_smul_comm, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul, mul_one, blkMat_one]⟩

theorem burnsideA315y_dgl_val (s : Fˣ) :
    ((burnsideA315y_dgl s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = blkMat ((s : F) • 1) 1 :=
  rfl

theorem burnsideA315y_pow_e3 {g : GL (Fin 3) F} {lam : F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = lam • ![0, 0, 1]) (m : ℕ) :
    ((g ^ m : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = lam ^ m • ![0, 0, 1] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ, mul_comm]

end CFSG.ASVolI
