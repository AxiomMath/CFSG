module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LieType.SpecialLinear.FieldActor.SemilinearDescent
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private lemma exists_B_transpose (h : UnitaryFieldData p f K) {n : ℕ} (hn : n ≠ 0)
    {B : Matrix (Fin n) (Fin n) K} (hBu : (B.map h.bar)ᵀ * B = 1)
    {c₂ : K} (hB2 : B * B.map h.bar = c₂ • 1) :
    ∃ d : K, (d = 1 ∨ d = -1) ∧ h.bar d = d ∧ Bᵀ = d • B ∧
      B * B.map h.bar = d • 1 ∧ B ≠ 0 := by
  classical
  have hBB' : B * (B.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hBu
  have hBbar : B.map h.bar = c₂ • (B.map h.bar)ᵀ := by
    have hm := congrArg (fun M => (B.map h.bar)ᵀ * M) hB2
    rw [Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hBu, Matrix.one_mul] at hm
    exact hm
  have hBmap : B = h.bar c₂ • Bᵀ := by
    have hm := congrArg (fun M => M.map h.bar) hBbar
    rw [Matrix.map_smul' h.bar c₂ _ (fun a b => map_mul h.bar a b),
      Matrix.transpose_map] at hm
    have hbarbar : ∀ M : Matrix (Fin n) (Fin n) K, (M.map h.bar).map h.bar = M :=
      Matrix.map_involutive h.bar_bar
    simpa [hbarbar] using hm
  have hBt : Bᵀ = h.bar c₂ • B := by
    have hm := congrArg Matrix.transpose hBmap
    rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at hm
  have hBscalar : B = (h.bar c₂ * h.bar c₂) • B := by
    calc B = h.bar c₂ • Bᵀ := hBmap
      _ = h.bar c₂ • (h.bar c₂ • B) := by rw [hBt]
      _ = (h.bar c₂ * h.bar c₂) • B := by rw [smul_smul]
  have h1ne0 : (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h10
    have h := congrFun (congrFun h10 ⟨0, Nat.pos_of_ne_zero hn⟩) ⟨0, Nat.pos_of_ne_zero hn⟩
    simp at h
  have hB0 : B ≠ 0 := by
    intro h0
    apply h1ne0
    rw [← hBB', h0, Matrix.zero_mul]
  have hentry : ∃ i j, B i j ≠ 0 := by
    by_contra! hc
    exact hB0 (Matrix.ext fun i j => by simpa using hc i j)
  obtain ⟨i, j, hij⟩ := hentry
  have hsq : h.bar c₂ * h.bar c₂ = 1 := by
    have hm := congrFun (congrFun hBscalar i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hm
    exact mul_right_cancel₀ hij (by rw [one_mul]; exact hm.symm)
  rcases mul_self_eq_one_iff.mp hsq with hc | hc
  · have hc₂ : c₂ = 1 := by rw [← h.bar_bar c₂, hc, map_one]
    exact ⟨1, Or.inl rfl, by simp, by rw [hBt, hc, one_smul],
      by rw [hB2, hc₂, one_smul], hB0⟩
  · have hc₂ : c₂ = -1 := by rw [← h.bar_bar c₂, hc, map_neg, map_one]
    exact ⟨-1, Or.inr rfl, by simp, by rw [hBt, hc], by rw [hB2, hc₂], hB0⟩


private lemma conj_key (h : UnitaryFieldData p f K) {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) K} {c₃ ν μ d : K}
    (hd : d = 1 ∨ d = -1) (hB2 : B * B.map h.bar = d • 1)
    (hν : h.norm ν = d) (hAB : A * B = c₃ • (B * A.map h.bar))
    (hc3 : h.norm c₃ = 1) (hμbar : h.bar μ = μ * c₃) :
    (ν • B) * (h.bar μ • A.map h.bar) * ((ν • B).map h.bar) = μ • A := by
  have hdd : d * d = 1 := by rcases hd with rfl | rfl <;> norm_num
  have hc3ne : c₃ ≠ 0 := by
    intro h0
    rw [UnitaryFieldData.norm, h0, map_zero, mul_zero] at hc3
    exact zero_ne_one hc3
  have hBA : B * A.map h.bar = c₃⁻¹ • (A * B) := by
    have hm := congrArg (fun M => c₃⁻¹ • M) hAB
    rw [smul_smul, inv_mul_cancel₀ hc3ne, one_smul] at hm
    exact hm.symm
  have hstep : (ν • B) * (h.bar μ • A.map h.bar) * ((ν • B).map h.bar)
      = (d * h.bar μ) • ((B * A.map h.bar) * B.map h.bar) := by
    rw [Matrix.map_smul' h.bar ν B (fun a b => map_mul h.bar a b)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    have hν' : ν * h.bar ν = d := hν
    linear_combination h.bar μ * hν' 
  rw [hstep, hBA, Matrix.smul_mul, Matrix.mul_assoc, hB2, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, smul_smul]
  have hscalar : (d * h.bar μ) * c₃⁻¹ * d = μ := by
    rw [hμbar]
    calc d * (μ * c₃) * c₃⁻¹ * d = μ * (d * d) * (c₃ * c₃⁻¹) := by ring
      _ = μ := by rw [hdd, mul_inv_cancel₀ hc3ne]; ring
  rw [hscalar]

private lemma exists_descent (h : UnitaryFieldData p f K) {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} {d ν : K}
    (hB2 : B * B.map h.bar = d • 1) (hd : d = 1 ∨ d = -1) (hν : h.norm ν = d) :
    ∃ P : GL (Fin n) K, (ν • B) * (P : Matrix (Fin n) (Fin n) K).map h.bar = P := by
  classical
  have hdd : d * d = 1 := by rcases hd with rfl | rfl <;> norm_num
  have hMMbar : (ν • B) * (ν • B).map h.bar = 1 := by
    rw [Matrix.map_smul' h.bar ν B (fun a b => map_mul h.bar a b),
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB2, smul_smul]
    rw [show ν * h.bar ν = d from hν, hdd, one_smul]
  have hMM' : (ν • B).map h.bar * (ν • B) = 1 := mul_eq_one_comm.mpr hMMbar
  let b : GL (Fin n) K := Units.mk (ν • B) ((ν • B).map h.bar) hMMbar hMM'
  have hbdef : b = Units.mk (ν • B) ((ν • B).map h.bar) hMMbar hMM' := rfl
  let σ : K ≃+* K :=
    { toFun := h.bar, invFun := h.bar, left_inv := h.bar_bar, right_inv := h.bar_bar,
      map_mul' := map_mul h.bar, map_add' := map_add h.bar }
  have hσ : σ.trans σ = RingEquiv.refl K := by
    ext c
    simp [σ, h.bar_bar]
  have hσne : σ ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    exact hc (by
      have := congrArg (fun e : K ≃+* K => e c) h1
      simpa [σ] using this)
  have hb : b * Matrix.GeneralLinearGroup.map σ.toRingHom b = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
    exact congrFun (congrFun hMMbar i) j
  obtain ⟨P, hP⟩ := CFSG.LieType.SpecialLinear.exists_eq_mul_map_inv_of_mul_map_eq_one
    hσ hσne hb
  have hbP : b * Matrix.GeneralLinearGroup.map σ.toRingHom P = P := by
    rw [hP]
    group
  have hco := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hbP
  simp only [Matrix.GeneralLinearGroup.coe_mul] at hco
  have hcoe : ((Matrix.GeneralLinearGroup.map σ.toRingHom P : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K).map h.bar := rfl
  rw [hcoe] at hco
  exact ⟨P, by simpa only [b] using hco⟩


theorem exists_real_form (h : UnitaryFieldData p f K) (hn : n ≠ 0)
    {A B : Matrix (Fin n) (Fin n) K} (hAu : (A.map h.bar)ᵀ * A = 1)
    (hBu : (B.map h.bar)ᵀ * B = 1) {c₁ c₂ c₃ : K} (hA2 : A * A = c₁ • 1)
    (hB2 : B * B.map h.bar = c₂ • 1) (hAB : A * B = c₃ • (B * A.map h.bar)) :
    ∃ (P : GL (Fin n) K) (ν μ ε α : K) (G X : Matrix (Fin n) (Fin n) K),
      ν ≠ 0 ∧ μ ≠ 0 ∧ ε ≠ 0 ∧
      ν • B * (P : Matrix (Fin n) (Fin n) K).map h.bar = P ∧
      μ • A * P = P * X ∧
      ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P = ε • G ∧
      G.map h.bar = G ∧ (Gᵀ = G ∨ Gᵀ = -G) ∧ X.map h.bar = X ∧
      Xᵀ * G * X = h.norm μ • G ∧ X * X = α • 1 := by
  classical
  obtain ⟨d, hd, hbd, hBt, hB2', hB0⟩ := exists_B_transpose h hn hBu hB2
  have hdd : d * d = 1 := by rcases hd with rfl | rfl <;> norm_num
  have hdne : d ≠ 0 := by rcases hd with rfl | rfl <;> norm_num
  obtain ⟨ν, hν⟩ : ∃ ν : K, h.norm ν = d := by
    rcases hd with rfl | rfl
    · exact ⟨1, by rw [UnitaryFieldData.norm, map_one, mul_one]⟩
    · exact OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have hνne : ν ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm] at hν
    simp only [map_zero, mul_zero] at hν
    exact hdne hν.symm
  obtain ⟨P, hMP⟩ := exists_descent h hB2' hd hν
  have hbarM : ∀ M : Matrix (Fin n) (Fin n) K, (M.map h.bar).map h.bar = M :=
    Matrix.map_involutive h.bar_bar
  let Q : Matrix (Fin n) (Fin n) K := ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P
  have hQdef : Q = ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      (P : Matrix (Fin n) (Fin n) K) := rfl
  have hQbar : Q.map h.bar = Qᵀ := by
    simp only [Q, Matrix.map_mul, Matrix.transpose_map, hbarM, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hQform : Q = ν • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * B *
      (P : Matrix (Fin n) (Fin n) K).map h.bar) := by
    calc Q = ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          ((ν • B) * (P : Matrix (Fin n) (Fin n) K).map h.bar) := by
          rw [hQdef, hMP]
      _ = ν • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (B * (P : Matrix (Fin n) (Fin n) K).map h.bar)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = ν • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * B *
            (P : Matrix (Fin n) (Fin n) K).map h.bar) := by
          rw [← Matrix.mul_assoc]
  have hXt : (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * B *
      (P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ =
      ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
        ((d • B) * (P : Matrix (Fin n) (Fin n) K).map h.bar) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBt]
  have hQd : Qᵀ = d • Q := by
    rw [hQform, Matrix.transpose_smul, hXt, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, smul_smul, smul_smul]
    congr 1
    rw [mul_comm]
  obtain ⟨ε, hεne, hεbar⟩ : ∃ ε : K, ε ≠ 0 ∧ h.bar ε = d * ε := by
    rcases hd with rfl | rfl
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]⟩
    · obtain ⟨t, ht0, ht⟩ := OddUnitaryInvolutionSylow.exists_bar_eq_neg h
      exact ⟨t, ht0, by rw [ht, neg_one_mul]⟩
  let G : Matrix (Fin n) (Fin n) K := ε⁻¹ • Q
  have hGdef : G = ε⁻¹ • Q := rfl
  have hGbar : G.map h.bar = G := by
    simp only [G]
    rw [Matrix.map_smul' h.bar ε⁻¹ Q (fun a b => map_mul h.bar a b), hQbar, map_inv₀, hεbar,
      hQd]
    have hsc : (d * ε)⁻¹ * d = ε⁻¹ := by
      rcases hd with rfl | rfl <;> field_simp
    rw [smul_smul, hsc]
  have hGt : Gᵀ = d • G := by
    simp only [G]
    rw [Matrix.transpose_smul, hQd, smul_comm]
  have hGsym : Gᵀ = G ∨ Gᵀ = -G := by
    rcases hd with rfl | rfl
    · left; rw [hGt, one_smul]
    · right; rw [hGt]; simp
  have hPG : ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P = ε • G := by
    rw [hGdef, smul_inv_smul₀ hεne]
  have hABbar : (A.map h.bar) * (B.map h.bar) = h.bar c₃ • (B.map h.bar * A) := by
    have hm := congrArg (fun M => M.map h.bar) hAB
    rw [Matrix.map_smul' h.bar c₃ _ (fun a b => map_mul h.bar a b), Matrix.map_mul,
      Matrix.map_mul] at hm
    simpa [hbarM] using hm
  have hkey : d • A = (h.norm c₃ * d) • A := by
    calc d • A = A * (B * B.map h.bar) := by rw [hB2', Matrix.mul_smul, Matrix.mul_one]
      _ = (A * B) * B.map h.bar := by rw [Matrix.mul_assoc]
      _ = (c₃ • (B * A.map h.bar)) * B.map h.bar := by rw [hAB]
      _ = c₃ • ((B * A.map h.bar) * B.map h.bar) := by rw [Matrix.smul_mul]
      _ = c₃ • (B * (A.map h.bar * B.map h.bar)) := by rw [Matrix.mul_assoc]
      _ = c₃ • (B * (h.bar c₃ • (B.map h.bar * A))) := by rw [hABbar]
      _ = (c₃ * h.bar c₃) • (B * (B.map h.bar * A)) := by
          rw [Matrix.mul_smul, smul_smul]
      _ = (h.norm c₃ * d) • A := by
          rw [UnitaryFieldData.norm, ← Matrix.mul_assoc, hB2', Matrix.smul_mul,
            Matrix.one_mul, smul_smul]
  have hAA' : A * (A.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hAu
  have hA0 : A ≠ 0 := by
    intro h0
    have h1ne0 : (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
      intro h10
      have h := congrFun (congrFun h10 ⟨0, Nat.pos_of_ne_zero hn⟩) ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at h
    apply h1ne0
    rw [← hAA', h0, Matrix.zero_mul]
  have hAc : d = h.norm c₃ * d := by
    obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
      by_contra! hc
      exact hA0 (Matrix.ext fun i j => by simpa using hc i j)
    have hm := congrFun (congrFun hkey i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hm
    exact mul_right_cancel₀ hij hm
  have hc3 : h.norm c₃ = 1 := mul_right_cancel₀ hdne (by rw [← hAc, one_mul])
  have hc3ne : c₃ ≠ 0 := by
    intro h0
    rw [UnitaryFieldData.norm, h0, map_zero, mul_zero] at hc3
    exact zero_ne_one hc3
  have hc3inv : h.norm c₃⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv,
      show c₃ * h.bar c₃ = 1 from hc3, inv_one]
  obtain ⟨μ, hμne, hμdiv⟩ := h.exists_div_bar_eq hc3inv
  have hμbar : h.bar μ = μ * c₃ := by
    have hbμ : h.bar μ ≠ 0 := (h.bar_eq_zero_iff).not.mpr hμne
    have h1 : μ = c₃⁻¹ * h.bar μ := (div_eq_iff hbμ).mp hμdiv
    have h2 : c₃ * μ = h.bar μ := by
      conv_lhs => rw [h1]
      rw [← mul_assoc, mul_inv_cancel₀ hc3ne, one_mul]
    exact h2.symm.trans (mul_comm _ _)
  have hconj : (ν • B) * (h.bar μ • A.map h.bar) * (ν • B).map h.bar = μ • A :=
    conj_key h hd hB2' hν hAB hc3 hμbar
  have hAinv : (μ • A) * (μ⁻¹ • (A.map h.bar)ᵀ) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA', mul_inv_cancel₀ hμne, one_smul]
  have hAinv' : (μ⁻¹ • (A.map h.bar)ᵀ) * (μ • A) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAu, inv_mul_cancel₀ hμne, one_smul]
  let Ag : GL (Fin n) K := Units.mk (μ • A) (μ⁻¹ • (A.map h.bar)ᵀ) hAinv hAinv'
  have hAgdef : Ag = Units.mk (μ • A) (μ⁻¹ • (A.map h.bar)ᵀ) hAinv hAinv' := rfl
  let Xg : GL (Fin n) K := P⁻¹ * Ag * P
  have hXgdef : Xg = P⁻¹ * Ag * P := rfl
  have hXPg : Ag * P = P * Xg := by
    rw [hXgdef]; group
  have hXP : (μ • A) * P = P * (Xg : Matrix (Fin n) (Fin n) K) := by
    have hm := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hXPg
    simpa only [Matrix.GeneralLinearGroup.coe_mul, Ag] using hm
  have hPX : (P : Matrix (Fin n) (Fin n) K) * (Xg : Matrix (Fin n) (Fin n) K) =
      μ • (A * P) := by
    rw [← Matrix.smul_mul]
    exact hXP.symm
  have hMMbar : (ν • B) * (ν • B).map h.bar = 1 := by
    rw [Matrix.map_smul' h.bar ν B (fun a b => map_mul h.bar a b),
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB2', smul_smul]
    rw [show ν * h.bar ν = d from hν, hdd, one_smul]
  have hMM' : (ν • B).map h.bar * (ν • B) = 1 := mul_eq_one_comm.mpr hMMbar
  let b : GL (Fin n) K := Units.mk (ν • B) ((ν • B).map h.bar) hMMbar hMM'
  have hbdef : b = Units.mk (ν • B) ((ν • B).map h.bar) hMMbar hMM' := rfl
  let σ : K ≃+* K :=
    { toFun := h.bar, invFun := h.bar, left_inv := h.bar_bar, right_inv := h.bar_bar,
      map_mul' := map_mul h.bar, map_add' := map_add h.bar }
  have hbP : b * Matrix.GeneralLinearGroup.map σ.toRingHom P = P := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, b]
    have hcoe : ((Matrix.GeneralLinearGroup.map σ.toRingHom P : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K).map h.bar := rfl
    rw [hcoe]
    exact hMP
  have hmapP : Matrix.GeneralLinearGroup.map σ.toRingHom P = b⁻¹ * P := by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom P
        = b⁻¹ * (b * Matrix.GeneralLinearGroup.map σ.toRingHom P) := by
          rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = b⁻¹ * P := by rw [hbP]
  have hbDb : b * Matrix.GeneralLinearGroup.map σ.toRingHom Ag * b⁻¹ = Ag := by
    apply Units.ext
    have hbval : (b : Matrix (Fin n) (Fin n) K) = ν • B := rfl
    have hbinv : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (ν • B).map h.bar := rfl
    have hAgval : (Ag : Matrix (Fin n) (Fin n) K) = μ • A := rfl
    have hmapAg : ((Matrix.GeneralLinearGroup.map σ.toRingHom Ag : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (μ • A).map h.bar := rfl
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hbval, hbinv,
      hmapAg, hAgval, Matrix.map_smul' h.bar μ A (fun a b => map_mul h.bar a b)]
    exact hconj
  have hmapX : Matrix.GeneralLinearGroup.map σ.toRingHom Xg = Xg := by
    have hD : Matrix.GeneralLinearGroup.map σ.toRingHom Ag = b⁻¹ * Ag * b := by
      calc Matrix.GeneralLinearGroup.map σ.toRingHom Ag
          = b⁻¹ * (b * Matrix.GeneralLinearGroup.map σ.toRingHom Ag * b⁻¹) * b := by group
        _ = b⁻¹ * Ag * b := by rw [hbDb]
    simp only [hXgdef, map_mul, map_inv, hmapP, hD]
    group
  have hXbar : ((Xg : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar
      = (Xg : Matrix (Fin n) (Fin n) K) := by
    have hm := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hmapX
    have hcoe : ((Matrix.GeneralLinearGroup.map σ.toRingHom Xg : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (Xg : Matrix (Fin n) (Fin n) K).map h.bar := rfl
    rw [hcoe] at hm
    exact hm
  have hXQX : (Xg : Matrix (Fin n) (Fin n) K)ᵀ * Q * (Xg : Matrix (Fin n) (Fin n) K)
      = h.norm μ • Q := by
    have h3 : (Xg : Matrix (Fin n) (Fin n) K)ᵀ *
        ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ =
        h.bar μ • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
          (A.map h.bar)ᵀ) := by
      have hm := congrArg (fun M => M.map h.bar) hPX
      rw [Matrix.map_mul, Matrix.map_smul' h.bar μ _ (fun a b => map_mul h.bar a b),
        Matrix.map_mul, hXbar] at hm
      calc (Xg : Matrix (Fin n) (Fin n) K)ᵀ *
            ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ
          = (((P : Matrix (Fin n) (Fin n) K).map h.bar) *
              (Xg : Matrix (Fin n) (Fin n) K))ᵀ := by rw [Matrix.transpose_mul]
        _ = (h.bar μ • (A.map h.bar *
              (P : Matrix (Fin n) (Fin n) K).map h.bar))ᵀ := by rw [hm]
        _ = h.bar μ • ((A.map h.bar *
              (P : Matrix (Fin n) (Fin n) K).map h.bar))ᵀ := by rw [Matrix.transpose_smul]
        _ = h.bar μ • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
              (A.map h.bar)ᵀ) := by rw [Matrix.transpose_mul]
    calc (Xg : Matrix (Fin n) (Fin n) K)ᵀ * Q * (Xg : Matrix (Fin n) (Fin n) K)
        = ((Xg : Matrix (Fin n) (Fin n) K)ᵀ *
            ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ) *
            ((P : Matrix (Fin n) (Fin n) K) * (Xg : Matrix (Fin n) (Fin n) K)) := by
          rw [hQdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = (h.bar μ • (((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (A.map h.bar)ᵀ)) * (μ • (A * P)) := by rw [h3, hPX]
      _ = (h.bar μ * μ) • ((((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (A.map h.bar)ᵀ) * (A * P)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (h.bar μ * μ) • Q := by
          rw [Matrix.mul_assoc ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ (A.map h.bar)ᵀ
            (A * (P : Matrix (Fin n) (Fin n) K)), ← Matrix.mul_assoc (A.map h.bar)ᵀ A
            (P : Matrix (Fin n) (Fin n) K), hAu, Matrix.one_mul, ← hQdef]
      _ = h.norm μ • Q := by rw [UnitaryFieldData.norm, mul_comm (h.bar μ) μ]
  have hXGX : (Xg : Matrix (Fin n) (Fin n) K)ᵀ * G * (Xg : Matrix (Fin n) (Fin n) K)
      = h.norm μ • G := by
    calc (Xg : Matrix (Fin n) (Fin n) K)ᵀ * G * (Xg : Matrix (Fin n) (Fin n) K)
        = (Xg : Matrix (Fin n) (Fin n) K)ᵀ * (ε⁻¹ • Q) *
            (Xg : Matrix (Fin n) (Fin n) K) := by
          rw [hGdef]
      _ = ε⁻¹ • ((Xg : Matrix (Fin n) (Fin n) K)ᵀ * Q *
            (Xg : Matrix (Fin n) (Fin n) K)) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = ε⁻¹ • (h.norm μ • Q) := by rw [hXQX]
      _ = h.norm μ • (ε⁻¹ • Q) := smul_comm _ _ _
      _ = h.norm μ • G := by rw [hGdef]
  have hAgAg : ((Ag * Ag : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (μ * μ * c₁) • 1 := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    simp only [Ag]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA2, smul_smul]
  have hXsq : Xg * Xg = P⁻¹ * (Ag * Ag) * P := by
    rw [hXgdef]; group
  have hPP' : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hXX : (Xg : Matrix (Fin n) (Fin n) K) * (Xg : Matrix (Fin n) (Fin n) K) =
      (μ * μ * c₁) • 1 := by
    have hm : (Xg : Matrix (Fin n) (Fin n) K) * (Xg : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((Ag * Ag : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (P : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hXsq
      simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv] using h
    rw [hm, hAgAg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP']
  exact ⟨P, ν, μ, ε, μ * μ * c₁, G, (Xg : Matrix (Fin n) (Fin n) K),
    hνne, hμne, hεne, hMP, hXP, hPG, hGbar, hGsym, hXbar, hXGX, hXX⟩

end CFSG.LocalAnalysis.WeakClosure81.UOuter
