module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSingerGen
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofSpan

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open Matrix CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

variable {F : Type*} [Field F]

theorem xr10_mem_of_mem_muM [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), a ∈ muM F → b ∈ muM F → d ∈ muM F →
      diagSL a b d h ∈ K)
    (hD : ∀ h : 1 * ω * ω ^ 2 = 1, diagSL 1 ω (ω ^ 2) h ∈ K) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hK : xr (by decide : (1 : Fin 3) ≠ 0) c₀ ∈ K) (c : F) :
    xr (by decide : (1 : Fin 3) ≠ 0) c ∈ K := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  set R : AddSubgroup F :=
    { carrier := {t | xr (by decide : (1 : Fin 3) ≠ 0) (t * c₀) ∈ K}
      add_mem' := fun {a b} ha hb => by
        change xr _ ((a + b) * c₀) ∈ K
        rw [add_mul, ← xr_mul]
        exact K.mul_mem ha hb
      zero_mem' := by
        change xr _ (0 * c₀) ∈ K
        rw [zero_mul, xr_zero]
        exact K.one_mem
      neg_mem' := fun {a} ha => by
        change xr _ (-a * c₀) ∈ K
        rw [neg_mul, ← xr_inv]
        exact K.inv_mem ha } with hR
  have hconj : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K → ∀ t ∈ R,
      b / a * t ∈ R := by
    intro a b d h hK' t ht
    have e := conj_eq_of_mul_eq (diagSL_mul_xr10 a b d h (t * c₀))
    change xr _ (b / a * t * c₀) ∈ K
    rw [mul_assoc, ← e]
    exact K.mul_mem (K.mul_mem hK' ht) (K.inv_mem hK')
  have h1 : (1 : F) ∈ R := by
    change xr _ (1 * c₀) ∈ K
    rwa [one_mul]
  have hS : ∀ ζ ∈ muM F, ∀ r ∈ R, ζ * r ∈ R := by
    intro ζ hζ r hr
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_muM hζ
    have h : 1 * ζ * ζ⁻¹ = 1 := by field_simp
    have := hconj 1 ζ ζ⁻¹ h (hdiag 1 ζ ζ⁻¹ h one_mem_muM hζ (muM_inv hζ)) r hr
    rwa [div_one] at this
  have hωR : ∀ r ∈ R, ω * r ∈ R := by
    intro r hr
    have h : 1 * ω * ω ^ 2 = 1 := by linear_combination hω3
    have := hconj 1 ω (ω ^ 2) h (hD h) r hr
    rwa [div_one] at this
  have htop := addSubgroup_eq_top_of_muM hω hω1 h1 hS hωR
  have hmem : c / c₀ ∈ R := htop ▸ AddSubgroup.mem_top _
  change xr _ (c / c₀ * c₀) ∈ K at hmem
  rwa [div_mul_cancel₀ c hc₀] at hmem

theorem xr12_mem_of_mem_muM [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), a ∈ muM F → b ∈ muM F → d ∈ muM F →
      diagSL a b d h ∈ K)
    (hD : ∀ h : 1 * ω * ω ^ 2 = 1, diagSL 1 ω (ω ^ 2) h ∈ K) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hK : xr (by decide : (1 : Fin 3) ≠ 2) c₀ ∈ K) (c : F) :
    xr (by decide : (1 : Fin 3) ≠ 2) c ∈ K := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  set R : AddSubgroup F :=
    { carrier := {t | xr (by decide : (1 : Fin 3) ≠ 2) (t * c₀) ∈ K}
      add_mem' := fun {a b} ha hb => by
        change xr _ ((a + b) * c₀) ∈ K
        rw [add_mul, ← xr_mul]
        exact K.mul_mem ha hb
      zero_mem' := by
        change xr _ (0 * c₀) ∈ K
        rw [zero_mul, xr_zero]
        exact K.one_mem
      neg_mem' := fun {a} ha => by
        change xr _ (-a * c₀) ∈ K
        rw [neg_mul, ← xr_inv]
        exact K.inv_mem ha } with hR
  have hconj : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K → ∀ t ∈ R,
      b / d * t ∈ R := by
    intro a b d h hK' t ht
    have e := conj_eq_of_mul_eq (diagSL_mul_xr12 a b d h (t * c₀))
    change xr _ (b / d * t * c₀) ∈ K
    rw [mul_assoc, ← e]
    exact K.mul_mem (K.mul_mem hK' ht) (K.inv_mem hK')
  have h1 : (1 : F) ∈ R := by
    change xr _ (1 * c₀) ∈ K
    rwa [one_mul]
  have hS : ∀ ζ ∈ muM F, ∀ r ∈ R, ζ * r ∈ R := by
    intro ζ hζ r hr
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_muM hζ
    have h : ζ * 1 * ζ⁻¹ = 1 := by field_simp
    have := hconj ζ 1 ζ⁻¹ h (hdiag ζ 1 ζ⁻¹ h hζ one_mem_muM (muM_inv hζ)) r hr
    rwa [one_div, inv_inv] at this
  have hωR : ∀ r ∈ R, ω ^ 2 * r ∈ R := by
    intro r hr
    have h : 1 * ω * ω ^ 2 = 1 := by linear_combination hω3
    have := hconj 1 ω (ω ^ 2) h (hD h) r hr
    have e : ω / ω ^ 2 = ω ^ 2 := by
      rw [div_eq_iff (pow_ne_zero 2 hω0)]
      linear_combination (-ω) * hω3
    rwa [e] at this
  have hω' : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by linear_combination (ω ^ 2 - ω + 1) * hω
  have hω1' : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    calc ω = ω ^ 3 / ω ^ 2 := by field_simp
      _ = 1 := by rw [hω3, h, div_one]
  have htop := addSubgroup_eq_top_of_muM hω' hω1' h1 hS hωR
  have hmem : c / c₀ ∈ R := htop ▸ AddSubgroup.mem_top _
  change xr _ (c / c₀ * c₀) ∈ K at hmem
  rwa [div_mul_cancel₀ c hc₀] at hmem

theorem outerYSL_mem_of_conj_diag {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {α b γ s' : F}
    (hb : b ≠ 0) (hγ : γ ^ 2 + 3 * γ + 3 = 0)
    (hK : ∀ y : SpecialLinearGroup (Fin 3) F,
      heisC α * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * heisC α → y ∈ K)
    (hDb : ∀ h : b⁻¹ * 1 * b = 1, diagSL b⁻¹ 1 b h ∈ K)
    (h : (α * b ^ 3 - 1) * s' = γ) : outerYSL hγ s' ∈ K := by
  have hbb : b⁻¹ * 1 * b = 1 := by field_simp
  set D : SpecialLinearGroup (Fin 3) F := diagSL b⁻¹ 1 b hbb with hD
  set Y : SpecialLinearGroup (Fin 3) F := outerYSL hγ s' with hY
  have hAD := heisC_mul_diag (α := α) hb hbb
  rw [← hD] at hAD
  have hNY : (b⁻¹ • heisC (α * b ^ 3)) * (Y : Matrix (Fin 3) (Fin 3) F) =
      (Y : Matrix (Fin 3) (Fin 3) F) * (b⁻¹ • heisC (α * b ^ 3)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    exact (outerY_comm h).symm
  have hDDi : (D : Matrix (Fin 3) (Fin 3) F) * ((D⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hDiD : ((D⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (D : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set N : Matrix (Fin 3) (Fin 3) F := b⁻¹ • heisC (α * b ^ 3) with hN
  set Dm : Matrix (Fin 3) (Fin 3) F := (D : Matrix (Fin 3) (Fin 3) F) with hDm
  set Di : Matrix (Fin 3) (Fin 3) F := ((D⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hDi
  set Ym : Matrix (Fin 3) (Fin 3) F := (Y : Matrix (Fin 3) (Fin 3) F) with hYm
  have hA : heisC α = Dm * N * Di := by
    calc heisC α = heisC α * (Dm * Di) := by rw [hDDi, Matrix.mul_one]
      _ = Dm * N * Di := by rw [← Matrix.mul_assoc, hAD]
  have hcomm : heisC α * ((D * Y * D⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((D * Y * D⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * heisC α := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [← hDm, ← hDi, ← hYm, hA]
    calc Dm * N * Di * (Dm * Ym * Di) = Dm * (N * (Di * Dm) * Ym) * Di := by
          simp only [Matrix.mul_assoc]
      _ = Dm * (Ym * N) * Di := by rw [hDiD, Matrix.mul_one, hNY]
      _ = Dm * Ym * (Di * Dm) * N * Di := by
          rw [hDiD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Dm * Ym * Di * (Dm * N * Di) := by simp only [Matrix.mul_assoc]
  have hmem := hK _ hcomm
  have e : Y = D⁻¹ * (D * Y * D⁻¹) * D := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.inv_mem (hDb hbb)) hmem) (hDb hbb)

theorem eq_top_of_singer_muM [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    {ω α b : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hα : α ≠ 0)
    (hαc : ¬ ∃ μ : F, μ ^ 3 = α) (hbS : b ∈ muM F) (hb3 : b ^ 3 ≠ 1)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), a ∈ muM F → b ∈ muM F → d ∈ muM F →
      diagSL a b d h ∈ K)
    (hD : ∀ h : 1 * ω * ω ^ 2 = 1, diagSL 1 ω (ω ^ 2) h ∈ K)
    (hK : ∀ y : SpecialLinearGroup (Fin 3) F,
      heisC α * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * heisC α → y ∈ K)
    {gα : GL (Fin 3) F} (hgα : (gα : Matrix (Fin 3) (Fin 3) F) = heisC α)
    (hinv : ∀ x ∈ K, conjUnit gα x ∈ K) : K = ⊤ := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h3 : (3 : F) ≠ 0 := by
    intro h
    apply hω1
    have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hω - ω * h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hα1 : α - 1 ≠ 0 := fun h => hαc ⟨1, by linear_combination (-1 : F) * h⟩
  have hb0 : b ≠ 0 := ne_zero_of_mem_muM hbS
  have hα'1 : α * b ^ 3 - 1 ≠ 0 := by
    intro h
    apply hαc
    refine ⟨b⁻¹, ?_⟩
    field_simp
    linear_combination (-1 : F) * h
  have hb31 : b ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hb3
  have hbi : b⁻¹ ∈ muM F := muM_inv hbS
  have hbi2 : b⁻¹ ^ 2 ∈ muM F := by
    rw [sq]
    exact muM_mul hbi hbi
  set c : F := 1 / (α - 1) - 1 / (α * b ^ 3 - 1) with hcdef
  have hc : c ≠ 0 := by
    have : c = α * (b ^ 3 - 1) / ((α - 1) * (α * b ^ 3 - 1)) := by
      rw [hcdef]; field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hα hb31) (mul_ne_zero hα1 hα'1)
  have hγ₁ : (-(ω + 2)) ^ 2 + 3 * (-(ω + 2)) + 3 = 0 := by linear_combination hω
  have hγ₂ : (-(ω ^ 2 + 2)) ^ 2 + 3 * (-(ω ^ 2 + 2)) + 3 = 0 := by
    linear_combination (ω ^ 2 - ω + 1) * hω
  have hsum : -(ω + 2) + -(ω ^ 2 + 2) = -3 := by linear_combination (-1 : F) * hω
  have hDb : ∀ h : b⁻¹ * 1 * b = 1, diagSL b⁻¹ 1 b h ∈ K := fun h =>
    hdiag _ _ _ h hbi one_mem_muM hbS
  have htau : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0), outerTauSL γ c ∈ K := by
    intro γ hγ
    have hs : (α - 1) * (γ / (α - 1)) = γ := by field_simp
    have hs' : (α * b ^ 3 - 1) * (γ / (α * b ^ 3 - 1)) = γ := by field_simp
    have hYs : outerYSL hγ (γ / (α - 1)) ∈ K := hK _ (outerY_comm hs).symm
    have hYs' : outerYSL hγ (γ / (α * b ^ 3 - 1)) ∈ K :=
      outerYSL_mem_of_conj_diag hb0 hγ hK hDb hs'
    have e : outerTauSL γ c =
        outerYSL hγ (γ / (α - 1)) * (outerYSL hγ (γ / (α * b ^ 3 - 1)))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      have h1 : γ / (α - 1) = γ / (α * b ^ 3 - 1) + c * γ := by
        rw [hcdef]; field_simp; ring
      have h2 := outerY_eq_tau hγ (γ / (α * b ^ 3 - 1)) c
      rw [← h1] at h2
      exact h2.symm
    rw [e]
    exact K.mul_mem hYs (K.inv_mem hYs')
  set T₀ : SpecialLinearGroup (Fin 3) F :=
    outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c with hT₀def
  have hT₀ : T₀ ∈ K := K.mul_mem (htau _ hγ₁) (htau _ hγ₂)
  have hT₀m : (T₀ : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)] := outerTau_mul hsum c
  obtain ⟨m, hmdef⟩ : ∃ m : F, m = 3 * c * ((b ^ 3)⁻¹ - 1) := ⟨_, rfl⟩
  have hbt : b * b⁻¹ ^ 2 * b = 1 := by field_simp
  obtain ⟨X, hXdef⟩ : ∃ X : SpecialLinearGroup (Fin 3) F,
      X = xr (by decide : (1 : Fin 3) ≠ 0) m * xr (by decide : (1 : Fin 3) ≠ 2) (-m) := ⟨_, rfl⟩
  have hdt : diagSL b (b⁻¹ ^ 2) b hbt ∈ K := hdiag _ _ _ hbt hbS hbi2 hbS
  have hX : X ∈ K := by
    have hA := diag_mul_T0 hb0 hbt hmdef hT₀m
    rw [← hXdef] at hA
    have e : X = diagSL b (b⁻¹ ^ 2) b hbt * T₀ * (diagSL b (b⁻¹ ^ 2) b hbt)⁻¹ * T₀⁻¹ := by
      rw [hA]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem hdt hT₀) (K.inv_mem hdt)) (K.inv_mem hT₀)
  have hbt' : b⁻¹ ^ 2 * b * b = 1 := by field_simp
  have hdt' : diagSL (b⁻¹ ^ 2) b b hbt' ∈ K := hdiag _ _ _ hbt' hbi2 hbS hbS
  have hx0 : xr (by decide : (1 : Fin 3) ≠ 0) ((b ^ 3 - 1) * m) ∈ K := by
    have hB := diag_mul_X (m := m) hb0 hbt'
    rw [← hXdef] at hB
    have e : xr (by decide : (1 : Fin 3) ≠ 0) ((b ^ 3 - 1) * m) =
        diagSL (b⁻¹ ^ 2) b b hbt' * X * (diagSL (b⁻¹ ^ 2) b b hbt')⁻¹ * X⁻¹ := by
      rw [hB]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem hdt' hX) (K.inv_mem hdt')) (K.inv_mem hX)
  have hb3' : (b ^ 3)⁻¹ - 1 ≠ 0 := by
    intro h
    apply hb3
    have h' : (b ^ 3)⁻¹ = 1 := sub_eq_zero.1 h
    rw [inv_eq_one] at h'
    exact h'
  have hm : m ≠ 0 := hmdef ▸ mul_ne_zero (mul_ne_zero h3 hc) hb3'
  have h10 := xr10_mem_of_mem_muM hω hω1 hdiag hD (mul_ne_zero hb31 hm) hx0
  have hx12 : xr (by decide : (1 : Fin 3) ≠ 2) (-m) ∈ K := by
    have e : xr (by decide : (1 : Fin 3) ≠ 2) (-m) =
        (xr (by decide : (1 : Fin 3) ≠ 0) m)⁻¹ * X := by
      rw [hXdef, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact K.mul_mem (K.inv_mem (h10 m)) hX
  have h12 := xr12_mem_of_mem_muM hω hω1 hdiag hD (neg_ne_zero.2 hm) hx12
  exact eq_top_of_xr10_xr12 hα hgα hinv h10 h12

end CFSG.RankThree.PartTwo.Sec14.L3PGL
