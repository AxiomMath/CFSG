module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1

public section

namespace CFSG.ASVolI

open CFSG.Quasithin.H13.Ch4.C135 (dualHom coe_dualHom dualHom_dualHom)
open scoped Matrix

variable {F : Type} [Field F]

theorem burnsideC135_cross_mulVec (A : Matrix (Fin 3) (Fin 3) F) (x y : Fin 3 → F) :
    (A *ᵥ x) ⨯₃ (A *ᵥ y) = (A.adjugate)ᵀ *ᵥ (x ⨯₃ y) := by
  rw [Matrix.adjugate_fin_three]
  funext i
  fin_cases i <;>
  simp [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] <;>
  ring

theorem burnsideC135_cross_dualHom (γ : Matrix.SpecialLinearGroup (Fin 3) F) (x y : Fin 3 → F) :
    (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) ⨯₃
        (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ (x ⨯₃ y) := by
  rw [burnsideC135_cross_mulVec, coe_dualHom, ← Matrix.adjugate_transpose,
    Matrix.transpose_transpose, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_adjugate _ (by simp), γ.2, one_pow, one_smul]

abbrev burnsideC135_e (F : Type) [Field F] (i : Fin 3) : Fin 3 → F := Pi.single i 1

theorem burnsideC135_vec_eq (x : Fin 3 → F) :
    x = x 0 • burnsideC135_e F 0 + x 1 • burnsideC135_e F 1 + x 2 • burnsideC135_e F 2 := by
  funext i
  fin_cases i <;> simp

theorem burnsideC135_eq_smul_cross (B : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F))
    (hadd₁ : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hadd₂ : ∀ x y y', B x (y + y') = B x y + B x y')
    (hsmul₁ : ∀ (c : F) x y, B (c • x) y = c • B x y)
    (hsmul₂ : ∀ (c : F) x y, B x (c • y) = c • B x y)
    (halt : ∀ x, B x x = 0)
    (heq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) x y,
      B (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
        (((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ B x y) :
    ∃ μ : F, ∀ x y, B x y = μ • (x ⨯₃ y) := by
  classical
  set e := burnsideC135_e F with he
  have hskew : ∀ x y, B y x = -B x y := by
    intro x y
    have h := halt (x + y)
    rw [hadd₁, hadd₂, hadd₂, halt, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  let Φ : (Fin 3 → F) → (Fin 3 → F) := fun z =>
    z 0 • B (e 1) (e 2) + z 1 • B (e 2) (e 0) + z 2 • B (e 0) (e 1)
  have hΦadd : ∀ z z', Φ (z + z') = Φ z + Φ z' := by
    intro z z'
    simp only [Φ, Pi.add_apply, add_smul]
    abel
  have hB : ∀ x y, B x y = Φ (x ⨯₃ y) := by
    intro x y
    conv_lhs => rw [burnsideC135_vec_eq x, burnsideC135_vec_eq y]
    simp only [hadd₁, hadd₂, hsmul₁, hsmul₂, halt, smul_zero, add_zero, zero_add]
    rw [hskew (e 2) (e 0), hskew (e 0) (e 1), hskew (e 1) (e 2)]
    funext k
    simp only [Φ, cross_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  have hΦγ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) z,
      Φ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ z) = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ Φ z := by
    intro γ z
    have hcross : ∀ x y, Φ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ (x ⨯₃ y)) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ Φ (x ⨯₃ y) := by
      intro x y
      rw [← burnsideC135_cross_dualHom, ← hB, heq, hB]
    have hz : z = (z 0 • e 1) ⨯₃ e 2 + (z 1 • e 2) ⨯₃ e 0 + (z 2 • e 0) ⨯₃ e 1 := by
      funext i
      fin_cases i <;> simp [cross_apply, he]
    conv_lhs => rw [hz]
    conv_rhs => rw [hz]
    simp only [Matrix.mulVec_add, hΦadd, hcross]
  let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := Φ
      map_zero' := by simp [Φ]
      map_add' := hΦadd }
  obtain ⟨μ, hμ⟩ := CFSG.Quasithin.H13.Ch4.exists_smul_of_commute φ fun i j hij b v =>
    hΦγ (Matrix.SpecialLinearGroup.transvection hij b) v
  exact ⟨μ, fun x y => by rw [hB]; exact hμ _⟩

theorem burnsideC135_quad_zero (D : (Fin 3 → F) → (Fin 3 → F))
    (hD : ∀ x y, D (x + y) = D x + D y)
    (h : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) v,
      ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) ⬝ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) =
        v ⬝ᵥ D v) :
    ∀ v, v ⬝ᵥ D v = 0 := by
  classical
  set q : (Fin 3 → F) → F := fun v => v ⬝ᵥ D v with hq
  have hD0 : D 0 = 0 := by
    have := hD 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hconst : ∀ v : Fin 3 → F, v ≠ 0 → q v = q ![1, 0, 0] := by
    intro v hv
    obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.Ch4.SL3Pt.exists_mulVec_e0 hv
    have h1 := h (dualHom g) v
    have e : ((dualHom g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v =
        ![1, 0, 0] := by
      rw [coe_dualHom, Matrix.transpose_transpose, ← hg, Matrix.mulVec_mulVec,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mulVec]
    rw [e] at h1
    exact h1.symm
  have hpol : ∀ x y, q (x + y) = q x + q y + (x ⬝ᵥ D y + y ⬝ᵥ D x) := by
    intro x y
    simp only [hq, hD, add_dotProduct, dotProduct_add]
    ring
  set c := q ![1, 0, 0] with hc
  have hne : ∀ (a b d : F), (a ≠ 0 ∨ b ≠ 0 ∨ d ≠ 0) → (![a, b, d] : Fin 3 → F) ≠ 0 := by
    intro a b d h h0
    rcases h with h | h | h
    · exact h (by simpa using congrFun h0 0)
    · exact h (by simpa using congrFun h0 1)
    · exact h (by simpa using congrFun h0 2)
  have q0 : q ![1, 0, 0] = c := rfl
  have q1 : q ![0, 1, 0] = c := hconst _ (hne _ _ _ (Or.inr (Or.inl one_ne_zero)))
  have q2 : q ![0, 0, 1] = c := hconst _ (hne _ _ _ (Or.inr (Or.inr one_ne_zero)))
  have q01 : q ![1, 1, 0] = c := hconst _ (hne _ _ _ (Or.inl one_ne_zero))
  have q02 : q ![1, 0, 1] = c := hconst _ (hne _ _ _ (Or.inl one_ne_zero))
  have q12 : q ![0, 1, 1] = c := hconst _ (hne _ _ _ (Or.inr (Or.inl one_ne_zero)))
  have q012 : q ![1, 1, 1] = c := hconst _ (hne _ _ _ (Or.inl one_ne_zero))
  have s01 : (![1, 1, 0] : Fin 3 → F) = ![1, 0, 0] + ![0, 1, 0] := by
    funext i; fin_cases i <;> simp
  have s02 : (![1, 0, 1] : Fin 3 → F) = ![1, 0, 0] + ![0, 0, 1] := by
    funext i; fin_cases i <;> simp
  have s12 : (![0, 1, 1] : Fin 3 → F) = ![0, 1, 0] + ![0, 0, 1] := by
    funext i; fin_cases i <;> simp
  have s012 : (![1, 1, 1] : Fin 3 → F) = ![1, 0, 0] + (![0, 1, 0] + ![0, 0, 1]) := by
    funext i; fin_cases i <;> simp
  have h01 := hpol ![1, 0, 0] ![0, 1, 0]
  have h02 := hpol ![1, 0, 0] ![0, 0, 1]
  have h012 := hpol ![1, 0, 0] (![0, 1, 0] + ![0, 0, 1])
  rw [← s01, q01, q0, q1] at h01
  rw [← s02, q02, q0, q2] at h02
  rw [hD, dotProduct_add, add_dotProduct, ← s012, ← s12, q012, q0, q12] at h012
  have hc0 : c = 0 := by linear_combination h012 - h01 - h02
  intro v
  by_cases hv : v = 0
  · rw [hv, hD0, dotProduct_zero]
  · exact (hconst v hv).trans hc0

theorem burnsideC135_eq_cross_of_alt [Fintype F] (hF : Fintype.card F = 2)
    (D : (Fin 3 → F) → (Fin 3 → F)) (hD : ∀ x y, D (x + y) = D x + D y)
    (halt : ∀ v, v ⬝ᵥ D v = 0) :
    ∃ y : Fin 3 → F, ∀ v, D v = y ⨯₃ v := by
  classical
  have h01 : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have h3 : 2 < Fintype.card F :=
      Fintype.two_lt_card_iff.mpr ⟨0, 1, c, zero_ne_one, hc.1.symm, hc.2.symm⟩
    omega
  have hD0 : D 0 = 0 := by
    have := hD 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hsmul : ∀ (c : F) v, D (c • v) = c • D v := by
    intro c v
    rcases h01 c with rfl | rfl
    · rw [zero_smul, zero_smul, hD0]
    · rw [one_smul, one_smul]
  obtain ⟨m, hm⟩ : ∃ m : Fin 3 → Fin 3 → F, ∀ i j, D (Pi.single j 1) i = m i j :=
    ⟨fun i j => D (Pi.single j 1) i, fun _ _ => rfl⟩
  have hd : ∀ i, m i i = 0 := by
    intro i
    have h := halt (Pi.single i 1)
    rw [single_dotProduct, one_mul, hm] at h
    exact h
  have hoff : ∀ i j, m i j + m j i = 0 := by
    intro i j
    have h := halt (Pi.single i 1 + Pi.single j 1)
    rw [hD, add_dotProduct, dotProduct_add, dotProduct_add, single_dotProduct, single_dotProduct,
      single_dotProduct, single_dotProduct, one_mul, one_mul, one_mul, one_mul, hm, hm, hm, hm,
      hd i, hd j] at h
    linear_combination h
  refine ⟨![m 2 1, m 0 2, m 1 0], fun v => ?_⟩
  have hv : D v = v 0 • D (Pi.single 0 1) + v 1 • D (Pi.single 1 1) + v 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [burnsideC135_vec_eq v]
    rw [hD, hD, hsmul, hsmul, hsmul]
  have h10 := hoff 1 0
  have h20 := hoff 2 0
  have h21 := hoff 2 1
  have hm00 := hd 0
  have hm11 := hd 1
  have hm22 := hd 2
  rw [hv]
  funext i
  fin_cases i
  · simp only [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta,
      Fin.isValue]
    linear_combination (v 0) * hm00 + (v 1) * h10
  · simp only [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.mk_one,
      Fin.isValue]
    linear_combination (v 1) * hm11 + (v 2) * h21
  · simp only [cross_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hm, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk,
      Fin.isValue]
    linear_combination (v 0) * h20 + (v 2) * hm22

theorem burnsideC135_weight [Fintype F] (hF : Fintype.card F = 2)
    (D : (Fin 3 → F) → (Fin 3 → F)) (hD : ∀ x y, D (x + y) = D x + D y)
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) F, ∃ y : Fin 3 → F, ∀ v,
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) = D v + y ⨯₃ v) :
    ∃ y₀ : Fin 3 → F, ∀ v, D v = y₀ ⨯₃ v := by
  refine burnsideC135_eq_cross_of_alt hF D hD (burnsideC135_quad_zero D hD fun γ v => ?_)
  obtain ⟨y, hy⟩ := h γ
  have e1 : ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) ⬝ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v) =
      v ⬝ᵥ ((γ : Matrix (Fin 3) (Fin 3) F) *ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ v)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [e1, hy, dotProduct_add, dot_cross_self, add_zero]

end CFSG.ASVolI

end
