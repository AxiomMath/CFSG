module

public import CFSG.RankThree.PartOne.SEITZ4.SpPlane

public section

namespace CFSG.RankThree.PartOne.SEITZ4

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def qMat (z a : Fin r ⊕ Fin r → K) (γ : K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + vecMulVec a (spGram r K *ᵥ z) + vecMulVec z (spGram r K *ᵥ a) +
    γ • vecMulVec z (spGram r K *ᵥ z)

theorem qMat_mulVec (z a : Fin r ⊕ Fin r → K) (γ : K) (x : Fin r ⊕ Fin r → K) :
    qMat z a γ *ᵥ x =
      x + spForm r K x z • a + spForm r K x a • z + (γ * spForm r K x z) • z := by
  rw [qMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    op_smul_eq_smul, op_smul_eq_smul, dotProduct_spGram, dotProduct_spGram, smul_smul]

theorem qMat_zero_zero (z : Fin r ⊕ Fin r → K) :
    qMat z (0 : Fin r ⊕ Fin r → K) (0 : K) = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp [Matrix.toLin'_apply, qMat_mulVec]

theorem qMat_zero_vec (z : Fin r ⊕ Fin r → K) (γ : K) :
    qMat z (0 : Fin r ⊕ Fin r → K) γ = spTransMat z γ := by
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp [Matrix.toLin'_apply, qMat_mulVec, spTransMat_mulVec]

section Char2

variable [CharP K 2] {z a a' : Fin r ⊕ Fin r → K} {γ γ' : K}

theorem spForm_comm_char2 (x y : Fin r ⊕ Fin r → K) : spForm r K x y = spForm r K y x :=
  spForm_comm' x y

theorem qMat_mul (ha : spForm r K z a = 0) (ha' : spForm r K z a' = 0) :
    qMat z a γ * qMat z a' γ' = qMat z (a + a') (γ + γ' + spForm r K a' a) := by
  have hz : spForm r K z z = 0 := spForm_self z
  have haz : spForm r K a z = 0 := by rw [spForm_comm_char2]; exact ha
  have ha'z : spForm r K a' z = 0 := by rw [spForm_comm_char2]; exact ha'
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, qMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hz, haz,
    ha'z, mul_zero, add_zero, spForm_comm_char2 z a]
  match_scalars <;> ring

theorem add_self_vec' (x : Fin r ⊕ Fin r → K) : x + x = 0 := by
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem qMat_self (ha : spForm r K z a = 0) : qMat z a γ * qMat z a γ = 1 := by
  rw [qMat_mul ha ha, add_self_vec', CharTwo.add_self_eq_zero, spForm_self, add_zero,
    qMat_zero_zero z]

theorem qMat_add_smul (t : K) : qMat z (a + t • z) γ = qMat z a γ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, qMat_mulVec, map_add, map_smul, smul_eq_mul]
  match_scalars <;> first | ring1 | linear_combination (t * spForm r K x z) * h2

theorem qMat_symplectic (ha : spForm r K z a = 0) (x y : Fin r ⊕ Fin r → K) :
    spForm r K (qMat z a γ *ᵥ x) (qMat z a γ *ᵥ y) = spForm r K x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hz : spForm r K z z = 0 := spForm_self z
  have haa : spForm r K a a = 0 := spForm_self a
  have haz : spForm r K a z = 0 := by rw [spForm_comm_char2]; exact ha
  simp only [qMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hz, haa,
    haz, ha, mul_zero, add_zero, spForm_comm_char2 z y, spForm_comm_char2 a y]
  linear_combination
    (spForm r K x z * spForm r K y a + spForm r K x a * spForm r K y z +
      γ * spForm r K x z * spForm r K y z) * h2

@[expose] noncomputable def qEl (z a : Fin r ⊕ Fin r → K) (γ : K) (ha : spForm r K z a = 0) :
    GL (Fin r ⊕ Fin r) K where
  val := qMat z a γ
  inv := qMat z a γ
  val_inv := qMat_self ha
  inv_val := qMat_self ha

theorem qEl_mem (ha : spForm r K z a = 0) : qEl z a γ ha ∈ StatedSp r K := by
  rw [mem_statedSp_iff_preserves]
  intro x y
  exact qMat_symplectic ha x y

@[expose] noncomputable def qSp (z a : Fin r ⊕ Fin r → K) (γ : K) (ha : spForm r K z a = 0) :
    StatedSp r K :=
  ⟨qEl z a γ ha, qEl_mem ha⟩

theorem coe_qSp (z a : Fin r ⊕ Fin r → K) (γ : K) (ha : spForm r K z a = 0) :
    (((qSp z a γ ha : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = qMat z a γ :=
  rfl

theorem qSp_add_smul (z a : Fin r ⊕ Fin r → K) (γ t : K) (ha : spForm r K z a = 0)
    (ha' : spForm r K z (a + t • z) = 0) : qSp z (a + t • z) γ ha' = qSp z a γ ha :=
  Subtype.ext (Units.ext (by rw [coe_qSp, coe_qSp]; exact qMat_add_smul t))

theorem conj_qSp (n : StatedSp r K) (z a : Fin r ⊕ Fin r → K) (γ : K)
    (hnz : ((n : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ z = z)
    (ha : spForm r K z a = 0)
    (ha' : spForm r K z
      (((n : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) = 0) :
    n * qSp z a γ ha * n⁻¹ = qSp z
      (((n : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) γ ha' := by
  apply Subtype.ext
  apply gl_ext_mulVec
  intro x
  set g : GL (Fin r ⊕ Fin r) K := (n : GL (Fin r ⊕ Fin r) K) with hg
  set y := ((g⁻¹ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x with hy
  have hx : (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ y = x := gl_mulVec_inv_mulVec g x
  have hyz : spForm r K y z = spForm r K x z := by
    have := spForm_mulVec n.2 y z
    rw [hx, hnz] at this
    exact this.symm
  have hya : spForm r K y a = spForm r K x
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) := by
    have := spForm_mulVec n.2 y a
    rw [hx] at this
    exact this.symm
  change ((g * qEl z a γ ha * g⁻¹ : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ x =
    qMat z ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ a) γ *ᵥ x
  rw [gl_mulVec_mul, gl_mulVec_mul, ← hy]
  change (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ (qMat z a γ *ᵥ y) = _
  rw [qMat_mulVec, qMat_mulVec, mulVec_add, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
    mulVec_smul, hx, hnz, hyz, hya]

theorem qMat_eq_spTrans_prod {e w : Fin r ⊕ Fin r → K} {β₁ β₂ : K} (hew : spForm r K e w = 0)
    (hβ : β₁ ≠ 0) :
    qMat (β₂ • e + β₁ • w) (β₁⁻¹ • e) 0 =
      spTransMat (e + w) 1 * spTransMat e 1 * spTransMat w 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hwe : spForm r K w e = 0 := by rw [spForm_comm_char2]; exact hew
  have hee : spForm r K e e = 0 := spForm_self e
  have hww : spForm r K w w = 0 := spForm_self w
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, qMat_mulVec, spTransMat_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hew, hwe,
    hee, hww, mul_zero, add_zero]
  match_scalars <;> field_simp <;> ring_nf
  · linear_combination ((β₂ - β₁) * spForm r K x e) * h2
  · linear_combination (-spForm r K x w) * h2

theorem qMat_three {b₁ b₂ : Fin r ⊕ Fin r → K} (hb₁ : spForm r K z b₁ = 0)
    (hb₂ : spForm r K z b₂ = 0) :
    qMat z b₁ 0 * qMat z b₂ 0 * qMat z (b₁ + b₂) 0 = spTransMat z (spForm r K b₂ b₁) := by
  have hb₁₂ : spForm r K z (b₁ + b₂) = 0 := by rw [map_add, hb₁, hb₂, add_zero]
  rw [qMat_mul hb₁ hb₂, qMat_mul hb₁₂ hb₁₂, add_self_vec', spForm_self, add_zero, zero_add,
    zero_add, add_zero, qMat_zero_vec]

theorem qSp_three (z b₁ b₂ : Fin r ⊕ Fin r → K) (hb₁ : spForm r K z b₁ = 0)
    (hb₂ : spForm r K z b₂ = 0) (hb₁₂ : spForm r K z (b₁ + b₂) = 0) :
    qSp z b₁ 0 hb₁ * qSp z b₂ 0 hb₂ * qSp z (b₁ + b₂) 0 hb₁₂ =
      ⟨spTrans z (spForm r K b₂ b₁), spTrans_mem_statedSp z _⟩ :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_qSp, coe_qSp,
      coe_qSp]
    exact qMat_three hb₁ hb₂))

theorem qSp_shortRoot {e w : Fin r ⊕ Fin r → K} {β₁ β₂ : K} (hew : spForm r K e w = 0)
    (hβ : β₁ ≠ 0) (h : spForm r K (β₂ • e + β₁ • w) (β₁⁻¹ • e) = 0) :
    qSp (β₂ • e + β₁ • w) (β₁⁻¹ • e) 0 h =
      ⟨spTrans (e + w) 1, spTrans_mem_statedSp _ _⟩ * ⟨spTrans e 1, spTrans_mem_statedSp _ _⟩ *
        ⟨spTrans w 1, spTrans_mem_statedSp _ _⟩ :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_qSp]
    exact qMat_eq_spTrans_prod hew hβ))

end Char2

end CFSG.RankThree.PartOne.SEITZ4
