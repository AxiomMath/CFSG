module

public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37
open scoped Matrix

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

private def transvMat (a b : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, a; 0, 1, b; 0, 0, 1]

private theorem transvMat_mul (a b c d : F) :
    transvMat a b * transvMat c d = transvMat (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private theorem transvMat_zero : transvMat (0 : F) 0 = 1 := by
  rw [Matrix.one_fin_three]
  rfl

private theorem det_transvMat (a b : F) : (transvMat a b).det = 1 := by
  simp [transvMat, Matrix.det_fin_three]

private def transvAct (p : (F × F) × (F × F)) (X : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  transvMat p.1.1 p.1.2 * X * (transvMat p.2.1 p.2.2)ᵀ

private theorem transvAct_transvAct (p q : (F × F) × (F × F)) (X : Matrix (Fin 3) (Fin 3) F) :
    transvAct p (transvAct q X) = transvAct (p + q) X := by
  simp only [transvAct, Prod.fst_add, Prod.snd_add, ← transvMat_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

private theorem transvAct_zero (X : Matrix (Fin 3) (Fin 3) F) : transvAct 0 X = X := by
  simp [transvAct, transvMat_zero]

private theorem transvAct_add (p : (F × F) × (F × F)) (X Y : Matrix (Fin 3) (Fin 3) F) :
    transvAct p (X + Y) = transvAct p X + transvAct p Y := by
  simp [transvAct, Matrix.mul_add, Matrix.add_mul]

private theorem transvAct_apply (p : (F × F) × (F × F)) (X : Matrix (Fin 3) (Fin 3) F)
    (i j : Fin 3) :
    transvAct p X i j = X i j + ![p.1.1, p.1.2, 0] i * X 2 j + ![p.2.1, p.2.2, 0] j * X i 2 +
      ![p.1.1, p.1.2, 0] i * ![p.2.1, p.2.2, 0] j * X 2 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [transvAct, transvMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul,
      dotProduct] <;> ring

private def transvAut (Mm : MatModel L₁ L₂ F 3) (p : (F × F) × (F × F)) : MulAut U where
  toFun v := Mm.β.symm (Multiplicative.ofAdd (transvAct p (Multiplicative.toAdd (Mm.β v))))
  invFun v := Mm.β.symm (Multiplicative.ofAdd (transvAct (-p) (Multiplicative.toAdd (Mm.β v))))
  left_inv v := by simp [transvAct_transvAct, transvAct_zero]
  right_inv v := by simp [transvAct_transvAct, transvAct_zero]
  map_mul' v w := by simp [transvAct_add]

private theorem toAdd_β_transvAut (Mm : MatModel L₁ L₂ F 3) (p : (F × F) × (F × F)) (v : U) :
    Multiplicative.toAdd (Mm.β (transvAut Mm p v)) =
      transvAct p (Multiplicative.toAdd (Mm.β v)) := by
  simp [transvAut]

private def transvHom (Mm : MatModel L₁ L₂ F 3) :
    Multiplicative ((F × F) × (F × F)) →* MulAut U where
  toFun p := transvAut Mm (Multiplicative.toAdd p)
  map_one' := by
    ext v
    apply Mm.β.injective
    apply Multiplicative.toAdd.injective
    simp [toAdd_β_transvAut, transvAct_zero]
  map_mul' p q := by
    ext v
    apply Mm.β.injective
    apply Multiplicative.toAdd.injective
    simp [toAdd_β_transvAut, transvAct_transvAct]

private theorem transvHom_apply (Mm : MatModel L₁ L₂ F 3)
    (p : Multiplicative ((F × F) × (F × F))) :
    transvHom Mm p = transvAut Mm (Multiplicative.toAdd p) := rfl

private theorem transvAut_injective (Mm : MatModel L₁ L₂ F 3) {p q : (F × F) × (F × F)}
    (h : transvAut Mm p = transvAut Mm q) : p = q := by
  have key : ∀ i j, transvAct p !![0, 0, 0; 0, 0, 0; 0, 0, 1] i j =
      transvAct q !![0, 0, 0; 0, 0, 0; 0, 0, 1] i j := by
    intro i j
    have := congrArg (fun g : MulAut U => Multiplicative.toAdd (Mm.β
      (g (Mm.β.symm (Multiplicative.ofAdd !![0, 0, 0; 0, 0, 0; 0, 0, 1])))) i j) h
    simpa only [toAdd_β_transvAut, MulEquiv.apply_symm_apply, toAdd_ofAdd] using this
  obtain ⟨⟨a, b⟩, a', b'⟩ := p
  obtain ⟨⟨c, d⟩, c', d'⟩ := q
  have h02 := key 0 2
  have h12 := key 1 2
  have h20 := key 2 0
  have h21 := key 2 1
  simp [transvAct_apply] at h02 h12 h20 h21
  simp [h02, h12, h20, h21]

private theorem transvAut_mem_sup (Mm : MatModel L₁ L₂ F 3)
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ k, Mm.R₂ k = g)
    (p : (F × F) × (F × F)) : transvAut Mm p ∈ L₁ ⊔ L₂ := by
  have hne : ∀ a b : F, (transvMat a b).det ≠ 0 := fun a b => by
    rw [det_transvMat]
    exact one_ne_zero
  obtain ⟨l, hl⟩ := hR₁ (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hne p.1.1 p.1.2))
    (by simpa using det_transvMat p.1.1 p.1.2)
  obtain ⟨k, hk⟩ := hR₂ (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hne p.2.1 p.2.2))
    (by simpa using det_transvMat p.2.1 p.2.2)
  have : transvAut Mm p = (l : MulAut U) * (k : MulAut U) := by
    ext v
    apply Mm.β.injective
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, Mm.act₁, Mm.act₂, hl, hk, toAdd_β_transvAut]
    simp [transvAct, Matrix.mul_assoc]
  rw [this]
  exact Subgroup.mul_mem_sup l.2 k.2

private theorem mem_fixV_range_transvHom (Mm : MatModel L₁ L₂ F 3) (v : U) :
    v ∈ fixV (transvHom Mm).range ↔
      Multiplicative.toAdd (Mm.β v) 0 2 = 0 ∧ Multiplicative.toAdd (Mm.β v) 1 2 = 0 ∧
      Multiplicative.toAdd (Mm.β v) 2 0 = 0 ∧ Multiplicative.toAdd (Mm.β v) 2 1 = 0 ∧
      Multiplicative.toAdd (Mm.β v) 2 2 = 0 := by
  rw [mem_fixV]
  constructor
  · intro h
    have hp : ∀ p : (F × F) × (F × F), ∀ i j,
        transvAct p (Multiplicative.toAdd (Mm.β v)) i j = Multiplicative.toAdd (Mm.β v) i j := by
      intro p i j
      have := congrArg (fun w => Multiplicative.toAdd (Mm.β w) i j)
        (h (transvHom Mm (Multiplicative.ofAdd p)) ⟨_, rfl⟩)
      simpa only [transvHom_apply, toAdd_β_transvAut, toAdd_ofAdd] using this
    have a1 := hp ((1, 0), (0, 0)) 0 0
    have a2 := hp ((1, 0), (0, 0)) 0 1
    have a3 := hp ((1, 0), (0, 0)) 0 2
    have b1 := hp ((0, 0), (1, 0)) 0 0
    have b2 := hp ((0, 0), (1, 0)) 1 0
    simp [transvAct_apply] at a1 a2 a3 b1 b2
    exact ⟨b1, b2, a1, a2, a3⟩
  · rintro ⟨h02, h12, h20, h21, h22⟩ _ ⟨p, rfl⟩
    apply Mm.β.injective
    apply Multiplicative.toAdd.injective
    ext i j
    rw [transvHom_apply, toAdd_β_transvAut, transvAct_apply]
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, h22]

private def edgeHom (Mm : MatModel L₁ L₂ F 3) : U →* Multiplicative (F × F × F × F × F) where
  toFun v := Multiplicative.ofAdd
    (Multiplicative.toAdd (Mm.β v) 0 2, Multiplicative.toAdd (Mm.β v) 1 2,
      Multiplicative.toAdd (Mm.β v) 2 0, Multiplicative.toAdd (Mm.β v) 2 1,
      Multiplicative.toAdd (Mm.β v) 2 2)
  map_one' := by simp
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    simp

private theorem ker_edgeHom (Mm : MatModel L₁ L₂ F 3) :
    (edgeHom Mm).ker = fixV (transvHom Mm).range := by
  ext v
  rw [MonoidHom.mem_ker, mem_fixV_range_transvHom]
  simp [edgeHom]

private theorem edgeHom_surjective (Mm : MatModel L₁ L₂ F 3) :
    Function.Surjective (edgeHom Mm) := by
  intro y
  refine ⟨Mm.β.symm (Multiplicative.ofAdd
    !![0, 0, (Multiplicative.toAdd y).1; 0, 0, (Multiplicative.toAdd y).2.1;
      (Multiplicative.toAdd y).2.2.1, (Multiplicative.toAdd y).2.2.2.1,
      (Multiplicative.toAdd y).2.2.2.2]), ?_⟩
  apply Multiplicative.toAdd.injective
  simp [edgeHom]

private def cornerSub (Mm : MatModel L₁ L₂ F 3) : Subgroup U where
  carrier := {v | Multiplicative.toAdd (Mm.β v) 2 2 = 0}
  one_mem' := by simp
  mul_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    simp [hv, hw]
  inv_mem' {v} hv := by
    simp only [Set.mem_setOf_eq] at hv ⊢
    simp [hv]

private theorem sq_eq_one_param (p : Multiplicative ((F × F) × (F × F))) : p ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  ext <;> simp [CharTwo.add_self_eq_zero]

theorem exists_opt_three (Mm : MatModel L₁ L₂ F 3)
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ∃ k, Mm.R₂ k = g)
    (hF : Nat.card F = 2) :
    ∃ B : Subgroup (MulAut U), B ≤ L₁ ⊔ L₂ ∧ B ≠ ⊥ ∧ IsElemAbelian2 B ∧ commSeries B 3 = ⊥ ∧
      rk B = 4 ∧ rkIdx (fixV B) = 5 := by
  have hinj : Function.Injective (transvHom Mm) := fun p q h =>
    Multiplicative.toAdd.injective (transvAut_injective Mm h)
  have hcard : Nat.card (transvHom Mm).range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    show Nat.card ((F × F) × (F × F)) = 16
    rw [Nat.card_prod, Nat.card_prod, hF]
  refine ⟨(transvHom Mm).range, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact transvAut_mem_sup Mm hR₁ hR₂ _
  · intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨p, rfl⟩
    rw [← map_pow, sq_eq_one_param, map_one]
  · have hW₁ : commSub ⊤ (transvHom Mm).range ≤ cornerSub Mm := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨_, ⟨p, rfl⟩, w, -, rfl⟩
      show Multiplicative.toAdd (Mm.β (transvHom Mm p w * w⁻¹)) 2 2 = 0
      simp [transvHom_apply, toAdd_β_transvAut, transvAct_apply]
    have hW₂ : commSub (cornerSub Mm) (transvHom Mm).range ≤ fixV (transvHom Mm).range := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨_, ⟨p, rfl⟩, w, hw, rfl⟩
      have hw' : Multiplicative.toAdd (Mm.β w) 2 2 = 0 := hw
      rw [SetLike.mem_coe, mem_fixV_range_transvHom]
      simp [transvHom_apply, toAdd_β_transvAut, transvAct_apply, hw']
    show commSub (commSub (commSub ⊤ (transvHom Mm).range) (transvHom Mm).range)
      (transvHom Mm).range = ⊥
    rw [eq_bot_iff]
    calc commSub (commSub (commSub ⊤ (transvHom Mm).range) (transvHom Mm).range)
          (transvHom Mm).range
        ≤ commSub (fixV (transvHom Mm).range) (transvHom Mm).range :=
          commSub_mono ((commSub_mono hW₁ le_rfl).trans hW₂) le_rfl
      _ = ⊥ := commSub_eq_bot_iff.mpr le_rfl
  · rw [rk, hcard, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  · rw [rkIdx, ← ker_edgeHom Mm, Subgroup.index_ker,
      MonoidHom.range_eq_top_of_surjective _ (edgeHom_surjective Mm), Subgroup.card_top]
    show padicValNat 2 (Nat.card (F × F × F × F × F)) = 5
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_prod, hF,
      show (2 * (2 * (2 * (2 * 2))) : ℕ) = 2 ^ 5 by norm_num, padicValNat.prime_pow]

end CFSG.Quasithin.RonanD37
