module

public import CFSG.Quasithin.EmptyFaithful.A38c16Mod
public import CFSG.Quasithin.EmptyFaithful.A38c16Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups Matrix
open CFSG.ComponentClassification CFSG.QuasithinUnique.Setup.Family

private noncomputable abbrev tauA : MulAut SL(3, ZMod 2) :=
  CatalogueBGraphForm.slGraphAut 3 (ZMod 2)

private theorem twistMat_tau (u : ZMod 2) (x : SL(3, ZMod 2)) :
    twistMat u (tauA x) = twistMat (u + 1) x := by
  rcases zmod_two_cases u with rfl | rfl
  · rw [twistMat_zero, zero_add, twistMat_one]
    rfl
  · have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h2, twistMat_zero, twistMat_one]
    have : (tauA x)⁻¹ = tauA x⁻¹ := (map_inv tauA x).symm
    rw [this]
    show (((x⁻¹)⁻¹ : SL(3, ZMod 2)) : M3).transpose.transpose = _
    rw [Matrix.transpose_transpose, inv_inv]

theorem outerClass_eq_zero_iff (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    outerClass α = 0 ↔ ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹ := by
  unfold outerClass
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 (by decide), fun h' => absurd h' h⟩

theorem outerClass_eq_one_iff (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    outerClass α = 1 ↔ ¬ ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹ := by
  unfold outerClass
  split_ifs with h
  · exact ⟨fun h1 => absurd h1 (by decide), fun h' => absurd h h'⟩
  · exact ⟨fun _ => h, fun _ => rfl⟩

private theorem slConj_toGL (g : SL(3, ZMod 2)) :
    CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) (Matrix.SpecialLinearGroup.toGL g) =
      MulAut.conj g := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  have h := CatalogueBHigherLinearAction.slConjugation_matrix 3 (ZMod 2)
    (Matrix.SpecialLinearGroup.toGL g) x
  rw [h]
  have e1 : ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) (ZMod 2)) : M3) = (g : M3) := rfl
  have e2 : (((Matrix.SpecialLinearGroup.toGL g : GL (Fin 3) (ZMod 2))⁻¹ :
      GL (Fin 3) (ZMod 2)) : M3) = ((g⁻¹ : SL(3, ZMod 2)) : M3) := by
    rw [← map_inv]; rfl
  rw [e1, e2, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

private theorem aut_cases (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    (∃ g : SL(3, ZMod 2), α = MulAut.conj g) ∨
      (∃ g : SL(3, ZMod 2), α = MulAut.conj g * tauA) := by
  rcases aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
  · left
    obtain ⟨g, rfl⟩ := (slEquivGL 3).surjective A
    exact ⟨g, by rw [hA]; exact slConj_toGL g⟩
  · right
    obtain ⟨g, rfl⟩ := (slEquivGL 3).surjective A
    exact ⟨g, by rw [hA, ← slConj_toGL g]; rfl⟩

private theorem tauA_tauA (x : SL(3, ZMod 2)) : tauA (tauA x) = x := tauA.symm_apply_apply x

private noncomputable def tauPow (c : ZMod 2) : MulAut SL(3, ZMod 2) := if c = 0 then 1 else tauA

private theorem tauPow_zero : tauPow 0 = 1 := by simp [tauPow]
private theorem tauPow_one : tauPow 1 = tauA := by simp [tauPow]

private theorem twistMat_tauPow (u c : ZMod 2) (x : SL(3, ZMod 2)) :
    twistMat u (tauPow c x) = twistMat (u + c) x := by
  rcases zmod_two_cases c with rfl | rfl
  · rw [tauPow_zero, add_zero]; rfl
  · rw [tauPow_one, twistMat_tau]

private theorem exists_conj_tauPow (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    ∃ g : SL(3, ZMod 2), α = MulAut.conj g * tauPow (outerClass α) := by
  by_cases hinn : ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹
  · obtain ⟨g, hg⟩ := hinn
    refine ⟨g, ?_⟩
    rw [(outerClass_eq_zero_iff α).2 ⟨g, hg⟩, tauPow_zero, mul_one]
    exact MulEquiv.ext fun x => (hg x).trans (MulAut.conj_apply g x).symm
  · rw [(outerClass_eq_one_iff α).2 hinn, tauPow_one]
    rcases aut_cases α with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact absurd ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩ hinn
    · exact ⟨g, hg⟩

private def Inn3 (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) : Prop :=
  ∃ g : SL(3, ZMod 2), ∀ x, α x = g * x * g⁻¹

private theorem Inn3.trans {α β : SL(3, ZMod 2) ≃* SL(3, ZMod 2)} (hα : Inn3 α) (hβ : Inn3 β) :
    Inn3 (α.trans β) := by
  obtain ⟨g, hg⟩ := hα
  obtain ⟨h, hh⟩ := hβ
  exact ⟨h * g, fun x => by rw [MulEquiv.trans_apply, hg, hh]; group⟩

private theorem Inn3.symm {α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)} (hα : Inn3 α) : Inn3 α.symm := by
  obtain ⟨g, hg⟩ := hα
  refine ⟨g⁻¹, fun y => ?_⟩
  have h1 : α (α.symm y) = y := α.apply_symm_apply y
  rw [hg] at h1
  rw [inv_inv]
  calc α.symm y = g⁻¹ * (g * α.symm y * g⁻¹) * g := by group
    _ = g⁻¹ * y * g := by rw [h1]

private theorem inn3_or_inn3_tau (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    Inn3 α ∨ Inn3 (α.trans tauA) := by
  rcases aut_cases α with ⟨g, hg⟩ | ⟨g, hg⟩
  · left
    exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩
  · right
    refine ⟨tauA g, fun x => ?_⟩
    rw [MulEquiv.trans_apply, hg, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, tauA_tauA,
      map_inv]

theorem outerClass_trans (α β : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) :
    outerClass (α.trans β) = outerClass α + outerClass β := by
  by_cases hα : Inn3 α <;> by_cases hβ : Inn3 β
  · rw [(outerClass_eq_zero_iff _).2 (hα.trans hβ), (outerClass_eq_zero_iff _).2 hα,
      (outerClass_eq_zero_iff _).2 hβ, add_zero]
  · have hn : ¬ Inn3 (α.trans β) := fun h => by
      apply hβ
      have : β = α.symm.trans (α.trans β) := MulEquiv.ext fun y => by simp
      rw [this]
      exact hα.symm.trans h
    rw [(outerClass_eq_one_iff _).2 hn, (outerClass_eq_zero_iff _).2 hα,
      (outerClass_eq_one_iff _).2 hβ, zero_add]
  · have hn : ¬ Inn3 (α.trans β) := fun h => by
      apply hα
      have : α = (α.trans β).trans β.symm := MulEquiv.ext fun y => by simp
      rw [this]
      exact h.trans hβ.symm
    rw [(outerClass_eq_one_iff _).2 hn, (outerClass_eq_zero_iff _).2 hβ,
      (outerClass_eq_one_iff _).2 hα, add_zero]
  · have hα' : Inn3 (α.trans tauA) := (inn3_or_inn3_tau α).resolve_left hα
    have hβ' : Inn3 (β.trans tauA) := (inn3_or_inn3_tau β).resolve_left hβ
    obtain ⟨h, hh⟩ := hα'
    obtain ⟨h', hh'⟩ := hβ'
    have hβy : ∀ y, β y = tauA h' * tauA y * (tauA h')⁻¹ := by
      intro y
      have := congrArg tauA (hh' y)
      rw [MulEquiv.trans_apply, tauA_tauA] at this
      rw [this, map_mul, map_mul, map_inv]
    have hin : Inn3 (α.trans β) := by
      refine ⟨tauA h' * h, fun x => ?_⟩
      rw [MulEquiv.trans_apply, hβy (α x)]
      have e : tauA (α x) = h * x * h⁻¹ := hh x
      rw [e]; group
    rw [(outerClass_eq_zero_iff _).2 hin, (outerClass_eq_one_iff _).2 hα,
      (outerClass_eq_one_iff _).2 hβ]
    decide

private theorem twistMat_aut (α : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) (u : ZMod 2) :
    ∃ g : SL(3, ZMod 2), ∀ x, twistMat u (α x) =
      twistMat u g * twistMat (u + outerClass α) x * twistMat u g⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_tauPow α
  refine ⟨g, fun x => ?_⟩
  have : α x = g * tauPow (outerClass α) x * g⁻¹ := by
    conv_lhs => rw [hg]
    rfl
  rw [this, twistMat_conj, twistMat_tauPow]

private theorem mat_cancel {A A' B B' Y Z : M3} (hA : A' * A = 1) (hB : B * B' = 1)
    (h : A * Y * B = A * Z * B) : Y = Z := by
  calc Y = (A' * A) * Y * (B * B') := by rw [hA, hB]; simp
    _ = A' * (A * Y * B) * B' := by simp only [Matrix.mul_assoc]
    _ = A' * (A * Z * B) * B' := by rw [h]
    _ = (A' * A) * Z * (B * B') := by simp only [Matrix.mul_assoc]
    _ = Z := by rw [hA, hB]; simp

theorem card_fixSetT_map (α₁ α₂ : SL(3, ZMod 2) ≃* SL(3, ZMod 2)) (t : ZMod 2 × ZMod 2)
    (E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2))) :
    Nat.card (fixSetT t (E.map (MulEquiv.prodCongr α₁ α₂).toMonoidHom)) =
      Nat.card (fixSetT (t + (outerClass α₁, outerClass α₂)) E) := by
  obtain ⟨g₁, h₁⟩ := twistMat_aut α₁ t.1
  obtain ⟨g₂, h₂⟩ := twistMat_aut α₂ t.2
  set Gl : M3 := twistMat t.1 g₁ with hGl
  set Hl : M3 := twistMat t.1 g₁⁻¹ with hHl
  set Gr : M3 := (twistMat t.2 g₂)ᵀ with hGr
  set Hr : M3 := (twistMat t.2 g₂⁻¹)ᵀ with hHr
  have hGH : Gl * Hl = 1 := twistMat_mul_inv _ _
  have hHG : Hl * Gl = 1 := twistMat_inv_mul _ _
  have hGrHr : Gr * Hr = 1 := by
    rw [hGr, hHr, ← Matrix.transpose_mul, twistMat_inv_mul, Matrix.transpose_one]
  have hHrGr : Hr * Gr = 1 := by
    rw [hGr, hHr, ← Matrix.transpose_mul, twistMat_mul_inv, Matrix.transpose_one]
  let Φ : M3 ≃ M3 :=
    { toFun := fun X => Hl * X * Hr
      invFun := fun Y => Gl * Y * Gr
      left_inv := fun X => by
        calc Gl * (Hl * X * Hr) * Gr = (Gl * Hl) * X * (Hr * Gr) := by simp only [Matrix.mul_assoc]
          _ = X := by rw [hGH, hHrGr]; simp
      right_inv := fun Y => by
        calc Hl * (Gl * Y * Gr) * Hr = (Hl * Gl) * Y * (Gr * Hr) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [hHG, hGrHr]; simp }
  have key : ∀ (e : SL(3, ZMod 2) × SL(3, ZMod 2)) (X : M3),
      tensorActT t (α₁ e.1, α₂ e.2) X =
        Gl * tensorActT (t + (outerClass α₁, outerClass α₂)) e (Φ X) * Gr := by
    intro e X
    unfold tensorActT
    rw [h₁, h₂]
    simp only [Matrix.transpose_mul, Prod.fst_add, Prod.snd_add]
    show _ = Gl * (twistMat (t.1 + outerClass α₁) e.1 * (Hl * X * Hr) *
      (twistMat (t.2 + outerClass α₂) e.2)ᵀ) * Gr
    simp only [hGl, hHl, hGr, hHr, Matrix.mul_assoc]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv Φ ?_
  intro X
  have hX : X = Gl * (Φ X) * Gr := (Φ.symm_apply_apply X).symm
  constructor
  · intro hfix e he
    have h1 := hfix (α₁ e.1, α₂ e.2) ⟨e, he, rfl⟩
    rw [key] at h1
    have h2 : Gl * tensorActT (t + (outerClass α₁, outerClass α₂)) e (Φ X) * Gr =
        Gl * (Φ X) * Gr := h1.trans hX
    exact mat_cancel hHG hGrHr h2
  · intro hfix g hg
    obtain ⟨e, he, rfl⟩ := hg
    have h3 := hfix e he
    show tensorActT t (α₁ e.1, α₂ e.2) X = X
    rw [key, h3]
    exact hX.symm

private def mA : M3 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

private def mB : M3 := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

private def uA : SL(3, ZMod 2) := ⟨mA, by decide⟩
private def uB : SL(3, ZMod 2) := ⟨mB, by decide⟩

private theorem uA_mul_self : uA * uA = 1 := Subtype.ext (by decide)
private theorem uB_mul_self : uB * uB = 1 := Subtype.ext (by decide)
private theorem uA_inv : uA⁻¹ = uA := inv_eq_of_mul_eq_one_right uA_mul_self
private theorem uB_inv : uB⁻¹ = uB := inv_eq_of_mul_eq_one_right uB_mul_self

private theorem twistMat_uA (a : ZMod 2) : twistMat a uA = if a = 0 then mA else mAᵀ := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [twistMat_zero]; simp; rfl
  · rw [twistMat_one, uA_inv]; simp; rfl

private theorem twistMat_uB (a : ZMod 2) : twistMat a uB = if a = 0 then mB else mBᵀ := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [twistMat_zero]; simp; rfl
  · rw [twistMat_one, uB_inv]; simp; rfl

private def E1 : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)) := Subgroup.closure {(uA, 1), (uB, 1)}

private def E2 : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)) := Subgroup.closure {(1, uA), (1, uB)}

private theorem fixSetT_E1 (a b : ZMod 2) :
    fixSetT (a, b) E1 = {X | twistMat a uA * X = X ∧ twistMat a uB * X = X} := by
  ext X
  rw [E1, mem_fixSetT_closure]
  simp [tensorActT, twistMat_one_eq]

private theorem fixSetT_E2 (a b : ZMod 2) :
    fixSetT (a, b) E2 = {X | X * (twistMat b uA)ᵀ = X ∧ X * (twistMat b uB)ᵀ = X} := by
  ext X
  rw [E2, mem_fixSetT_closure]
  simp [tensorActT, twistMat_one_eq]

private theorem card_E1_zero : Nat.card ↥{X : M3 | mA * X = X ∧ mB * X = X} = 8 := by
  rw [card_setOf_eq_card_filter]
  unfold mA mB
  set_option maxRecDepth 100000 in decide +kernel

private theorem card_E1_one : Nat.card ↥{X : M3 | mAᵀ * X = X ∧ mBᵀ * X = X} = 64 := by
  rw [card_setOf_eq_card_filter]
  unfold mA mB
  set_option maxRecDepth 100000 in decide +kernel

private theorem card_E2_zero : Nat.card ↥{X : M3 | X * mAᵀ = X ∧ X * mBᵀ = X} = 8 := by
  rw [card_setOf_eq_card_filter]
  unfold mA mB
  set_option maxRecDepth 100000 in decide +kernel

private theorem card_E2_one : Nat.card ↥{X : M3 | X * mA = X ∧ X * mB = X} = 64 := by
  rw [card_setOf_eq_card_filter]
  unfold mA mB
  set_option maxRecDepth 100000 in decide +kernel

private theorem card_fixSetT_E1 (a b : ZMod 2) :
    Nat.card (fixSetT (a, b) E1) = if a = 0 then 8 else 64 := by
  rw [fixSetT_E1, twistMat_uA, twistMat_uB]
  by_cases ha : a = 0
  · simp only [ha, ite_true]; exact card_E1_zero
  · simp only [ha, ite_false]; exact card_E1_one

private theorem card_fixSetT_E2 (a b : ZMod 2) :
    Nat.card (fixSetT (a, b) E2) = if b = 0 then 8 else 64 := by
  rw [fixSetT_E2, twistMat_uA, twistMat_uB]
  by_cases hb : b = 0
  · simp only [hb, ite_true]; exact card_E2_zero
  · simp only [hb, ite_false]
    have e1 : (mAᵀ)ᵀ = mA := Matrix.transpose_transpose _
    have e2 : (mBᵀ)ᵀ = mB := Matrix.transpose_transpose _
    rw [e1, e2]; exact card_E2_one

private theorem distinguish_types (t t' : ZMod 2 × ZMod 2) (h : t ≠ t') :
    ∃ E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)),
      Nat.card (fixSetT t E) ≠ Nat.card (fixSetT t' E) := by
  obtain ⟨a, b⟩ := t
  obtain ⟨a', b'⟩ := t'
  by_cases h1 : a = a'
  · have h2 : b ≠ b' := fun h2 => h (by rw [h1, h2])
    refine ⟨E2, ?_⟩
    rw [card_fixSetT_E2, card_fixSetT_E2]
    rcases zmod_two_cases b with rfl | rfl <;> rcases zmod_two_cases b' with rfl | rfl <;>
      first | exact absurd rfl h2 | decide
  · refine ⟨E1, ?_⟩
    rw [card_fixSetT_E1, card_fixSetT_E1]
    rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases a' with rfl | rfl <;>
      first | exact absurd rfl h1 | decide

theorem sl3OutFacts : SL3OutFacts :=
  ⟨outerClass_trans, fun α => (outerClass_eq_zero_iff α).1, card_fixSetT_map, distinguish_types⟩

end CFSG.Quasithin.A38c16
