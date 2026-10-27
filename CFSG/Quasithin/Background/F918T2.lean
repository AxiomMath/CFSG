module

public import CFSG.Quasithin.Background.F918T0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

theorem isSimpleGroup_statedSL5 : IsSimpleGroup ↥(StatedSL 5 (ZMod 2)) := by
  have := Bridge.isSimple_sl_zmod2 5 (by norm_num)
  exact (specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm.isSimpleGroup

theorem center_statedSL5 {γ : ↥(StatedSL 5 (ZMod 2))} (h : ∀ δ, γ * δ = δ * γ) : γ = 1 := by
  set e := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  have hA : e.symm γ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact (h (e g)).symm
  rw [Bridge.center_sl_zmod2 5, Subgroup.mem_bot] at hA
  rw [← e.apply_symm_apply γ, hA, map_one]

private def altKer : Subgroup ↥(StatedSL 5 (ZMod 2)) where
  carrier := {γ | ∀ B, altMulAct γ B = B}
  one_mem' := altMulAct_one
  mul_mem' {a b} ha hb B := by
    show altMulAct (a * b) B = B
    rw [altMulAct_mul, hb B, ha B]
  inv_mem' {a} ha B := by
    show altMulAct a⁻¹ B = B
    calc altMulAct a⁻¹ B = altMulAct a (altMulAct a⁻¹ B) := (ha _).symm
      _ = B := by rw [← altMulAct_mul, mul_inv_cancel, altMulAct_one]

private theorem altKer_normal : altKer.Normal :=
  ⟨fun a ha g B => by
    show altMulAct (g * a * g⁻¹) B = B
    rw [altMulAct_mul, altMulAct_mul, ha, ← altMulAct_mul, mul_inv_cancel, altMulAct_one]⟩

private noncomputable def tv01 : ↥(StatedSL 5 (ZMod 2)) :=
  specialLinearGroupEquivStatedSL 5 (ZMod 2)
    ⟨Matrix.transvection 0 1 1, Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩

private theorem mat_tv01 : mat tv01 = Matrix.transvection (0 : Fin 5) 1 (1 : ZMod 2) :=
  specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) _

private def alt12 : ↥(altMat 5) :=
  ⟨Matrix.single 1 2 1 + Matrix.single 2 1 1, by
    refine ⟨?_, fun i => ?_⟩
    · rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]
    · fin_cases i <;> simp⟩

private theorem tv01_moves :
    altMulAct tv01 (Multiplicative.ofAdd alt12) ≠ Multiplicative.ofAdd alt12 := by
  intro h
  have h02 := congrArg
    (fun B : Multiplicative ↥(altMat 5) =>
      ((Multiplicative.toAdd B : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2) h
  simp only [coe_toAdd_altMulAct, mat_tv01, toAdd_ofAdd, alt12] at h02
  simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.transvection, Matrix.one_apply,
    Matrix.single_apply] at h02

theorem altMulAct_faithful {γ : ↥(StatedSL 5 (ZMod 2))} (h : ∀ B, altMulAct γ B = B) : γ = 1 := by
  have := isSimpleGroup_statedSL5
  have hγ : γ ∈ altKer := h
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ altKer altKer_normal with hK | hK
  · rw [hK] at hγ
    exact Subgroup.mem_bot.1 hγ
  · have ht : tv01 ∈ altKer := hK ▸ Subgroup.mem_top tv01
    exact absurd (ht (Multiplicative.ofAdd alt12)) tv01_moves

theorem eq_one_of_altMulAct_comm {γ₀ : ↥(StatedSL 5 (ZMod 2))}
    (h : ∀ δ B, altMulAct γ₀ (altMulAct δ B) = altMulAct δ (altMulAct γ₀ B)) : γ₀ = 1 := by
  refine center_statedSL5 fun δ => ?_
  have h1 : (δ * γ₀)⁻¹ * (γ₀ * δ) = 1 := altMulAct_faithful fun B => by
    rw [altMulAct_mul, altMulAct_mul γ₀ δ, h, ← altMulAct_mul δ γ₀, ← altMulAct_mul,
      inv_mul_cancel, altMulAct_one]
  exact inv_mul_eq_one.1 h1 |>.symm

theorem exists_aut_of_ker_le {Λ S : Type} [Group Λ] [Group S] [Finite S] (θ₁ θ₂ : Λ →* S)
    (h₁ : Function.Surjective θ₁) (h₂ : Function.Surjective θ₂) (hk : ∀ l, θ₁ l = 1 → θ₂ l = 1) :
    ∃ α : S ≃* S, ∀ l, α (θ₁ l) = θ₂ l := by
  set α₀ : S →* S := θ₁.liftOfSurjective h₁ ⟨θ₂, fun l hl => hk l hl⟩ with hα₀
  have hα₀θ : ∀ l, α₀ (θ₁ l) = θ₂ l := fun l =>
    θ₁.liftOfRightInverse_comp_apply _ _ ⟨θ₂, fun l hl => hk l hl⟩ l
  have hsurj : Function.Surjective α₀ := fun s => by
    obtain ⟨l, rfl⟩ := h₂ s
    exact ⟨θ₁ l, hα₀θ l⟩
  exact ⟨MulEquiv.ofBijective α₀ ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩, hα₀θ⟩

theorem altMulAct_inner (α : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(StatedSL 5 (ZMod 2)))
    (P : GL (Fin 5) (ZMod 2))
    (hα : ∀ g, mat (α g) = (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) * mat g *
      ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (γ : ↥(StatedSL 5 (ZMod 2))) (B : Multiplicative ↥(altMat 5)) :
    altMulAct (α γ) (altMulAct (CFSG.Quasithin.B5.Ln.ofGL P) B) =
      altMulAct (CFSG.Quasithin.B5.Ln.ofGL P) (altMulAct γ B) := by
  have hc : α γ * B5.Ln.ofGL P = B5.Ln.ofGL P * γ := by
    apply B5.Ln.mat_injective
    simp only [B5.Ln.mat_mul, B5.Ln.mat_ofGL, hα, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [← altMulAct_mul, hc, altMulAct_mul]

private theorem altMulAct_eq_iff (γ : ↥(StatedSL 5 (ZMod 2))) (B : Multiplicative ↥(altMat 5)) :
    altMulAct γ B = B ↔
      mat γ * ((Multiplicative.toAdd B : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        (mat γ)ᵀ = (Multiplicative.toAdd B : ↥(altMat 5)) := by
  constructor
  · intro h
    rw [← coe_toAdd_altMulAct, h]
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [coe_toAdd_altMulAct, h]

private theorem card_fix_altMulAct (E : Subgroup ↥(StatedSL 5 (ZMod 2))) :
    Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct γ B = B} =
      Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B} :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun B =>
    forall₂_congr fun γ _ => altMulAct_eq_iff γ B)

private theorem congr_eq_iff {P Q Y C : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) : P * Y * Pᵀ = C ↔ Y = Q * C * Qᵀ := by
  constructor
  · rintro rfl
    have : Q * (P * Y * Pᵀ) * Qᵀ = (Q * P) * Y * (Q * P)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hQP, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
  · rintro rfl
    have : P * (Q * C * Qᵀ) * Pᵀ = (P * Q) * C * (P * Q)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [this, hPQ, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]

private theorem card_fix_altMulAct_graph (α : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(StatedSL 5 (ZMod 2)))
    (P : GL (Fin 5) (ZMod 2))
    (hα : ∀ g, mat (α g) = (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) * dmat g *
      ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (E : Subgroup ↥(StatedSL 5 (ZMod 2))) :
    Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct (α γ) B = B} =
      Nat.card {B : ↥(altMat 5) //
        ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B} := by
  set Pm : Matrix (Fin 5) (Fin 5) (ZMod 2) := (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hPm
  set Q : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hQ
  have hPQ : Pm * Q = 1 := Units.mul_inv P
  have hQP : Q * Pm = 1 := Units.inv_mul P
  let φ : ↥(altMat 5) ≃ ↥(altMat 5) :=
    { toFun := fun B => ⟨Q * B * Qᵀ, congr_mem_altMat Q B.2⟩
      invFun := fun B => ⟨Pm * B * Pmᵀ, congr_mem_altMat Pm B.2⟩
      left_inv := fun B => Subtype.ext ((congr_eq_iff hPQ hQP).2 rfl)
      right_inv := fun B => Subtype.ext ((congr_eq_iff hQP hPQ).2 rfl) }
  refine Nat.card_congr (Equiv.subtypeEquiv (Multiplicative.toAdd.trans φ) fun B =>
    forall₂_congr fun γ _ => ?_)
  set C : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
    ((Multiplicative.toAdd B : ↥(altMat 5)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) with hC
  show altMulAct (α γ) B = B ↔ dmat γ * (Q * C * Qᵀ) * (dmat γ)ᵀ = Q * C * Qᵀ
  have key : Pm * dmat γ * Q * C * (Pm * dmat γ * Q)ᵀ =
      Pm * (dmat γ * (Q * C * Qᵀ) * (dmat γ)ᵀ) * Pmᵀ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [altMulAct_eq_iff, hα γ, ← hC, key, congr_eq_iff hPQ hQP]

theorem final_graph (hU : D35InspExtSq) (α : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(StatedSL 5 (ZMod 2)))
    (P : GL (Fin 5) (ZMod 2))
    (hα : ∀ g, mat (α g) = (P : Matrix (Fin 5) (Fin 5) (ZMod 2)) * dmat g *
      ((P⁻¹ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (E : Subgroup ↥(StatedSL 5 (ZMod 2))) (hE0 : E ≠ ⊥) (hEab : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hE2 : ∀ g ∈ E, g * g = 1)
    (h1 : 2 ^ 10 ≤ Nat.card E *
      Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct γ B = B})
    (h2 : 2 ^ 10 ≤ Nat.card E *
      Nat.card {B : Multiplicative ↥(altMat 5) // ∀ γ ∈ E, altMulAct (α γ) B = B}) : False := by
  refine hU E hE0 hEab hE2 ⟨?_, ?_⟩
  · rwa [card_fix_altMulAct] at h1
  · rwa [card_fix_altMulAct_graph α P hα] at h2

end CFSG.Quasithin
