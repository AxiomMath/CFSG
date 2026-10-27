module

public import CFSG.Quasithin.Background.SmithB42LnL5Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen

public section

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix

@[expose] def Reduced (A : BM) : Prop := ∀ i, A i < 32

theorem toMat_injective_of_reduced {A B : BM} (hA : Reduced A) (hB : Reduced B)
    (h : toMat A = toMat B) : A = B := by
  funext i
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 5
  · have h1 := congrFun (congrFun h i) ⟨j, hj⟩
    simp only [toMat, Matrix.of_apply] at h1
    by_cases ha : (A i).testBit j <;> by_cases hb : (B i).testBit j <;> simp_all
  · have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
    have hA' : A i < 2 ^ j := lt_of_lt_of_le (h32 ▸ hA i) (Nat.pow_le_pow_right (by norm_num)
      (by omega))
    have hB' : B i < 2 ^ j := lt_of_lt_of_le (h32 ▸ hB i) (Nat.pow_le_pow_right (by norm_num)
      (by omega))
    rw [Nat.testBit_eq_false_of_lt hA', Nat.testBit_eq_false_of_lt hB']

theorem reduced_upB (e : ℕ) : Reduced (upB e) := by
  intro i
  fin_cases i <;> simp only [upB] <;> simp <;> omega

theorem lt_32_ite (c : Bool) {x : ℕ} (hx : x < 32) : (if c = true then x else 0) < 32 := by
  split <;> omega

theorem reduced_bmul {A B : BM} (hB : Reduced B) : Reduced (bmul A B) := by
  intro i
  simp only [bmul, rowMul]
  have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
  rw [h32]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow ?_ ?_) ?_) ?_) ?_ <;> rw [← h32] <;> exact lt_32_ite _ (hB _)

@[expose] def commCnt (x : ℕ) : ℕ :=
  (sqCodes.filter (fun y => bmul (upB x) (upB y) = bmul (upB y) (upB x))).length

set_option maxRecDepth 100000 in
theorem big_count : (sqCodes.filter (fun x => 128 ≤ commCnt x)).length < 128 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mem_sqCodes : ∀ c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2,
    upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ * upMat c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ = 1 →
    codeU c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ ∈ sqCodes := by
  decide +kernel

@[expose] def codeOf (u : G5) : ℕ :=
  codeU ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 1) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 2)
    ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 3) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 4)
    ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 2) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 3)
    ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 4) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 3)
    ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 2 4) ((u : Matrix (Fin 5) (Fin 5) (ZMod 2)) 3 4)

theorem toMat_upB_codeOf {u : G5} (hu : u ∈ Ugrp) :
    toMat (upB (codeOf u)) = (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  rw [codeOf, toMat_upB_codeU]
  exact (eq_upMat hu).symm

theorem codeOf_injective {u w : G5} (hu : u ∈ Ugrp) (hw : w ∈ Ugrp)
    (h : codeOf u = codeOf w) : u = w := by
  apply Subtype.ext
  rw [← toMat_upB_codeOf hu, ← toMat_upB_codeOf hw, h]

theorem codeOf_mem_sqCodes {u : G5} (hu : u ∈ Ugrp) (h2 : u * u = 1) : codeOf u ∈ sqCodes := by
  have hU : IsUpU (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) := hu
  have h2' : (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (u : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.SpecialLinearGroup.coe_one]
  rw [eq_upMat hU] at h2'
  exact mem_sqCodes _ _ _ _ _ _ _ _ _ _ h2'

theorem bmul_comm_of_commute {u w : G5} (hu : u ∈ Ugrp) (hw : w ∈ Ugrp) (h : u * w = w * u) :
    bmul (upB (codeOf u)) (upB (codeOf w)) = bmul (upB (codeOf w)) (upB (codeOf u)) := by
  apply toMat_injective_of_reduced (reduced_bmul (reduced_upB _)) (reduced_bmul (reduced_upB _))
  rw [toMat_bmul, toMat_bmul, toMat_upB_codeOf hu, toMat_upB_codeOf hw,
    ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]

theorem card_lt_of_le_Ugrp {E : Subgroup G5} (hEU : E ≤ Ugrp)
    (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E < 128 := by
  classical
  set S : Finset ℕ := Finset.univ.image fun u : ↥E => codeOf (u : G5) with hS
  have hinj : Function.Injective fun u : ↥E => codeOf (u : G5) := fun u w h =>
    Subtype.ext (codeOf_injective (hEU u.2) (hEU w.2) h)
  have hcard : S.card = Nat.card E := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  by_contra hlt
  push Not at hlt
  have hsub : S ⊆ (sqCodes.filter (fun x => 128 ≤ commCnt x)).toFinset := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨codeOf_mem_sqCodes (hEU u.2) (h2 u u.2), ?_⟩
    have hS' : S ⊆ (sqCodes.filter (fun y => bmul (upB (codeOf (u : G5))) (upB y) =
        bmul (upB y) (upB (codeOf (u : G5))))).toFinset := by
      intro y hy
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨codeOf_mem_sqCodes (hEU w.2) (h2 w w.2),
        decide_eq_true (bmul_comm_of_commute (hEU u.2) (hEU w.2) (hc u u.2 w w.2))⟩
    have h1 := (Finset.card_le_card hS').trans (List.toFinset_card_le _)
    rw [hcard] at h1
    simp only [decide_eq_true_eq]
    exact hlt.trans h1
  have h1 := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [hcard] at h1
  exact absurd (hlt.trans h1) (not_le.2 big_count)

theorem card_le_of_elemAbelian {E : Subgroup G5} (hc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq E h2
  obtain ⟨h, hh⟩ := exists_conj_le_Ugrp hp
  set E' : Subgroup G5 := E.map (MulAut.conj h).toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hE'U : E' ≤ Ugrp := by
    rintro _ ⟨a, ha, rfl⟩
    exact hh a ha
  have hc' : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hc a ha b hb
    calc h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [this]
      _ = h * b * h⁻¹ * (h * a * h⁻¹) := by group
  have h2' : ∀ a ∈ E', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
      _ = 1 := by rw [h2 a ha]; group
  have hlt := card_lt_of_le_Ugrp hE'U hc' h2'
  rw [hcard] at hlt
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hlt ⊢
  have hk6 : k ≤ 6 := by
    by_contra h7
    have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
    _ = 64 := by norm_num

end CFSG.Quasithin.B42Ln
