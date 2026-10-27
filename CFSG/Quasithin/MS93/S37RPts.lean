module

public import CFSG.Quasithin.MS93.S37RAlg
public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.MS93.S37R

variable {F : Type} [Field F]

@[expose] def mv (t : F × F × F) (x : Fin 2 → F) : Fin 2 → F :=
  ![t.1 * x 0 + t.2.1 * x 1, t.2.1 * x 0 + t.2.2 * x 1]

@[expose] def ktr (x : Fin 2 → F) : F × F × F := (x 1 ^ 2, x 0 * x 1, x 0 ^ 2)

@[expose] def del (y x : Fin 2 → F) : F := y 1 * x 0 + y 0 * x 1

theorem mv_add (t t' : F × F × F) (x : Fin 2 → F) : mv (t + t') x = mv t x + mv t' x := by
  funext i
  fin_cases i <;> simp [mv] <;> ring

theorem mv_smul (c : F) (t : F × F × F) (x : Fin 2 → F) : mv (c • t) x = c • mv t x := by
  funext i
  fin_cases i <;> simp [mv] <;> ring

theorem mv_zero (x : Fin 2 → F) : mv 0 x = 0 := by
  funext i
  fin_cases i <;> simp [mv]

theorem mv_ktr (y x : Fin 2 → F) : mv (ktr y) x = del y x • ![y 1, y 0] := by
  funext i
  fin_cases i <;> simp [mv, ktr, del] <;> ring

variable [CharP F 2]

theorem del_self (x : Fin 2 → F) : del x x = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [del]
  linear_combination x 0 * x 1 * h2

theorem mv_ktr_self (x : Fin 2 → F) : mv (ktr x) x = 0 := by
  rw [mv_ktr, del_self, zero_smul]

theorem eq_smul_ktr {x : Fin 2 → F} (hx : x ≠ 0) {t : F × F × F} (ht : mv t x = 0) :
    ∃ c : F, t = c • ktr x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e0 : t.1 * x 0 + t.2.1 * x 1 = 0 := congrFun ht 0
  have e1 : t.2.1 * x 0 + t.2.2 * x 1 = 0 := congrFun ht 1
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := fun h1 => hx (by funext i; fin_cases i <;> simp [h0, h1])
    rw [h0, mul_zero, zero_add] at e0
    rw [h0, mul_zero, zero_add] at e1
    have hc : t.2.1 = 0 := (mul_eq_zero.1 e0).resolve_right h1
    have hd : t.2.2 = 0 := (mul_eq_zero.1 e1).resolve_right h1
    refine ⟨t.1 / x 1 ^ 2, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · simp [ktr, div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
    · simp [ktr, hc, h0]
    · simp [ktr, hd, h0]
  · refine ⟨t.2.2 / x 0 ^ 2, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
    · simp only [ktr, Prod.smul_fst, smul_eq_mul]
      field_simp
      linear_combination x 0 * e0 - x 1 * e1
    · simp only [ktr, Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
      field_simp
      linear_combination e1 - t.2.2 * x 1 * h2
    · simp only [ktr, Prod.smul_snd, smul_eq_mul]
      field_simp

omit [CharP F 2] in
theorem ktr_ne_zero {x : Fin 2 → F} (hx : x ≠ 0) : ktr x ≠ 0 := by
  intro h
  apply hx
  have h1 : x 1 ^ 2 = 0 := congrArg Prod.fst h
  have h0 : x 0 ^ 2 = 0 := congrArg (fun t => t.2.2) h
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1

omit [CharP F 2] in
theorem del_comm (x y : Fin 2 → F) : del x y = del y x := by
  simp only [del]
  ring

theorem solve2 {y z a : Fin 2 → F} (hD : del y z ≠ 0) :
    ∃ l m : F, l • ![y 1, y 0] + m • ![z 1, z 0] = a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [del] at hD
  refine ⟨(a 0 * z 0 + z 1 * a 1) / (y 1 * z 0 + y 0 * z 1),
    (y 1 * a 1 + a 0 * y 0) / (y 1 * z 0 + y 0 * z 1), ?_⟩
  funext i
  fin_cases i
  · show (a 0 * z 0 + z 1 * a 1) / (y 1 * z 0 + y 0 * z 1) * y 1 +
      (y 1 * a 1 + a 0 * y 0) / (y 1 * z 0 + y 0 * z 1) * z 1 = a 0
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    linear_combination a 1 * y 1 * z 1 * h2
  · show (a 0 * z 0 + z 1 * a 1) / (y 1 * z 0 + y 0 * z 1) * y 0 +
      (y 1 * a 1 + a 0 * y 0) / (y 1 * z 0 + y 0 * z 1) * z 0 = a 1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]
    linear_combination a 0 * y 0 * z 0 * h2

theorem false_of_three [Finite F] (hq : 1 < Nat.card F) {E : AddSubgroup (F × F × F)}
    (hE : Nat.card E ≤ Nat.card F ^ 2) {x₁ x₂ x₃ : Fin 2 → F} (h12 : del x₁ x₂ ≠ 0)
    (h13 : del x₁ x₃ ≠ 0) (h23 : del x₂ x₃ ≠ 0) (hK₁ : ∀ c : F, c • ktr x₁ ∈ E)
    (hK₂ : ∀ c : F, c • ktr x₂ ∈ E) (hK₃ : ∀ c : F, c • ktr x₃ ∈ E) : False := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx₁ : x₁ ≠ 0 := fun h => h12 (by simp [del, h])
  let f : ↥E →+ (Fin 2 → F) :=
    { toFun := fun t => mv t x₁
      map_zero' := mv_zero x₁
      map_add' := fun t t' => mv_add t t' x₁ }
  have hrange : Nat.card f.range = Nat.card F ^ 2 := by
    have htop : f.range = ⊤ := by
      refine eq_top_iff.2 fun a _ => ?_
      obtain ⟨l, m, hlm⟩ := solve2 (a := a) h23
      have ht : (l / del x₂ x₁) • ktr x₂ + (m / del x₃ x₁) • ktr x₃ ∈ E :=
        E.add_mem (hK₂ _) (hK₃ _)
      refine ⟨⟨_, ht⟩, ?_⟩
      show mv _ x₁ = a
      rw [mv_add, mv_smul, mv_smul, mv_ktr, mv_ktr, smul_smul, smul_smul,
        div_mul_cancel₀ _ (by rwa [del_comm] at h12), div_mul_cancel₀ _ (by rwa [del_comm] at h13)]
      exact hlm
    rw [htop, Nat.card_congr (AddEquiv.ofBijective (AddSubgroup.subtype ⊤)
      ⟨Subtype.val_injective, fun y => ⟨⟨y, AddSubgroup.mem_top y⟩, rfl⟩⟩).toEquiv]
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  have hker : Nat.card F ≤ Nat.card f.ker := by
    let g : F → ↥f.ker := fun c => ⟨⟨c • ktr x₁, hK₁ c⟩, by
      show mv (c • ktr x₁) x₁ = 0
      rw [mv_smul, mv_ktr_self, smul_zero]⟩
    have hg : Function.Injective g := fun c c' h => by
      have h' : c • ktr x₁ = c' • ktr x₁ := congrArg (fun t : ↥f.ker => ((t : ↥E) : F × F × F)) h
      exact smul_left_injective F (ktr_ne_zero hx₁) h'
    have : Finite ↥f.ker := Finite.of_injective _ (Subtype.val_injective.comp
      Subtype.val_injective)
    exact Nat.card_le_card_of_injective g hg
  have hcard := AddSubgroup.card_ker_mul_card_range f
  rw [hrange] at hcard
  have hq2 : 0 < Nat.card F ^ 2 := pow_pos (by omega) 2
  have : Nat.card F * Nat.card F ^ 2 ≤ Nat.card F ^ 2 :=
    (Nat.mul_le_mul_right _ hker).trans (hcard.le.trans hE)
  have : Nat.card F ^ 2 * 2 ≤ Nat.card F ^ 2 * 1 := by nlinarith
  omega

omit [CharP F 2] in
theorem exists_ne_zero_ne_one' [Finite F] (hF : 2 < Nat.card F) : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have : Fintype F := Fintype.ofFinite F
  have hs : (Finset.univ : Finset F) ⊆ {0, 1} := fun t _ => by
    by_cases h0 : t = 0
    · simp [h0]
    · simp [h t h0]
  have h1 := Finset.card_le_card hs
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_insert_le (0 : F) {1}
  rw [Finset.card_singleton] at h2
  omega

theorem exists_good [Finite F] (hq : 2 < Nat.card F) {E : AddSubgroup (F × F × F)}
    (hE : Nat.card E ≤ Nat.card F ^ 2)
    (hker : ∀ x : Fin 2 → F, x ≠ 0 → (∃ t ∈ E, t ≠ 0 ∧ mv t x = 0) → ∀ c : F, c • ktr x ∈ E)
    {a : Fin 2 → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) :
    ∃ x : Fin 2 → F, dot x a = c ∧ ∀ t ∈ E, mv t x = 0 → t = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨x₀, hx₀⟩ := exists_dot_eq ha c
  have hx₀' : dot x₀ a = c := by rw [← hx₀]; simp only [dot]; ring
  set d : Fin 2 → F := ![a 1, a 0] with hd
  have hda : dot d a = 0 := by
    simp only [hd, dot, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination a 0 * a 1 * h2
  have hp : ∀ l : F, dot (x₀ + l • d) a = c := fun l => by
    rw [show dot (x₀ + l • d) a = dot x₀ a + l * dot d a by
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring, hda, mul_zero, add_zero,
      hx₀']
  have hdel : ∀ l m : F, del (x₀ + l • d) (x₀ + m • d) = (l + m) * c := fun l m => by
    rw [← hx₀']
    simp only [del, dot, hd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination (x₀ 0 * x₀ 1 + l * m * a 0 * a 1) * h2
  have hne0 : ∀ l : F, x₀ + l • d ≠ 0 := fun l h => hc (by rw [← hp l, h]; simp [dot])
  by_contra hall
  push Not at hall
  have hbad : ∀ l : F, ∀ k : F, k • ktr (x₀ + l • d) ∈ E := fun l => by
    obtain ⟨t, htE, hmv, ht0⟩ := hall (x₀ + l • d) (hp l)
    exact hker _ (hne0 l) ⟨t, htE, ht0, hmv⟩
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one' hq
  have hne : ∀ l m : F, l ≠ m → del (x₀ + l • d) (x₀ + m • d) ≠ 0 := fun l m hlm => by
    rw [hdel]
    refine mul_ne_zero (fun h => hlm ?_) hc
    exact eq_of_add_eq_zero' h
  exact false_of_three (by omega) hE (hne 0 1 zero_ne_one) (hne 0 ω (Ne.symm hω0))
    (hne 1 ω (Ne.symm hω1)) (hbad 0) (hbad 1) (hbad ω)

end CFSG.Quasithin.MS93.S37R
