module

public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ4
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

variable {k : Type} [Field k] [CharP k 2]

theorem eq_of_pow_two_pow_eq' {x y : k} {r : ℕ} (h : x ^ 2 ^ r = y ^ 2 ^ r) : x = y := by
  have h1 : (x - y) ^ 2 ^ r = 0 := by rw [sub_pow_char_pow, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero r two_ne_zero) |>.mp h1)

theorem mem_of_pow_two_pow_mem [Finite k] {F : Subfield k} {x : k} {r : ℕ}
    (hx : x ^ 2 ^ r ∈ F) : x ∈ F := by
  let f : F → F := fun y => ⟨(y : k) ^ 2 ^ r, F.pow_mem y.2 _⟩
  have hf : Function.Injective f := fun y y' h =>
    Subtype.ext (eq_of_pow_two_pow_eq' (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x ^ 2 ^ r, hx⟩
  have : (y : k) = x := eq_of_pow_two_pow_eq' (congrArg Subtype.val hy)
  exact this ▸ y.2

namespace CentreSystem

variable (S : CentreSystem k)

theorem chi_chi_of_Q [Finite k] {Q : k → k → Prop} (hQP : ∀ {b c}, Q b c → S.P b c)
    (hQ₀ : Q S.b₀ S.c₀) {h₁ h₂ : k} (hh₁ : h₁ ≠ 0) {r : ℕ}
    (hσ : ∀ {b c}, Q b c → Q (h₁ * c ^ 2 ^ r) (h₂ * (b ^ 2 ^ r) ^ 2)) {b c : k} (h : Q b c) :
    S.chi (b / S.b₀) ∈ S.F0 ∧ S.chi (S.chi (b / S.b₀)) = (b / S.b₀) ^ 2 := by
  set l := b / S.b₀ with hl
  have hc : c = S.c₀ * S.chi l := S.eq_chi (hQP h)
  have hσP := hQP (hσ h)
  have hσ₀ := hQP (hσ hQ₀)
  set A := h₁ * S.c₀ ^ 2 ^ r / S.b₀ with hA
  have hAF : A ∈ S.F0 := S.div_mem_F0 hσ₀
  have hA0 : A ≠ 0 := div_ne_zero (mul_ne_zero hh₁ (pow_ne_zero _ S.c₀_ne)) S.b₀_ne
  have hcA : h₂ * (S.b₀ ^ 2 ^ r) ^ 2 = S.c₀ * S.chi A := S.eq_chi hσ₀
  have hb : b = l * S.b₀ := by rw [hl, div_mul_cancel₀ _ S.b₀_ne]
  have hl' : h₁ * c ^ 2 ^ r / S.b₀ = A * S.chi l ^ 2 ^ r := by
    rw [hc, mul_pow, hA]
    field_simp [S.b₀_ne]
  have hpF : S.chi l ^ 2 ^ r ∈ S.F0 := by
    have h1 := S.div_mem_F0 hσP
    rw [hl'] at h1
    have h2 := S.F0.mul_mem (S.F0.inv_mem hAF) h1
    rwa [← mul_assoc, inv_mul_cancel₀ hA0, one_mul] at h2
  have hχF : S.chi l ∈ S.F0 := mem_of_pow_two_pow_mem hpF
  refine ⟨hχF, ?_⟩
  have hc' := S.eq_chi hσP
  rw [hl', S.chi_mul hAF hpF, S.chi_pow hχF] at hc'
  have key : S.chi A * S.chi (S.chi l) ^ 2 ^ r = S.chi A * (l ^ 2) ^ 2 ^ r := by
    have e : S.c₀ * (S.chi A * S.chi (S.chi l) ^ 2 ^ r) = S.c₀ * (S.chi A * (l ^ 2) ^ 2 ^ r) := by
      rw [← hc', hb, ← mul_assoc, ← hcA]
      ring
    exact mul_left_cancel₀ S.c₀_ne e
  exact eq_of_pow_two_pow_eq' (mul_left_cancel₀ (S.chi_ne_zero hAF hA0) key)

@[expose] noncomputable def F1 : Subfield k where
  carrier := {l | l ∈ S.F0 ∧ S.chi l ∈ S.F0 ∧ S.chi (S.chi l) = l ^ 2}
  zero_mem' := ⟨S.F0.zero_mem, by rw [S.chi_zero]; exact S.F0.zero_mem,
    by rw [S.chi_zero, S.chi_zero, zero_pow two_ne_zero]⟩
  one_mem' := ⟨S.F0.one_mem, by rw [S.chi_one]; exact S.F0.one_mem,
    by rw [S.chi_one, S.chi_one, one_pow]⟩
  add_mem' := by
    rintro l l' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨S.F0.add_mem h1 h1', ?_, ?_⟩
    · rw [S.chi_add h1 h1']
      exact S.F0.add_mem h2 h2'
    · rw [S.chi_add h1 h1', S.chi_add h2 h2', h3, h3', CharTwo.add_sq]
  neg_mem' := by
    rintro l h
    rwa [CharTwo.neg_eq]
  mul_mem' := by
    rintro l l' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨S.F0.mul_mem h1 h1', ?_, ?_⟩
    · rw [S.chi_mul h1 h1']
      exact S.F0.mul_mem h2 h2'
    · rw [S.chi_mul h1 h1', S.chi_mul h2 h2', h3, h3', mul_pow]
  inv_mem' := by
    rintro l ⟨h1, h2, h3⟩
    refine ⟨S.F0.inv_mem h1, ?_, ?_⟩
    · rw [S.chi_inv h1]
      exact S.F0.inv_mem h2
    · rw [S.chi_inv h1, S.chi_inv h2, h3, inv_pow]

theorem mem_F1 {l : k} : l ∈ S.F1 ↔ l ∈ S.F0 ∧ S.chi l ∈ S.F0 ∧ S.chi (S.chi l) = l ^ 2 :=
  Iff.rfl

@[expose] noncomputable def psi : S.F1 →+* S.F1 where
  toFun x := ⟨S.chi x, x.2.2.1, by rw [x.2.2.2]; exact S.F0.pow_mem x.2.1 2,
    by rw [x.2.2.2, S.chi_pow x.2.1]⟩
  map_one' := Subtype.ext S.chi_one
  map_mul' x y := Subtype.ext (S.chi_mul x.2.1 y.2.1)
  map_zero' := Subtype.ext S.chi_zero
  map_add' x y := Subtype.ext (S.chi_add x.2.1 y.2.1)

theorem coe_psi (x : S.F1) : (S.psi x : k) = S.chi x :=
  rfl

theorem psi_psi (x : S.F1) : S.psi (S.psi x) = x ^ 2 :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact x.2.2.2)

end CentreSystem

end CFSG.Quasithin.Ch3E213M.G41.CTwo
