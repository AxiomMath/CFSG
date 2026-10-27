module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

theorem exists_eq_pow_of_comp_eq_sq {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ψ : F →+* F) (hψ : ∀ x, ψ (ψ x) = x ^ 2) (h3 : 2 < Nat.card F) :
    ∃ a : ℕ, 1 ≤ a ∧ Nat.card F = 2 ^ (2 * a + 1) ∧ ∀ x, ψ x = x ^ 2 ^ (a + 1) := by
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have := Fintype.ofFinite F
  let ψa : F →ₐ[ZMod 2] F :=
    { ψ with
      commutes' := fun r => congrArg (fun f : ZMod 2 →+* F => f r)
        (RingHom.ext_zmod (ψ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)) }
  set φ := FiniteField.frobeniusAlgHom (ZMod 2) F with hφ
  have hφx : ∀ (n : ℕ) (x : F), (φ ^ n) x = x ^ 2 ^ n := by
    intro n x
    rw [AlgHom.coe_pow, hφ, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  obtain ⟨⟨i, _⟩, hψi⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) F).2 ψa
  simp only at hψi
  have hψx : ∀ x, ψ x = x ^ 2 ^ i := fun x => by
    rw [← hφx i x, hψi]
    rfl
  set e := Module.finrank (ZMod 2) F with he
  have hcard : Nat.card F = 2 ^ e := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hord : orderOf φ = e := FiniteField.orderOf_frobeniusAlgHom (ZMod 2) F
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; exact Module.finrank_pos)
  have h2i : φ ^ (2 * i) = φ ^ 1 := by
    ext x
    rw [hφx, hφx, pow_one, ← hψ x, hψx, hψx, ← pow_mul, ← pow_add, two_mul]
  have hmod : 2 * i ≡ 1 [MOD e] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp h2i
  have he2 : 2 ≤ e := by
    by_contra h
    have h' : e ≤ 1 := by omega
    have : 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h'
    omega
  have hodd : ¬ 2 ∣ e := fun h2 => by
    have := Nat.ModEq.of_dvd h2 hmod
    simp [Nat.ModEq, Nat.mul_mod_right] at this
  obtain ⟨a, ha⟩ : ∃ a, e = 2 * a + 1 := ⟨e / 2, by omega⟩
  have ha1 : 1 ≤ a := by omega
  have hcop : Nat.Coprime e 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact hodd
  have hia : i ≡ a + 1 [MOD e] := by
    refine Nat.ModEq.cancel_left_of_coprime (c := 2) hcop ?_
    refine hmod.trans ?_
    rw [show 2 * (a + 1) = 1 + e by omega]
    exact (Nat.add_modEq_right).symm
  refine ⟨a, ha1, by rw [hcard, ha], fun x => ?_⟩
  rw [hψx, ← hφx, ← hφx, hfin.pow_eq_pow_iff_modEq.mpr (hord ▸ hia)]

end CFSG.Quasithin.Ch3E213M.G41.CTwo
