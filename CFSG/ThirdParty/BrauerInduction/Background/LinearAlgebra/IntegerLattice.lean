module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.LinearAlgebra.Quotient.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Local-to-global membership in integer lattices

This file proves an elementwise form of Bernstein's lattice lemma.

If `L` is a finitely generated `ℤ`-module, `A ≤ L`, and an element `x` is
congruent modulo `A` to a multiple of `p ^ N` for every prime `p` and every
`N`, then `x ∈ A`.

The proof passes to `L ⧸ A` and uses the structure theorem for finitely
generated abelian groups.
-/

universe u

namespace Int

lemma eq_zero_of_forall_two_pow_dvd
    {z : ℤ}
    (h : ∀ N : ℕ, (2 : ℤ) ^ N ∣ z) :
    z = 0 := by
  by_contra hz
  have hz_pos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hdvd : (2 : ℕ) ^ z.natAbs ∣ z.natAbs :=
    ofNat_dvd_left.mp (h z.natAbs)
  have hle : (2 : ℕ) ^ z.natAbs ≤ z.natAbs :=
    Nat.le_of_dvd hz_pos hdvd
  have hlt : z.natAbs < (2 : ℕ) ^ z.natAbs :=
    Nat.lt_two_pow_self
  grind only

end Int

namespace ZMod

lemma eq_zero_of_primePow_smul
    (p e : ℕ)
    {x : ZMod (p ^ e)}
    (h : ∃ y : ZMod (p ^ e),
      (((p ^ e : ℕ) : ℤ) • y) = x) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := h
  simp only [Nat.cast_pow, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  rw [← Nat.cast_pow]
  simp only [CharP.cast_eq_zero, zero_mul]

end ZMod

namespace AddCommGroup

/--
A divisible-by-all-prime-powers element of a finitely generated abelian group
is zero.
-/
theorem eq_zero_of_forall_primePow_smul
    {M : Type u} [AddCommGroup M] [Module.Finite ℤ M]
    {x : M}
    (h :
      ∀ p : ℕ, p.Prime →
        ∀ N : ℕ,
          ∃ y : M,
            (((p ^ N : ℕ) : ℤ) • y) = x) :
        x = 0 := by
  letI : AddGroup.FG M :=
    (Module.Finite.iff_addGroup_fg).mp
      (inferInstance : Module.Finite ℤ M)
  obtain ⟨n, ι, instι, p, hp, e, ⟨E⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod M
  apply E.injective
  rw [map_zero]
  apply Prod.ext
  · ext i
    apply Int.eq_zero_of_forall_two_pow_dvd
    intro N
    obtain ⟨y, hy⟩ := h 2 Nat.prime_two N
    refine ⟨(E y).1 i, ?_⟩
    have hy' :
        (((2 ^ N : ℕ) : ℤ) • (E y).1 i) =
          (E x).1 i := by
      simpa using congrArg (fun z => (E z).1 i) hy
    calc
      (E x).1 i
          = (((2 ^ N : ℕ) : ℤ) • (E y).1 i) :=
            hy'.symm
      _ = (2 : ℤ) ^ N * (E y).1 i := by
            simp only [zsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
            simp only [Int.cast_pow, Int.cast_ofNat]

  · apply DFinsupp.ext
    intro i
    obtain ⟨y, hy⟩ := h (p i) (hp i) (e i)
    let n : ℤ := (p i ^ e i : ℕ)

    have hyE : n • E y = E x := by
      rw [← map_zsmul]
      exact congrArg E hy

    have hy2 : n • (E y).2 = (E x).2 := by
      exact congrArg Prod.snd hyE

    have hcoord : n • (E y).2 i = (E x).2 i := congrArg (fun z => z i) hy2
    exact
      ZMod.eq_zero_of_primePow_smul
        (p i) (e i) ⟨(E y).2 i, hcoord⟩


end AddCommGroup

namespace Submodule

/--
Bernstein's lattice lemma, in elementwise form.

If `x` is congruent modulo `A` to a multiple of `p ^ N` for every prime `p`
and every exponent `N`, then `x` belongs to `A`.
-/
theorem mem_of_forall_primePow_congr
    {L : Type u} [AddCommGroup L]
    [Module.Finite ℤ L]
    (A : Submodule ℤ L)
    {x : L}
    (h :
      ∀ p : ℕ, p.Prime →
        ∀ N : ℕ,
          ∃ y : L,
            x - (((p ^ N : ℕ) : ℤ) • y) ∈ A) :
    x ∈ A := by
  have hcofg : A.CoFG :=
    Submodule.CoFG.of_finite
      (R := ℤ) (M := L) (S := A)
  letI : AddGroup.FG (L ⧸ A) :=
    (Module.Finite.iff_addGroup_fg).mp hcofg
  have hquot :
      ∀ p : ℕ, p.Prime →
        ∀ N : ℕ,
          ∃ y : L ⧸ A,
            (((p ^ N : ℕ) : ℤ) • y) =
              Submodule.Quotient.mk x := by
    intro p hp N
    obtain ⟨y, hy⟩ := h p hp N
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    have hz :
        Submodule.Quotient.mk
            (x - (((p ^ N : ℕ) : ℤ) • y)) = (0 : L ⧸ A) :=
      (Submodule.Quotient.mk_eq_zero A).2 hy
    exact (sub_eq_zero.mp hz).symm
  have hzero :
      Submodule.Quotient.mk x = (0 : L ⧸ A) :=
    AddCommGroup.eq_zero_of_forall_primePow_smul hquot

  exact (Submodule.Quotient.mk_eq_zero A).1 hzero

end Submodule
