module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylCheck

public section

namespace CFSG.StandardType.SCFourCover.WeylFix

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem r3_cast {a : ℕ} (ha : a < 72) (k : Fin Tag.E6.rank) :
    ((r3 a k : ℕ) : ZMod 3) = ((e6Certificate.root a k : ℤ) : ZMod 3) := by
  have h := roots3OK_eq
  simp only [roots3OK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h a ha k k.2, ZMod.natCast_mod]
  have h9 : (9 : ZMod 3) = 0 := by decide
  simp only [RootCertificate.root, decodeVec, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_one]
  linear_combination h9

private def gZ (x y : Fin 6 → ZMod 3) : ZMod 3 :=
  2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 0 * y 2 +
    x 2 * y 0 + x 1 * y 3 + x 3 * y 1 + x 2 * y 3 + x 3 * y 2 + x 3 * y 4 + x 4 * y 3 +
    x 4 * y 5 + x 5 * y 4)

private theorem iform_cast (x y : Fin Tag.E6.rank → ℤ) :
    ((iform x y : ℤ) : ZMod 3) = gZ (fun k => (x k : ZMod 3)) (fun k => (y k : ZMod 3)) := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hB : Tag.E6.symmetrizedCartan = Tag.cartanE 6 := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]
    rfl
  have key : ∀ x y : Fin 6 → ℤ,
      ((∑ i : Fin 6, ∑ j : Fin 6, x i * Tag.cartanE 6 i j * y j : ℤ) : ZMod 3) =
        gZ (fun k => (x k : ZMod 3)) (fun k => (y k : ZMod 3)) := by
    intro x y
    simp [Fin.sum_univ_six, Tag.cartanE, gZ]
    linear_combination (-((x 0 : ZMod 3) * y 2 + (x 2 : ZMod 3) * y 0 + (x 1 : ZMod 3) * y 3 +
      (x 3 : ZMod 3) * y 1 + (x 2 : ZMod 3) * y 3 + (x 3 : ZMod 3) * y 2 +
      (x 3 : ZMod 3) * y 4 + (x 4 : ZMod 3) * y 3 + (x 4 : ZMod 3) * y 5 +
      (x 5 : ZMod 3) * y 4)) * h3
  simp only [iform, hB]
  exact key x y

private theorem gram3_cast {r s : ℕ} (hr : r < 72) (hs : s < 72) :
    ((gram3 r s : ℕ) : ZMod 3) =
      ((iform (e6Certificate.root r) (e6Certificate.root s) : ℤ) : ZMod 3) := by
  rw [iform_cast]
  have hx : ∀ k : Fin 6, ((e6Certificate.root r k : ℤ) : ZMod 3) = ((r3 r k : ℕ) : ZMod 3) :=
    fun k => (r3_cast hr k).symm
  have hy : ∀ k : Fin 6, ((e6Certificate.root s k : ℤ) : ZMod 3) = ((r3 s k : ℕ) : ZMod 3) :=
    fun k => (r3_cast hs k).symm
  simp only [gZ, hx, hy]
  simp only [gram3, ZMod.natCast_mod]
  push_cast
  rfl


variable {u : WeylGroup Tag.E6} {f : Fin Tag.E6.rank → ℕ}

private theorem gram3_tuple (hf72 : ∀ j, f j < 72)
    (hf : ∀ j, e6Certificate.root (f j) = u • Pi.single j 1) (i j : Fin Tag.E6.rank) :
    ((gram3 (f i) (f j) : ℕ) : ZMod 3) = ((Tag.E6.cartan i j : ℤ) : ZMod 3) := by
  rw [gram3_cast (hf72 i) (hf72 j), hf i, hf j, iform_smul, iform_single_left]
  simp [Pi.single_apply, Tag.symmetrizer]

theorem mem_adjRoots_of_cartan (hf72 : ∀ j, f j < 72)
    (hf : ∀ j, e6Certificate.root (f j) = u • Pi.single j 1) {i j : Fin Tag.E6.rank}
    (hij : Tag.E6.cartan i j = -1) : f j ∈ adjRoots.getD (f i) [] := by
  have hg := gram3_tuple hf72 hf i j
  rw [hij] at hg
  have h2 : gram3 (f i) (f j) = 2 := by
    have hlt : gram3 (f i) (f j) < 3 := Nat.mod_lt _ (by decide)
    have key : ∀ n < 3, ((n : ℕ) : ZMod 3) = ((-1 : ℤ) : ZMod 3) → n = 2 := by decide
    exact key _ hlt hg
  have hne : f i ≠ f j := by
    intro h
    have e : u • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = u • Pi.single j 1 := by
      rw [← hf i, ← hf j, h]
    have e' := congrFun (MulAction.injective u e) i
    have hii : i ≠ j := by
      rintro rfl
      have hd : ∀ i : Fin Tag.E6.rank, Tag.E6.cartan i i = 2 := by decide
      rw [hd] at hij
      exact absurd hij (by decide)
    simp [Pi.single_apply, hii] at e'
  have h := adjOK_eq
  simp only [adjOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  rcases h (f i) (hf72 i) (f j) (hf72 j) with (h | h) | h
  · exact absurd h2 h
  · exact absurd h hne
  · simpa using h

theorem orthB_of_cartan (hf72 : ∀ j, f j < 72)
    (hf : ∀ j, e6Certificate.root (f j) = u • Pi.single j 1) {i j : Fin Tag.E6.rank}
    (hij : Tag.E6.cartan i j = 0) : orthB (f i) (f j) = true := by
  have hg := gram3_tuple hf72 hf i j
  rw [hij] at hg
  have h0 : gram3 (f i) (f j) = 0 := by
    have hlt : gram3 (f i) (f j) < 3 := Nat.mod_lt _ (by decide)
    have key : ∀ n < 3, ((n : ℕ) : ZMod 3) = ((0 : ℤ) : ZMod 3) → n = 0 := by decide
    exact key _ hlt hg
  have h := orthOK_eq
  simp only [orthOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne,
    ne_eq] at h
  rcases h (f i) (hf72 i) (f j) (hf72 j) with h | h
  · exact absurd h0 h
  · exact h

end CFSG.StandardType.SCFourCover.WeylFix

end
