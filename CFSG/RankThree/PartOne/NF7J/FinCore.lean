module

public import CFSG.RankThree.PartOne.NF7J.OctNC
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.RankThree.PartOne.NF7J

abbrev M32 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def mk32 (n : ℕ) : M32 :=
  Matrix.of fun i j => (((n >>> (3 * i.val + j.val)) % 2 : ℕ) : ZMod 2)

@[expose] def det3 (M : M32) : ZMod 2 :=
  M 0 0 * M 1 1 * M 2 2 + M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
    M 0 2 * M 1 0 * M 2 1 + M 0 2 * M 1 1 * M 2 0

theorem det3_eq : ∀ M : M32, M.det = det3 M := by decide +kernel

@[expose] def IsOrd4 (g : M32) : Prop := det3 g = 1 ∧ g * g ≠ 1 ∧ g ^ 4 = 1

instance : DecidablePred IsOrd4 := fun g => by unfold IsOrd4; infer_instance

@[expose] def octCode : Fin 8 → ℕ := ![254, 443, 103, 188, 92, 116, 122, 460]

@[expose] def octCls : Fin 8 → ℕ := ![0, 0, 1, 1, 2, 2, 3, 3]

@[expose] def octInv : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

@[expose] def oct (i : Fin 8) : M32 := mk32 (octCode i)

theorem oct_isOrd4 : ∀ i, IsOrd4 (oct i) := by decide +kernel

theorem oct_inv : ∀ i, oct (octInv i) = oct i ^ 3 := by decide +kernel

theorem octCls_inv : ∀ i, octCls (octInv i) = octCls i := by decide

theorem octCls_eq : ∀ i j, octCls i = octCls j → j = i ∨ j = octInv i := by decide

structure OctHyp (N : M32 → M32 → Prop) (p : Fin 8 → Fin 8) : Prop where
  cls_mod : ∀ i, (p i).val % 4 = octCls i
  inv_pos : ∀ i, p (octInv i) = p i + 4
  wagner : ∀ i j, N (oct i) (oct j) ↔ OctNC (p i) (p j)
  j1 : ∀ i j k, p j = p i + 3 → (p k = p i + 1 ∨ p k = p i + 2) → ∀ h : M32, IsOrd4 h →
    ¬ N h (oct i) → ¬ N h (oct j) → ¬ N h (oct k)

namespace OctHyp

variable {N : M32 → M32 → Prop} {p : Fin 8 → Fin 8}

theorem inj (hO : OctHyp N p) : Function.Injective p := by
  intro i j hij
  have h1 : octCls i = octCls j := by rw [← hO.cls_mod, ← hO.cls_mod, hij]
  rcases octCls_eq i j h1 with h | h
  · exact h.symm
  · exfalso
    rw [h, hO.inv_pos] at hij
    have h4 : (4 : Fin 8) = 0 := by
      have := congrArg (fun x => x - p i) hij
      simpa using this.symm
    exact absurd h4 (by decide)

theorem c6 (hO : OctHyp N p) (i j : Fin 8) (hij : (octCls i + octCls j) % 2 = 1) :
    (N (oct i) (oct j) ∨ N (oct i) (oct (octInv j))) ∧
      ¬ (N (oct i) (oct j) ∧ N (oct i) (oct (octInv j))) := by
  have h1 := hO.cls_mod i
  have h2 := hO.cls_mod j
  have h3 : ((p i).val + (p j).val) % 2 = 1 := by omega
  rw [hO.wagner, hO.wagner, hO.inv_pos]
  exact octNC_c6 (p i) (p j) h3

theorem c7 (hO : OctHyp N p) (i j k : Fin 8) (_hji : j ≠ i) (hjinv : j ≠ octInv i) (hki : k ≠ i)
    (hkj : k ≠ j) (hij : N (oct i) (oct j)) (hki' : ¬ N (oct k) (oct i)) (hkj' : ¬ N (oct k) (oct j))
    (h : M32) (hh : IsOrd4 h) (hhi : ¬ N h (oct i)) (hhj : ¬ N h (oct j)) : ¬ N h (oct k) := by
  rw [hO.wagner] at hij hki' hkj'
  have hy : p j ≠ p i + 4 := fun e => hjinv (hO.inj (e.trans (hO.inv_pos i).symm))
  have hz1 : p k ≠ p i := fun e => hki (hO.inj e)
  have hz2 : p k ≠ p j := fun e => hkj (hO.inj e)
  rcases octNC_c7 (p i) (p j) (p k) hij hy hz1 hz2 hki' hkj' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hO.j1 i j k e1 e2 h hh hhi hhj
  · exact hO.j1 j i k e1 e2 h hh hhj hhi

end OctHyp

@[expose] def chk (x y h rx ry : ℕ) (e : Bool) : Bool :=
  decide (IsOrd4 (mk32 x)) && decide (IsOrd4 (mk32 y)) && decide (IsOrd4 (mk32 rx)) &&
    decide (IsOrd4 (mk32 ry)) && decide (det3 (mk32 h) = 1) &&
    (if e then decide (IsOrd4 (mk32 rx ^ 3)) && decide (IsOrd4 (mk32 ry ^ 3)) &&
        decide (mk32 h * mk32 rx ^ 3 = mk32 x * mk32 h) && decide (mk32 h * mk32 ry ^ 3 = mk32 y * mk32 h)
      else decide (mk32 h * mk32 rx = mk32 x * mk32 h) && decide (mk32 h * mk32 ry = mk32 y * mk32 h))

theorem atom_iff {N : M32 → M32 → Prop}
    (hconj : ∀ h g g' g₁ g₁' : M32, det3 h = 1 → IsOrd4 g → IsOrd4 g' → h * g = g₁ * h →
      h * g' = g₁' * h → (N g g' ↔ N g₁ g₁'))
    (hinv : ∀ g g', IsOrd4 g → IsOrd4 g' → (N g g' ↔ N (g ^ 3) (g' ^ 3)))
    {x y h rx ry : ℕ} {e : Bool} (hc : chk x y h rx ry e = true) :
    N (mk32 x) (mk32 y) ↔ N (mk32 rx) (mk32 ry) := by
  cases e
  · simp only [chk, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hx, hy⟩, hrx⟩, hry⟩, hh⟩, h1, h2⟩ := hc
    exact (hconj (mk32 h) (mk32 rx) (mk32 ry) (mk32 x) (mk32 y) hh hrx hry h1 h2).symm
  · simp only [chk, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hx, hy⟩, hrx⟩, hry⟩, hh⟩, ⟨⟨⟨hrx3, hry3⟩, h1⟩, h2⟩⟩ := hc
    exact ((hinv _ _ hrx hry).trans
      (hconj (mk32 h) _ _ (mk32 x) (mk32 y) hh hrx3 hry3 h1 h2)).symm

theorem core_false (N : M32 → M32 → Prop)
    (hsymm : ∀ g g' : M32, IsOrd4 g → IsOrd4 g' → N g g' → N g' g)
    (hconj : ∀ h g g' g₁ g₁' : M32, det3 h = 1 → IsOrd4 g → IsOrd4 g' → h * g = g₁ * h →
      h * g' = g₁' * h → (N g g' ↔ N g₁ g₁'))
    (hinv : ∀ g g' : M32, IsOrd4 g → IsOrd4 g' → (N g g' ↔ N (g ^ 3) (g' ^ 3)))
    (p : Fin 8 → Fin 8) (hO : OctHyp N p)
    (hF2 : ¬ N (mk32 254) (mk32 239) ∨ ¬ N (mk32 254) (mk32 351)) : False := by
  have i2 : N (mk32 103) (mk32 122) → ¬N (mk32 116) (mk32 103) → ¬N (mk32 116) (mk32 122) → ¬N (mk32 169) (mk32 103) → ¬N (mk32 169) (mk32 122) → ¬N (mk32 169) (mk32 116) :=
    fun a b c d e => hO.c7 2 6 5 (by decide) (by decide) (by decide) (by decide) a b c (mk32 169) (by decide +kernel) d e
  have i3 : N (mk32 103) (mk32 122) → ¬N (mk32 92) (mk32 103) → ¬N (mk32 92) (mk32 122) → ¬N (mk32 86) (mk32 103) → ¬N (mk32 86) (mk32 122) → ¬N (mk32 86) (mk32 92) :=
    fun a b c d e => hO.c7 2 6 4 (by decide) (by decide) (by decide) (by decide) a b c (mk32 86) (by decide +kernel) d e
  have i4 : N (mk32 86) (mk32 92) → N (mk32 92) (mk32 86) := hsymm _ _ (by decide +kernel) (by decide +kernel)
  have i5 : N (mk32 86) (mk32 163) → N (mk32 163) (mk32 86) := hsymm _ _ (by decide +kernel) (by decide +kernel)
  have i6 : N (mk32 254) (mk32 103) → ¬N (mk32 122) (mk32 254) → ¬N (mk32 122) (mk32 103) → ¬N (mk32 169) (mk32 254) → ¬N (mk32 169) (mk32 103) → ¬N (mk32 169) (mk32 122) :=
    fun a b c d e => hO.c7 0 2 6 (by decide) (by decide) (by decide) (by decide) a b c (mk32 169) (by decide +kernel) d e
  have i7 : (N (mk32 254) (mk32 103) ∨ N (mk32 254) (mk32 188)) ∧ ¬(N (mk32 254) (mk32 103) ∧ N (mk32 254) (mk32 188)) :=
    hO.c6 0 2 (by decide)
  have i8 : (N (mk32 103) (mk32 254) ∨ N (mk32 103) (mk32 443)) ∧ ¬(N (mk32 103) (mk32 254) ∧ N (mk32 103) (mk32 443)) :=
    hO.c6 2 0 (by decide)
  have i9 : N (mk32 103) (mk32 122) → ¬N (mk32 92) (mk32 103) → ¬N (mk32 92) (mk32 122) → ¬N (mk32 158) (mk32 103) → ¬N (mk32 158) (mk32 122) → ¬N (mk32 158) (mk32 92) :=
    fun a b c d e => hO.c7 2 6 4 (by decide) (by decide) (by decide) (by decide) a b c (mk32 158) (by decide +kernel) d e
  have i10 : N (mk32 254) (mk32 103) → ¬N (mk32 92) (mk32 254) → ¬N (mk32 92) (mk32 103) → ¬N (mk32 86) (mk32 254) → ¬N (mk32 86) (mk32 103) → ¬N (mk32 86) (mk32 92) :=
    fun a b c d e => hO.c7 0 2 4 (by decide) (by decide) (by decide) (by decide) a b c (mk32 86) (by decide +kernel) d e
  have i11 : N (mk32 254) (mk32 188) → ¬N (mk32 460) (mk32 254) → ¬N (mk32 460) (mk32 188) → ¬N (mk32 358) (mk32 254) → ¬N (mk32 358) (mk32 188) → ¬N (mk32 358) (mk32 460) :=
    fun a b c d e => hO.c7 0 3 7 (by decide) (by decide) (by decide) (by decide) a b c (mk32 358) (by decide +kernel) d e
  have i12 : N (mk32 103) (mk32 443) → ¬N (mk32 122) (mk32 103) → ¬N (mk32 122) (mk32 443) → ¬N (mk32 285) (mk32 103) → ¬N (mk32 285) (mk32 443) → ¬N (mk32 285) (mk32 122) :=
    fun a b c d e => hO.c7 2 1 6 (by decide) (by decide) (by decide) (by decide) a b c (mk32 285) (by decide +kernel) d e
  have i13 : N (mk32 254) (mk32 92) → ¬N (mk32 122) (mk32 254) → ¬N (mk32 122) (mk32 92) → ¬N (mk32 212) (mk32 254) → ¬N (mk32 212) (mk32 92) → ¬N (mk32 212) (mk32 122) :=
    fun a b c d e => hO.c7 0 4 6 (by decide) (by decide) (by decide) (by decide) a b c (mk32 212) (by decide +kernel) d e
  have i14 : N (mk32 103) (mk32 122) → ¬N (mk32 116) (mk32 103) → ¬N (mk32 116) (mk32 122) → ¬N (mk32 86) (mk32 103) → ¬N (mk32 86) (mk32 122) → ¬N (mk32 86) (mk32 116) :=
    fun a b c d e => hO.c7 2 6 5 (by decide) (by decide) (by decide) (by decide) a b c (mk32 86) (by decide +kernel) d e
  have a0 : N (mk32 254) (mk32 239) ↔ N (mk32 86) (mk32 103) :=
    atom_iff hconj hinv (x := 254) (y := 239) (h := 318) (rx := 86) (ry := 103) (e := false) (by decide +kernel)
  have a1 : N (mk32 254) (mk32 351) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 254) (y := 351) (h := 318) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  have a2 : N (mk32 103) (mk32 122) ↔ N (mk32 86) (mk32 107) :=
    atom_iff hconj hinv (x := 103) (y := 122) (h := 281) (rx := 86) (ry := 107) (e := false) (by decide +kernel)
  have a3 : N (mk32 116) (mk32 103) ↔ N (mk32 86) (mk32 163) :=
    atom_iff hconj hinv (x := 116) (y := 103) (h := 477) (rx := 86) (ry := 163) (e := false) (by decide +kernel)
  have a4 : N (mk32 116) (mk32 122) ↔ N (mk32 86) (mk32 163) :=
    atom_iff hconj hinv (x := 116) (y := 122) (h := 461) (rx := 86) (ry := 163) (e := false) (by decide +kernel)
  have a5 : N (mk32 169) (mk32 103) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 169) (y := 103) (h := 266) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  have a6 : N (mk32 169) (mk32 122) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 169) (y := 122) (h := 410) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a7 : N (mk32 169) (mk32 116) ↔ N (mk32 86) (mk32 165) :=
    atom_iff hconj hinv (x := 169) (y := 116) (h := 266) (rx := 86) (ry := 165) (e := false) (by decide +kernel)
  have a8 : N (mk32 92) (mk32 103) ↔ N (mk32 86) (mk32 165) :=
    atom_iff hconj hinv (x := 92) (y := 103) (h := 335) (rx := 86) (ry := 165) (e := false) (by decide +kernel)
  have a9 : N (mk32 92) (mk32 122) ↔ N (mk32 86) (mk32 165) :=
    atom_iff hconj hinv (x := 92) (y := 122) (h := 351) (rx := 86) (ry := 165) (e := false) (by decide +kernel)
  have a11 : N (mk32 86) (mk32 122) ↔ N (mk32 86) (mk32 103) :=
    atom_iff hconj hinv (x := 86) (y := 122) (h := 84) (rx := 86) (ry := 103) (e := true) (by decide +kernel)
  have a13 : N (mk32 92) (mk32 86) ↔ N (mk32 86) (mk32 163) :=
    atom_iff hconj hinv (x := 92) (y := 86) (h := 501) (rx := 86) (ry := 163) (e := false) (by decide +kernel)
  have a14 : N (mk32 163) (mk32 86) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 163) (y := 86) (h := 494) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a15 : N (mk32 254) (mk32 103) ↔ N (mk32 86) (mk32 163) :=
    atom_iff hconj hinv (x := 254) (y := 103) (h := 107) (rx := 86) (ry := 163) (e := false) (by decide +kernel)
  have a16 : N (mk32 122) (mk32 254) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 122) (y := 254) (h := 419) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a17 : N (mk32 122) (mk32 103) ↔ N (mk32 86) (mk32 107) :=
    atom_iff hconj hinv (x := 122) (y := 103) (h := 305) (rx := 86) (ry := 107) (e := false) (by decide +kernel)
  have a18 : N (mk32 169) (mk32 254) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 169) (y := 254) (h := 114) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  have a19 : N (mk32 254) (mk32 188) ↔ N (mk32 86) (mk32 165) :=
    atom_iff hconj hinv (x := 254) (y := 188) (h := 107) (rx := 86) (ry := 165) (e := false) (by decide +kernel)
  have a20 : N (mk32 103) (mk32 254) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 103) (y := 254) (h := 395) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a21 : N (mk32 103) (mk32 443) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 103) (y := 443) (h := 395) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a22 : N (mk32 158) (mk32 103) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 158) (y := 103) (h := 103) (rx := 86) (ry := 188) (e := true) (by decide +kernel)
  have a23 : N (mk32 158) (mk32 122) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 158) (y := 122) (h := 415) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a24 : N (mk32 158) (mk32 92) ↔ N (mk32 86) (mk32 103) :=
    atom_iff hconj hinv (x := 158) (y := 92) (h := 397) (rx := 86) (ry := 103) (e := true) (by decide +kernel)
  have a25 : N (mk32 92) (mk32 254) ↔ N (mk32 86) (mk32 339) :=
    atom_iff hconj hinv (x := 92) (y := 254) (h := 335) (rx := 86) (ry := 339) (e := false) (by decide +kernel)
  have a26 : N (mk32 86) (mk32 254) ↔ N (mk32 86) (mk32 107) :=
    atom_iff hconj hinv (x := 86) (y := 254) (h := 212) (rx := 86) (ry := 107) (e := false) (by decide +kernel)
  have a27 : N (mk32 460) (mk32 254) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 460) (y := 254) (h := 206) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a28 : N (mk32 460) (mk32 188) ↔ N (mk32 86) (mk32 107) :=
    atom_iff hconj hinv (x := 460) (y := 188) (h := 92) (rx := 86) (ry := 107) (e := false) (by decide +kernel)
  have a29 : N (mk32 358) (mk32 254) ↔ N (mk32 86) (mk32 163) :=
    atom_iff hconj hinv (x := 358) (y := 254) (h := 103) (rx := 86) (ry := 163) (e := false) (by decide +kernel)
  have a30 : N (mk32 358) (mk32 188) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 358) (y := 188) (h := 103) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  have a31 : N (mk32 358) (mk32 460) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 358) (y := 460) (h := 247) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a32 : N (mk32 122) (mk32 443) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 122) (y := 443) (h := 419) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a33 : N (mk32 285) (mk32 103) ↔ N (mk32 86) (mk32 103) :=
    atom_iff hconj hinv (x := 285) (y := 103) (h := 167) (rx := 86) (ry := 103) (e := true) (by decide +kernel)
  have a34 : N (mk32 285) (mk32 443) ↔ N (mk32 86) (mk32 92) :=
    atom_iff hconj hinv (x := 285) (y := 443) (h := 143) (rx := 86) (ry := 92) (e := false) (by decide +kernel)
  have a35 : N (mk32 285) (mk32 122) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 285) (y := 122) (h := 143) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  have a36 : N (mk32 254) (mk32 92) ↔ N (mk32 86) (mk32 339) :=
    atom_iff hconj hinv (x := 254) (y := 92) (h := 107) (rx := 86) (ry := 339) (e := false) (by decide +kernel)
  have a37 : N (mk32 122) (mk32 92) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 122) (y := 92) (h := 305) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a38 : N (mk32 212) (mk32 254) ↔ N (mk32 86) (mk32 107) :=
    atom_iff hconj hinv (x := 212) (y := 254) (h := 275) (rx := 86) (ry := 107) (e := false) (by decide +kernel)
  have a39 : N (mk32 212) (mk32 92) ↔ N (mk32 86) (mk32 116) :=
    atom_iff hconj hinv (x := 212) (y := 92) (h := 84) (rx := 86) (ry := 116) (e := false) (by decide +kernel)
  have a40 : N (mk32 212) (mk32 122) ↔ N (mk32 86) (mk32 188) :=
    atom_iff hconj hinv (x := 212) (y := 122) (h := 84) (rx := 86) (ry := 188) (e := false) (by decide +kernel)
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a11, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40] at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  clear a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a11 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 hconj hinv hsymm hO
  generalize N (mk32 86) (mk32 92) = v1 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 103) = v2 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 107) = v3 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 116) = v4 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 163) = v5 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 165) = v6 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 188) = v7 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  generalize N (mk32 86) (mk32 339) = v9 at i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 hF2
  by_cases bv1 : v1 <;> by_cases bv2 : v2 <;> by_cases bv3 : v3 <;> by_cases bv4 : v4 <;> by_cases bv5 : v5 <;> by_cases bv6 : v6 <;> by_cases bv7 : v7 <;> by_cases bv9 : v9 <;> simp_all

end CFSG.RankThree.PartOne.NF7J
