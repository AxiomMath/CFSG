module

public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


structure GGDepEFrame (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod p) V) (x : V) : Prop where
  p3 : p = 3
  pair : ∀ i j, α i (h j) = (((CartanMatrix.E 6) i j : ℤ) : ZMod p)
  x_ne : x ≠ 0
  x_ker : ∀ i, α i x = 0
  fix : ∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod p) {x}
  dep : ¬ LinearIndependent (ZMod p) h

@[expose] def ggDepEh (p : ℕ) (i : Fin 6) : GGDepAE p 7 :=
  fun j => if hj : j.val < 6 then (((CartanMatrix.E 6) ⟨j.val, hj⟩ i : ℤ) : ZMod p) else 0

@[expose] def ggDepEα (p : ℕ) (i : Fin 6) : GGDepAE p 7 := fun j => if j.val = i.val then 1 else 0

@[expose] def ggDepEx (p : ℕ) : GGDepAE p 7 := fun j => if j.val = 6 then 1 else 0

@[expose] def GGDepEPat (b c0 : Fin 6) (m n : ℤ) : Prop :=
  m = -1 ∧ n = -1 ∧
    ((b = 0 ∧ (c0 = 1 ∨ c0 = 2 ∨ c0 = 5)) ∨ (b = 5 ∧ (c0 = 0 ∨ c0 = 1 ∨ c0 = 4)) ∨
      (b = 1 ∧ c0 = 3))

@[expose] def GGDepECells : Prop :=
  ∀ (b c0 : Fin 6) (m n : ℤ), GGDepEPat b c0 m n → ∀ ha αa : GGDepAE 3 7,
    (∀ c : Fin 6, c ≠ b →
      ggDepAdot αa (ggDepEh 3 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepEα 3 c) ha = (if c = c0 then (n : ZMod 3) else 0)) →
    ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepEx 3) ≠ 0 →
      ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin 6 =>
          ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g

end CFSG.StandardType
