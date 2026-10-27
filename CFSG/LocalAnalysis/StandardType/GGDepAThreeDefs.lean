module

public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] def GGDepAPatE (N : ℕ) (b c0 : Fin (N - 1)) (m n : ℤ) : Prop :=
  GGDepAPat N b c0 m n ∨
    (N = 9 ∧ (b.val = 0 ∨ b.val + 2 = N) ∧ c0 ≠ b ∧ m = -1 ∧ n = -1 ∧
      ((if b.val = 0 then c0.val - 1 else c0.val) = 2 ∨
        (if b.val = 0 then c0.val - 1 else c0.val) = 4))

@[expose] def GGDepAThreeCells9 : Prop :=
  ∀ (b c0 : Fin (9 - 1)) (m n : ℤ), GGDepAPatE 9 b c0 m n → ∀ ha αa : GGDepAE 3 9,
    (∀ c : Fin (9 - 1), c ≠ b →
      ggDepAdot αa (ggDepAh 3 9 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepAα 3 9 c) ha = (if c = c0 then (n : ZMod 3) else 0)) →
    ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepAx 3 9) ≠ 0 →
      ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (9 - 1) =>
          ggDepARefl (ggDepAh 3 9 i) (ggDepAα 3 9 i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g

@[expose] def GGDepAWeylE6Data (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6))) : Prop :=
  ∃ (s : Fin 6 → Module.End (ZMod 3) (GGDepAE 3 6))
    (w : Fin 72 → Module.End (ZMod 3) (GGDepAE 3 6)),
    (∀ i, s i ∈ Submonoid.closure gens) ∧
    (∀ i, ∃ c f : GGDepAE 3 6, ggDepAdot f c = 2 ∧ s i = ggDepARefl c f) ∧
    (∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆ i j) = 1) ∧
    (∀ g ∈ gens, g ∈ Submonoid.closure (Set.range s)) ∧
    (∀ k, w k ∈ Submonoid.closure gens) ∧ Function.Injective (fun k => w k (ggDepAx 3 6))

@[expose] def GGDepAThreeCells6 : Prop :=
  ∀ (b c0 : Fin (6 - 1)) (m n : ℤ), GGDepAPatE 6 b c0 m n → ∀ ha αa : GGDepAE 3 6,
    (∀ c : Fin (6 - 1), c ≠ b →
      ggDepAdot αa (ggDepAh 3 6 c) = (if c = c0 then (m : ZMod 3) else 0) ∧
        ggDepAdot (ggDepAα 3 6 c) ha = (if c = c0 then (n : ZMod 3) else 0)) →
    ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepAx 3 6) ≠ 0 →
      (∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (6 - 1) =>
          ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g) ∨
      GGDepAWeylE6Data (Set.range (fun i : Fin (6 - 1) =>
          ggDepARefl (ggDepAh 3 6 i) (ggDepAα 3 6 i)) ∪ {ggDepARefl ha αa})

end CFSG.StandardType
