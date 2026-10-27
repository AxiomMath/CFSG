module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWDPairs1 (p N : ℕ) (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ)
    (ha αa : GGDepAE p N) : Prop :=
  ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
    ggDepAdot αa (ggDepAh p N c) = (if c = c0 then (m : ZMod p) else 0) ∧
      ggDepAdot (ggDepAα p N c) ha = (if c = c0 then (n : ZMod p) else 0)

@[expose] def GGTWDPairs2 (p N : ℕ) (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1)))
    (ha1 αa1 ha2 αa2 : GGDepAE p N) : Prop :=
  (∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggDepAdot αa1 (ggDepAh p N c') = (if c' = c then -1 else 0) ∧
        ggDepAdot (ggDepAα p N c') ha1 = (if c' = c then -1 else 0) ∧
        ggDepAdot αa2 (ggDepAh p N c') = (if some c' = c₂ then -1 else 0) ∧
        ggDepAdot (ggDepAα p N c') ha2 = (if some c' = c₂ then -1 else 0)) ∧
    ggDepAdot αa1 ha2 = (if c₂ = none then -1 else 0) ∧
      ggDepAdot αa2 ha1 = (if c₂ = none then -1 else 0) ∧ ggDepAdot αa1 ha1 = 2 ∧
        ggDepAdot αa2 ha2 = 2

@[expose] def GGTWDCells1 (p N : ℕ) : Prop :=
  ∀ (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n →
    ∀ ha αa : GGDepAE p N, GGTWDPairs1 p N pos c0 m n ha αa → ggDepAdot αa ha = 2 →
      ggDepAdot αa (ggDepAx p N) ≠ 0 →
        ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
            ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g

@[expose] def GGTWDCells2 (p N : ℕ) : Prop :=
  ∀ (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))),
    GGTWPat2 N pos c.val (c₂.map Fin.val) →
      ∀ ha1 αa1 ha2 αa2 : GGDepAE p N, GGTWDPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 →
        (ggDepAdot αa1 (ggDepAx p N) ≠ 0 ∨ ggDepAdot αa2 (ggDepAx p N) ≠ 0) →
          ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
              ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
                {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}), GGDepAIsTv g

@[expose] def GGTWDCells (p N : ℕ) : Prop :=
  GGTWDCells1 p N ∧ GGTWDCells2 p N

end CFSG.StandardType

end
