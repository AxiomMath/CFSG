module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps66Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10Spor
import CFSG.LocalAnalysis.UniquenessCase.UC22S216

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps67Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s21_8 : S21_8Sp4 D Ch
  s21_21TB : S21_21TB D Ch
  s22_5_1R3 : S22_5_1R3 D Ch
  s21_12 : S21_12 D Ch
  s21_17RJ1 : S21_17RJ1 D Ch
  r8_2 : F08.R82 D
  s21_3 : S21_3 D Ch
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3 : S21_22R3 D Ch
  s21_9Sig3 : S21_9Sig3 D Ch
  s22_fin3R : S22Fin3R D Ch

theorem Steps67Three.toSteps66Three {D : Data G} {Ch : Choice2011 G} (h : Steps67Three D Ch)
    (h5 : S21_5 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hK : F10.K105Spor)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2) :
    Steps66Three D Ch where
  s21_6Inf := s21_6Inf_of_k105Spor h.s21_3 h5 hn3 hK hrank hout
  s21_14 := h.s21_14
  s21_8 := h.s21_8
  s21_21TB := h.s21_21TB
  s22_5_1R3 := h.s22_5_1R3
  s21_12 := h.s21_12
  s21_17RJ1 := h.s21_17RJ1
  r8_2 := h.r8_2
  s21_3 := h.s21_3
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3 := h.s21_22R3
  s21_9Sig3 := h.s21_9Sig3
  s22_fin3R := h.s22_fin3R

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
