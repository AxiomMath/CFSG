module

public import CFSG.Monster.Existence.TwoPoint.Fi23Check
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Data

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short

@[expose] def s4PGamma : List Native.PGen := HS.pw s4WGamma

@[expose] def s4WBetaGamma : List Native.Gen := s4WGamma ++ fiWBeta

@[expose] def s4PBetaGamma : List Native.PGen := s4PGamma ++ fiPBeta

theorem s4PBetaGamma_eq : s4PBetaGamma = HS.pw s4WBetaGamma := by
  unfold s4PBetaGamma s4WBetaGamma s4PGamma fiPBeta
  rw [HS.pw_append]

@[expose] def s4WE8Gamma : List Native.Gen := s4WGamma ++ fiWU[8]!

@[expose] def s4PE8Gamma : List Native.PGen := s4PGamma ++ fiPU[8]!

theorem s4PE8Gamma_eq : s4PE8Gamma = HS.pw s4WE8Gamma := by
  unfold s4PE8Gamma s4WE8Gamma s4PGamma
  rw [HS.pw_append, fiPU_get (by norm_num)]

@[expose] def s4WAlphaGamma : List Native.Gen := s4WGamma ++ fiWAlpha

@[expose] def s4PAlphaGamma : List Native.PGen := s4PGamma ++ fiPAlpha

theorem s4PAlphaGamma_eq : s4PAlphaGamma = HS.pw s4WAlphaGamma := by
  unfold s4PAlphaGamma s4WAlphaGamma s4PGamma fiPAlpha
  rw [HS.pw_append]

@[expose, noinline] def s4CommGenCheck : Bool :=
  [0, 1, 2, 3, 4, 5, 6, 7, 9].all (fiCommCheck s4WGamma s4PGamma)

@[expose, noinline] def s4CommBetaCheck : Bool :=
  fiEqP (s4WGamma ++ fiWBeta) (fiWBeta ++ s4WGamma) (s4PGamma ++ fiPBeta) (fiPBeta ++ s4PGamma)

theorem wordLin_comm_of_s4CommBetaCheck
    (h : s4CommBetaCheck = true) :
    wordLin fiWBeta * wordLin s4WGamma = wordLin s4WGamma * wordLin fiWBeta := by
  unfold s4CommBetaCheck at h
  have := wordLin_eq_of_fiEqP h (by simp only [s4PGamma, fiPBeta, HS.pw_append])
    (by simp only [s4PGamma, fiPBeta, HS.pw_append])
  rwa [wordLin_append, wordLin_append] at this

@[expose, noinline] def s4CubeCheck (w : List Native.Gen) (p : List Native.PGen) : Bool :=
  fiEqP (w ++ w ++ w) [] (p ++ p ++ p) []

theorem wordLin_cube_of_s4CubeCheck
    {w : List Native.Gen} {p : List Native.PGen}
    (h : s4CubeCheck w p = true) (e : p = HS.pw w) : (wordLin w) ^ 3 = 1 := by
  unfold s4CubeCheck at h
  have := wordLin_eq_of_fiEqP h (by rw [e, HS.pw_append, HS.pw_append])
    (rfl : ([] : List Native.PGen) = HS.pw [])
  rw [wordLin_nil] at this
  rw [← this]
  simp only [wordLin_append]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

@[expose, noinline] def s4NeCheck (w : List Native.Gen) (p : List Native.PGen) (i j : ℕ) : Bool :=
  w.all Native.Gen.validB && hnDiffA i j (Native.evalPrep HS.hsCtx p HS.axisP) HS.axisP

theorem s4_wordLin_ne_one
    {w : List Native.Gen} {p : List Native.PGen} {i j : ℕ} (hi : i < 24)
    (hj : j < 24) (h : s4NeCheck w p i j = true) (e : p = HS.pw w) : wordLin w ≠ 1 := by
  unfold s4NeCheck at h
  rw [Bool.and_eq_true] at h
  rw [e] at h
  exact hn_wordLin_ne_one_of_diffA (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) h.1 h.2

@[expose, noinline] def s4MiscCheck : Bool :=
  fiSqCheck s4WGamma s4PGamma && fiSqCheck fiWU[8]! fiPU[8]! && s4CommBetaCheck

@[expose, noinline] def s4CubeNeCheck : Bool :=
  s4CubeCheck s4WE8Gamma s4PE8Gamma && s4CubeCheck s4WAlphaGamma s4PAlphaGamma &&
    s4NeCheck s4WE8Gamma s4PE8Gamma 0 0 && s4NeCheck s4WAlphaGamma s4PAlphaGamma 0 0

@[expose, noinline] def s4PowCheck : Bool := s4MiscCheck && s4CubeNeCheck

@[expose, noinline] def s4ConjCheck : Bool :=
  fiEqP (fiRhoT ++ s4CGamma) (s4CGamma ++ s4WGamma) (HS.pw fiRhoT ++ HS.pw s4CGamma)
      (HS.pw s4CGamma ++ s4PGamma) &&
    fiEqP (fiRhoT ++ s4CBetaGamma) (s4CBetaGamma ++ s4WBetaGamma)
      (HS.pw fiRhoT ++ HS.pw s4CBetaGamma) (HS.pw s4CBetaGamma ++ s4PBetaGamma)

theorem s4ConjCheck_parts
    (h : wordLin (fiRhoT ++ s4CGamma) = wordLin (s4CGamma ++ s4WGamma) ∧
      wordLin (fiRhoT ++ s4CBetaGamma) = wordLin (s4CBetaGamma ++ s4WBetaGamma)) :
    wordLin s4CGamma * wordLin fiRhoT = wordLin s4WGamma * wordLin s4CGamma ∧
      wordLin s4CBetaGamma * wordLin fiRhoT = wordLin s4WBetaGamma * wordLin s4CBetaGamma := by
  obtain ⟨h1, h2⟩ := h
  rw [wordLin_append, wordLin_append] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Monster.Existence
