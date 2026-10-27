module

public import CFSG.Quasithin.EmptyFaithful.S151S9TChecks
public import Certificates.Certificate4033
public import CFSG.Quasithin.EmptyFaithful.S151S9TM24

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.S151S9T

theorem input15122ThreeDLocS_proved
    (h : ThreeDFacts) : Input15122ThreeDLocS := by
  intro G _ _ L S hL hS2 hSN hSyl z hz hnc
  rcases hL with hJ | hHe | hM12 | hM22 | hM23 | hM24
  · exact h.j2 G L S hJ hS2 hSN hSyl z hz hnc
  · exact Certificates.certificate4033.2 G L S hHe hS2 hSN hSyl z hz hnc
  · exact h.m12 G L S hM12 hS2 hSN hSyl z hz hnc
  · exact h.m22 G L S hM22 hS2 hSN hSyl z hz hnc
  · exact h.m23 G L S hM23 hS2 hSN hSyl z hz hnc
  · exact m24_threeD G L S hM24 hS2 hSN hSyl z hz hnc

end CFSG.Quasithin
