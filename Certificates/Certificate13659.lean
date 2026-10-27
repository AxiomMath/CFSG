module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit
import Certificates.Kernel.RootOrbit.Orbit

public section

open CFSG.HardMathSupport.Timmesfeld.RootAut TauCeti CertificateChecks.KernelRootOrbit

namespace Certificates

open CFSG.HardMathSupport.Timmesfeld.RootAut in
theorem certificate13659 : rigidTypes.all rigidOK = true ∧ countTypes.all countOK = true := by
  refine ⟨?_, ?_⟩
  · simp only [rigidTypes, List.all_cons, List.all_nil, rigidOK, DynkinType.cartanMatrix_A,
      DynkinType.cartanMatrix_B, DynkinType.cartanMatrix_C, DynkinType.cartanMatrix_E7,
      DynkinType.cartanMatrix_E8, DynkinType.cartanMatrix_F4, DynkinType.cartanMatrix_G2,
      Bool.and_true, Bool.and_eq_true]
    exact ⟨sepA1, sepB2, sepB3, sepB4, sepB5, sepB6, sepB7, sepB8, sepC3, sepC4, sepC5, sepC6,
      sepC7, sepC8, sepE7, sepE8, sepF4, sepG2⟩
  · simp only [countTypes, List.all_cons, List.all_nil, countOK, DynkinType.cartanMatrix_A,
      DynkinType.cartanMatrix_D, DynkinType.cartanMatrix_E6, Bool.and_true, Bool.and_eq_true]
    exact ⟨orbitOK_A2, orbitOK_A3, orbitOK_A4, orbitOK_A5, orbitOK_A6, orbitOK_A7, orbitOK_A8,
      orbitOK_D4, orbitOK_D5, orbitOK_D6, orbitOK_D7, orbitOK_D8, orbitOK_E6⟩

end Certificates
