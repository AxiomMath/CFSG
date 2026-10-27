module

public import CFSG.Sporadic.Schreier.J1CertData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public meta import CFSG.Sporadic.Schreier.J1CertData
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.Sporadic.Schreier.J1VecCheckInputs
public import Certificates.Certificate2167

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ProperTwoGeneratedCore Matrix

theorem j1_vectors_nodup : J1Certificate.vectors.Nodup :=
  Certificates.certificate2167.1

theorem j1Vec_ne_zero : ∀ i : Fin 3080, j1Vec i ≠ 0 :=
  Certificates.certificate2167.2.1

theorem j1_first_mulVec :
    ∀ i : Fin 3080, j1_first_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A1List i) :=
  Certificates.certificate2167.2.2.1

theorem j1_second_mulVec :
    ∀ i : Fin 3080, j1_second_matrix *ᵥ j1Vec i = j1Vec (j1Idx j1A2List i) :=
  Certificates.certificate2167.2.2.2.1

theorem j1BasisMat_mul_inv : j1BasisMat * j1BasisInv = 1 :=
  Certificates.certificate2167.2.2.2.2

end CFSG.Sporadic.Schreier
