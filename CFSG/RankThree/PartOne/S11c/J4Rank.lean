module

public import CFSG.RankThree.PartOne.S11c.J4Rep
public import CFSG.RankThree.PartOne.S11c.J4LocalRank
public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.Schreier.J4SCheck
public import CFSG.RankThree.PartOne.S11c.J4RankInputs
public import Certificates.Certificate10058
public meta import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra CFSG.Sporadic.J4Schreier Matrix Module
open scoped Matrix
open CFSG.Sporadic.SmallF2 (rowsMatrix)

attribute [local instance high] cleanAddCommGroupFin

theorem minor_check_eta_one :
    MinorCheck (etaP 1).1 minorQ1 minorB1 :=
  Certificates.certificate10058.1

theorem minor_check_eta_fourteen :
    MinorCheck (etaP 14).1 minorQ14 minorB14 :=
  Certificates.certificate10058.2

theorem finrank_centralFixed_le_of_minorCheck (g : CFSG.Sporadic.J4.J) (hg : g⁻¹ = g)
    (X : Array ℕ)
    (hX : rowsMatrix 112 X = ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (qs Bs : List ℕ) (hcheck : MinorCheck X qs Bs) :
    finrank (ZMod 2) (centralFixed rowRep g) ≤ 86 := by
  have hker : centralFixed rowRep g = LinearMap.ker (Matrix.vecMulLinear
      (rowsMatrix 112 X - 1)) := by
    ext w
    simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Matrix.vecMulLinear_apply, Matrix.vecMul_sub, Matrix.vecMul_one, rowRepGen_apply,
      hg, hX]
  have hB : (rowsMatrix 112 X - 1).submatrix minorRow (minorCol qs) * minorInv Bs = 1 := by
    ext a c
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hcheck a c
  have := finrank_ker_vecMul_add_le_of_minor (rowsMatrix 112 X - 1) minorRow (minorCol qs)
    (minorInv Bs) hB
  rw [hker]
  omega

theorem eta_inv (i : ℕ) : (η i)⁻¹ = η i :=
  inv_eq_of_mul_eq_one_right (by rw [← η_xor, Nat.xor_self, η_zero])

theorem finrank_centralFixed_eta_one :
    finrank (ZMod 2) (centralFixed rowRep (η 1)) ≤ 86 :=
  finrank_centralFixed_le_of_minorCheck (η 1) (eta_inv 1) (etaP 1).1
    (rep_etaP CFSG.Sporadic.J4.j4Facts.mat 1).2.2.1 minorQ1 minorB1 minor_check_eta_one

theorem finrank_centralFixed_eta_fourteen :
    finrank (ZMod 2) (centralFixed rowRep (η 14)) ≤ 86 :=
  finrank_centralFixed_le_of_minorCheck (η 14) (eta_inv 14) (etaP 14).1
    (rep_etaP CFSG.Sporadic.J4.j4Facts.mat 14).2.2.1 minorQ14 minorB14 minor_check_eta_fourteen

end CFSG.RankThree.PartOne
