module

public import CFSG.Quasithin.H13.U3SixCodes
public import CFSG.Quasithin.H13.L32NKGCertInputs
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin.SzPS8.G2U

open CFSG.Quasithin CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.KGCert

@[expose] def g2uc (i : Fin 5) : List ℕ :=
  [[1, 18, 36, 63, 17, 33], [1, 34, 52, 43, 17, 32], [1, 6, 4, 8, 16, 48],
    [1, 6, 2, 8, 32, 48], [17, 42, 49, 39, 1, 37]].getD i []

@[expose] def g2uci (i : Fin 5) : List ℕ :=
  [[1, 19, 37, 15, 17, 33], [1, 34, 53, 11, 17, 32], [1, 6, 4, 8, 16, 48],
    [1, 4, 6, 8, 48, 16], [16, 40, 53, 47, 17, 5]].getD i []

@[expose] def g2uw (i : Fin 5) : List Bool :=
  [[true, true, false, true, false, true, true, true, false, true, true, false],
    [false, true, false, true, false, true, false, true, true, true, false, false],
    [false, true, false, false, false, false, true, false, false, false, false, false, true],
    [true, true, true, false, false, false, false, true, false, true, false, false, false],
    [false, false, false, false, true, true, true, true, true, false, true, false, true,
      true]].getD i []

theorem g2uc_mul_inv :
    ∀ i : Fin 5, mul6 (g2uc i) (g2uci i) = id6 ∧ mul6 (g2uci i) (g2uc i) = id6 := by
  decide +kernel

theorem g2uc_relators : ∀ w ∈ u33PresRels,
    (w.map fun l => cond l.2 (g2uc l.1) (g2uci l.1)).foldr mul6 id6 = id6 := by
  decide +kernel

theorem g2uc_words : ∀ i : Fin 5, evalWord (g2uw i) = g2uc i := by
  decide +kernel

theorem g2uc_zero_ne : g2uc 0 ≠ id6 := by
  decide +kernel

end CFSG.Quasithin.SzPS8.G2U
