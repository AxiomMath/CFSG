module

public import CFSG.OddTranspositions.O4PairTenAbstract

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.PSL2Table

def commX (i j : Fin 10) : Prop :=
  X i * X j = X j * X i ∨ X i * X j = -(X j * X i)

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

private instance (priority := 2000) f25tDecEqInst : DecidableEq F25t := f25tDecEq

private def commXDecidable (i j : Fin 10) : Decidable (commX i j) :=
  decidable_of_iff (X i * X j = X j * X i ∨ X i * X j = -(X j * X i)) Iff.rfl

private instance instDecidableRelCommX : DecidableRel commX := commXDecidable

theorem commY_iff (i j : Fin 10) : Commute (y i) (y j) ↔ Commute (x i) (x j) := by
  rw [show y i = psigmaL2Equiv (SemidirectProduct.mk (x i) frob25t) from rfl,
    show y j = psigmaL2Equiv (SemidirectProduct.mk (x j) frob25t) from rfl,
    psigmaL2Equiv_conj_iff]
  exact commute_mk_frob25t_iff (x_fixed i) (x_fixed j)

end CFSG.OddTranspositions.QZ
