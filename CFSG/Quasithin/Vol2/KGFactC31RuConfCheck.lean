module

public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Quasithin.Vol2.KGFactC31ArrChain
public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

@[expose] def m64S : Array (Array ℕ) := (strongM64W.map wA).toArray

@[expose] def m64B : Vector (Fin 4060) 2 := #v[0, 1]

@[expose] def noDer5 : Array (List ℤ) := (List.replicate 5 ([] : List ℤ)).toArray

@[expose] def m64L : Array Level := rawLevels 4060 m64S (arrBase m64B)

@[expose] def m64Sift (t : Array ℕ) : Bool := siftA 4060 m64L (arrBase m64B) 0 t

@[expose] def wM (w : List ℤ) : Array ℕ := wordA 4060 m64S (m64S.map ruInv) w

@[expose] def u33A : Array (Array ℕ) := (u33W.map wA).toArray

@[expose] def uGens : Array (Array ℕ) := u33A ++ b64A.toArray

@[expose] def relA (r : List (Fin 5 × Bool)) : Array ℕ :=
  r.foldl (fun acc l => compA 4060 acc (if l.2 then u33A[l.1.val]! else ruInv u33A[l.1.val]!))
    (idA 4060)

@[expose] def t64A : Array ℕ := wA t64W

@[expose] def m64Checks : Bool :=
  rawChainOK 4060 (arrO m64S 5) m64S (arrBase m64B) noDer5 4 &&
  (rawOrbitSizes 4060 m64S (arrBase m64B)).prod == 387072 &&
  (m64S.toList.all fun s => normsA s (ruInv s) b64A sp64) &&
  b64A.all m64Sift &&
  u33A.toList.all m64Sift &&
  (u33PresRels.all fun r => inA sp64 (relA r)) &&
  ((List.range 5).all fun j =>
    eqA 4060 (wordA 4060 uGens (uGens.map ruInv) (strongInU33W.getD j [])) m64S[j]!) &&
  (sp64.all fun v => eqA 4060 v (idA 4060) ||
    conjT64W.any fun w => eqA 4060 (cjA (wM w) (ruInv (wM w)) t64A) v)

end CFSG.Quasithin.KGC31.Ru

end
