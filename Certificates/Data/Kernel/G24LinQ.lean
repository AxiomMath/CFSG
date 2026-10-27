module

public import Certificates.Data.Kernel.G24LinK
public import Certificates.Data.G24LinEq

public section

namespace CFSG.KD.G24Lin

open CFSG.Quasithin.St84.G24LE

@[expose] noncomputable def monoB {n : ℕ} (w : ℕ) : Mono n → Bool
  | .inl i => bitK w i.val
  | .inr p => bitK w p.1.1.val && bitK w p.1.2.val

@[expose] noncomputable def entryB {n d : ℕ} (RC SR TB : ℕ) (r : Fin 3 × Mono n × Fin d)
    (u : Mono n × Fin d) : Bool :=
  xor (decide (r.2.2 = u.2) && monoB (wvK RC n r.1.val (laneK TB (monoKey r.2.1))) u.1)
    (bitK (laneK SR (Nat.add (Nat.mul r.1.val d) r.2.2.val)) u.2.val &&
      monoB (laneK TB (monoKey r.2.1)) u.1)

@[expose] def zB (b : Bool) : ZMod 2 := if b then 1 else 0

@[expose] noncomputable def pinM {R C : Type*} (rows : List R) (cols : List C) (M : R → C → ZMod 2)
    (kr : R → ℕ) (kc : C → ℕ) (o : ℕ) (D : ℕ → ℕ) : Bool :=
  rows.all fun r => cols.all fun u => M r u == zB (bitK (D (Nat.add o (kr r))) (kc u))

@[expose] def ext2KList : List ((Fin 2 × Fin 4) ⊕ Fin 2) :=
  ((List.finRange 2).flatMap fun i => (List.finRange 4).map fun j => Sum.inl (i, j)) ++
    (List.finRange 2).map Sum.inr

end CFSG.KD.G24Lin

end
