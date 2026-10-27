module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1ElemData

public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2

namespace ElemThree

@[expose, irreducible] noncomputable def Ws : List GL24 :=
  dagG [ThreeLocal.y, ThreeLocal.t, ThreeLocal.z] (Data.dagWords.map Native.decWord)

@[expose] noncomputable def W (k : ℕ) : GL24 := Ws.getD k 1

@[expose] noncomputable def a (i : Fin 6) : GL24 := W (Data.elemIdx.getD i.val 0)

@[expose] noncomputable def E : Subgroup GL24 := Subgroup.closure (Set.range a)

@[expose] noncomputable def hAmb : List GL24 :=
  Data.ambWords.map fun w => wordG [A₁, A₂] (Native.decWord w)

@[expose] noncomputable def strong : List GL24 := dagG hAmb (Data.strongWords.map Native.decWord)

@[expose] noncomputable def g (i : Fin 3) : GL24 :=
  (Data.lowerWords.getD i.val []).foldl (fun x w => x * wordG strong (Native.decWord w))
    (wordG [A₁, A₂] (Native.decWord (Data.topWords.getD i.val [])))

@[expose] noncomputable def r : GL24 := g 2

@[expose] noncomputable def d (i : Fin 2) : GL24 := r * g i.castSucc * r⁻¹ * (g i.castSucc)⁻¹

@[expose] noncomputable def c (i : Fin 2) : GL24 := d i ^ 2 * g i.castSucc

@[expose] noncomputable def C : Subgroup GL24 := Subgroup.closure {c 0, c 1, r}

@[expose] noncomputable def A : Subgroup GL24 := Subgroup.closure ((E : Set GL24) ∪ {g 0, g 1, r})

noncomputable abbrev e (k : Fin 24) : Vec24 := Pi.single k 1

@[expose] noncomputable def f4Vec (cs : List ℕ) : Vec24 :=
  ∑ k : Fin 12, ((((cs.getD k.val 0) % 2 : ℕ) : ZMod 2) • e (k.castLE (by norm_num)) +
    (((cs.getD k.val 0) / 2 % 2 : ℕ) : ZMod 2) •
      (ThreeLocal.z : Matrix (Fin 24) (Fin 24) (ZMod 2)).mulVec (e (k.castLE (by norm_num))))

@[expose] noncomputable def q (j : Fin 12) : Vec24 := f4Vec (Data.f4vecs.getD j.val [])

@[expose] def γ (j : Fin 12) : Fin 6 → ZMod 3 :=
  fun i => ((Data.eigenchars.getD j.val []).getD i.val 0 : ℕ)

@[expose] def R : Matrix (Fin 6) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => ((Data.ternRows.getD i.val []).getD j.val 0 : ℕ)

@[expose] noncomputable def T : Submodule (ZMod 3) (Fin 12 → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range R)

@[expose] def signedMatrix (p : Fin 12 → Fin 12) (ε : Fin 12 → ZMod 3) :
    Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun i j => if i = p j then ε j else 0

@[expose] def liftPerm (i : Fin 2) (j : Fin 12) : Fin 12 :=
  Fin.ofNat 12 ((Data.liftPerms.getD i.val []).getD j.val 0)

@[expose] def liftSign (i : Fin 2) (j : Fin 12) : ZMod 3 :=
  ((Data.liftSigns.getD i.val []).getD j.val 0 : ℕ)

@[expose] def σMat (i : Fin 2) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  signedMatrix (liftPerm i) (liftSign i)

@[expose] def σInvMat (i : Fin 2) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  Matrix.of fun j k => if k = liftPerm i j then liftSign i j else 0

end ElemThree

end CFSG.Sporadic.Co1Schreier
