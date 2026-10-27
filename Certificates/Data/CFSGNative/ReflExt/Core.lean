module

public import Certificates.Data.CFSGNative.TwoNodeSmall.VerifyPos

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

set_option compiler.extract_closed false

structure Root where
  r : Refl
  w : Word

structure OEnt where
  e : Refl
  w : Word
  j : Nat

structure Rep2 where
  r : Refl
  o : OWit

inductive RKind
  | bad (o : OWit)
  | good (c : WWit)

structure Rep where
  r : Refl
  kind : RKind
  maximal : Bool
  roots : List Root
  reps2 : List Rep2
  orb2 : List OEnt

structure Tables where
  roots : List Root
  orb1 : List OEnt
  reps : List Rep

@[expose, reducible] def withExtra (P : Pt) (extra : List Refl) : Pt := { P with gens := P.gens ++ extra }

@[expose] def negR (P : Pt) (r : Refl) : Refl :=
  ⟨(List.range P.D).map fun i => (P.p - (r.f.getD i 0) % P.p) % P.p,
   (List.range P.D).map fun i => (P.p - (r.h.getD i 0) % P.p) % P.p⟩

@[expose] def reqb (r s : Refl) : Bool := r.f == s.f && r.h == s.h

@[expose] def conjR (P : Pt) (i : Nat) (r : Refl) : Refl :=
  match P.gens[i]? with
  | none => r
  | some ρ =>
    let a := P.dotv r.f ρ.h
    let b := P.dotv ρ.f r.h
    ⟨(List.range P.D).map fun t => (r.f.getD t 0 + (P.p - (a * ρ.f.getD t 0) % P.p)) % P.p,
     (List.range P.D).map fun t => (r.h.getD t 0 + (P.p - (b * ρ.h.getD t 0) % P.p)) % P.p⟩

@[expose] def realizes (P : Pt) (w : Word) (r : Refl) : Bool :=
  P.wordOK w && (List.range P.D).all fun i => P.vecEq (P.applyWord w (P.unit i)) (P.applyRefl r (P.unit i))

@[expose] def wfR (P : Pt) (r : Refl) : Bool := P.dotv r.f r.h == 2 % P.p

@[expose] def asymR (P : Pt) (c ρ : Refl) : Bool := (P.dotv c.f ρ.h == 0) != (P.dotv ρ.f c.h == 0)

@[expose] def asymAny (P : Pt) (rs : List Refl) (c : Refl) : Bool := rs.any fun ρ => asymR P c ρ

@[expose] def maskF (P : Pt) (rs : List Refl) (v : Vec) : List Bool := rs.map fun ρ => P.dotv v ρ.h == 0
@[expose] def maskH (P : Pt) (rs : List Refl) (v : Vec) : List Bool := rs.map fun ρ => P.dotv ρ.f v == 0

@[expose] def candList (P : Pt) (rs : List Refl) : List Refl :=
  let vs := allVecsP P.p P.D
  let VF := vs.map fun v => (v, maskF P rs v)
  let VH := vs.map fun v => (v, maskH P rs v)
  VF.flatMap fun a => VH.filterMap fun b =>
    if a.2 == b.2 && P.dotv a.1 b.1 == 2 % P.p then some ⟨a.1, b.1⟩ else none

@[expose] def movingOf (P : Pt) (cs : List Refl) : List Refl := cs.filter fun c => P.dotv c.f P.x != 0

end CFSG.ReflExt

end
