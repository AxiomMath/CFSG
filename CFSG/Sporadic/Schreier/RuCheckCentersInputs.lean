module

public import CFSG.Sporadic.Schreier.RuCheckSylow
public meta import CFSG.Sporadic.Schreier.RuCheckSylow

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def ruConjA (n e : Array ℕ) : Array ℕ := compA 4060 (compA 4060 n e) (invCand 4060 n)

@[expose] def ruNGensA : Array (Array ℕ) := #[ruNs0A, ruNs1A]

@[expose] def ruEBFS : Array (Array ℕ) × Array ℕ × Array ℕ := Id.run do
  let mut els : Array (Array ℕ) := #[ruZA]
  let mut par : Array ℕ := #[0]
  let mut gl : Array ℕ := #[0]
  let mut head := 0
  for _ in [0:8] do
    if head < els.size then
      let e := els[head]!
      for g in [0:2] do
        let c := ruConjA ruNGensA[g]! e
        if !(els.any fun x => eqA 4060 x c) then
          els := els.push c
          par := par.push head
          gl := gl.push g
      head := head + 1
  return (els, par, gl)

opaque ruEArrSeal : {a : Array (Array ℕ) // a = ruEBFS.1} := ⟨ruEBFS.1, rfl⟩

@[expose] def ruEArr : Array (Array ℕ) := ruEArrSeal.1

theorem ruEArr_def : ruEArr = ruEBFS.1 := ruEArrSeal.2

attribute [irreducible] ruEArr

opaque ruEParSeal : {a : Array ℕ // a = ruEBFS.2.1} := ⟨ruEBFS.2.1, rfl⟩

@[expose] def ruEPar : Array ℕ := ruEParSeal.1

theorem ruEPar_def : ruEPar = ruEBFS.2.1 := ruEParSeal.2

attribute [irreducible] ruEPar

opaque ruEGenSeal : {a : Array ℕ // a = ruEBFS.2.2} := ⟨ruEBFS.2.2, rfl⟩

@[expose] def ruEGen : Array ℕ := ruEGenSeal.1

theorem ruEGen_def : ruEGen = ruEBFS.2.2 := ruEGenSeal.2

attribute [irreducible] ruEGen

@[expose] def ruEF (i : ℕ) : Array ℕ := resA ruF ruFPos ruEArr[i]!

@[expose] def ruKF (k : ℕ) : Array ℕ := (ruField1920 2)[k]!

@[expose] def ruJF (j : ℕ) : Array ℕ := (ruField1920 3)[j]!

@[expose] def ruKLevels : Array Level := rawLevels 1920 (ruField1920 2) (ruBaseArr 1920 ruKBase)

@[expose] def ruJLevels : Array Level := rawLevels 1920 (ruField1920 3) (ruBaseArr 1920 ruJBase)

@[expose] def ruComm1920 (g h : Array ℕ) : Bool := eqA 1920 (compA 1920 g h) (compA 1920 h g)

end CFSG.Sporadic.RuSchreier
