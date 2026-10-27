module

public import CFSG.Sporadic.Schreier.TitsInv
public import CFSG.Sporadic.Schreier.TitsAbel
public import CFSG.Sporadic.Schreier.RuOrbit
public import CFSG.Quasithin.Recognition.RuRank3Defs
public meta import CFSG.Sporadic.Schreier.TitsInv
public meta import CFSG.Sporadic.Schreier.TitsAbel
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public meta import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public meta import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public meta import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public meta import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public meta import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.RuCore
public meta import CFSG.Sporadic.Schreier.RuCore
public import CFSG.Sporadic.Schreier.TitsOther
public meta import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public meta import CFSG.Sporadic.Schreier.TitsOuter
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates

@[expose] def orbLabels (n : ℕ) (gens : Array (Array ℕ)) : Array ℕ × Array ℕ := Id.run do
  let mut lab : Array ℕ := Array.replicate n n
  let mut roots : Array ℕ := #[]
  for s in [0:n] do
    if lab[s]! == n then
      let c := roots.size
      roots := roots.push s
      lab := lab.set! s c
      let mut queue : Array ℕ := #[s]
      let mut head := 0
      for _ in [0:n] do
        if head < queue.size then
          let x := queue[head]!
          head := head + 1
          for k in [0:gens.size] do
            let y := (gens[k]!)[x]!
            if y < n && lab[y]! == n then
              lab := lab.set! y c
              queue := queue.push y
  return (lab, roots)

@[expose] def orbLab (n : ℕ) (gens : Array (Array ℕ)) : Array ℕ := (orbLabels n gens).1

theorem orbLab_eq (n : ℕ) (gens : Array (Array ℕ)) : orbLab n gens = (orbLabels n gens).1 := rfl

@[expose] def orbCheck (n : ℕ) (gens : Array (Array ℕ)) : Bool :=
  let L := orbLabels n gens
  let F := CFSG.Sporadic.RuSchreier.orbitForest n gens L.2
  orbitPartOK n gens L.1 L.2 F.1 F.2.1 F.2.2

@[expose] def labCount (n : ℕ) (lab : Array ℕ) (c : ℕ) : ℕ :=
  (List.range n).countP fun x => lab[x]! == c

@[expose] def titsPAGens : Array (Array ℕ) :=
  #[titsSArrs[0]!, titsSArrs[1]!, titsSArrs[2]!, titsGenArrs[1]!]

@[expose] def titsPALab : Array ℕ := orbLab 1755 titsPAGens

end CFSG.Quasithin.RuRank3
