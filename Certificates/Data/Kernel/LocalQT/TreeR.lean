module

public import Certificates.Data.Kernel.LocalQT.RankB
public import CFSG.Quasithin.Vol2.KGFactRankInputs
public import CFSG.Foundations
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.KC.LQT.TR

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.PP CFSG.KC.LQT.RW CFSG.KC.LQT.RB
open CFSG.Quasithin.H13.KGRank

@[expose] noncomputable def cenR (W g N zi : Nat) (PT CT : Nat → Nat) (lo len : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) => allR lo len fun i => Nat.beq (mul zi i) (mul i zi))
    (mulT W g N PT CT)

@[expose] noncomputable def candR (W g N : Nat) (PT CT : Nat → Nat) : List Nat :=
  List.cons 0 (invsB N (mulT W g N PT CT))

@[expose] noncomputable def treeRT (W g N zi : Nat) (PT CT : Nat → Nat)
    (nodes : Array (List Nat × List Nat)) : Bool :=
  CFSG.KC.Ord.andB (Nat.blt zi N) (CFSG.KC.Ord.andB (Nat.beq (mulT W g N PT CT zi zi) 0)
    (nodeCheck N (mulT W g N PT CT) nodes (nodes.size + 1) 0 [zi] (candR W g N PT CT)))

@[expose] noncomputable def nodeTop (N : Nat) (mul : Nat → Nat → Nat)
    (nodes : Array (List Nat × List Nat)) (j : Nat) (F D : List Nat) : Bool :=
  let invs := D.filter fun x => mul x x == 0
  let sp := spanIdx mul F
  let cands := invs.filter fun x => !sp.contains x
  let nd := nodes.getD j ([], [])
  let reps := pairsOf nd.1
  let wit := triplesOf nd.2
  decide (sp.length < 2 ^ 8) && cands == wit.map Prod.fst &&
    wit.all (fun w => decide (w.2.1 < N) && decide (w.2.2 < reps.length) &&
      F.all (fun f => mul w.2.1 f == mul f w.2.1) &&
      mul w.2.1 w.1 == mul (reps.getD w.2.2 (0, 0)).1 w.2.1) &&
    reps.all fun rc => decide (rc.1 < N)

@[expose] noncomputable def candOK (W g N : Nat) (PT CT : Nat → Nat) (C : List Nat) : Bool :=
  CFSG.KC.LQT.BW.eqLW (candR W g N PT CT) C

@[expose] noncomputable def topR (W g N zi : Nat) (PT CT : Nat → Nat)
    (nodes : Array (List Nat × List Nat)) (C : List Nat) (K : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) => CFSG.KC.Ord.andB (Nat.blt zi N) (CFSG.KC.Ord.andB (Nat.beq (mul zi zi) 0)
    (CFSG.KC.Ord.andB (nodeTop N mul nodes 0 [zi] C)
      (Nat.beq (pairsOf (nodes.getD 0 ([], [])).1).length K))))
  (mulT W g N PT CT)

@[expose] noncomputable def childR (W g N zi : Nat) (PT CT : Nat → Nat)
    (nodes : Array (List Nat × List Nat)) (C : List Nat) (k : Nat) : Bool :=
  (fun (mul : Nat → Nat → Nat) => (fun (rc : Nat × Nat) =>
      nodeCheck N mul nodes nodes.size rc.2 [rc.1, zi] (C.filter fun y => mul y rc.1 == mul rc.1 y))
    ((pairsOf (nodes.getD 0 ([], [])).1).getD k (0, 0)))
  (mulT W g N PT CT)

end CFSG.KC.LQT.TR

end
