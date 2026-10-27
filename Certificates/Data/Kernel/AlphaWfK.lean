module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding.R3

@[expose] def NMod.wfK (p : Nat) (m : NMod) : Bool :=
  decide (2 ≤ p) &&
  m.acts.all (fun g => decide (g.mat.length = m.basis.length * m.basis.length)) &&
  match allVecs p m.basis.length with
  | [] => true
  | c :: cs => c.all (· == 0) && cs == m.indep.map (·.1)

end CFSG.AGLEmbedding.R3

end
