module

public import CFSG.Sporadic.Schreier.TitsQTStrong
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public noncomputable section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.QuasithinUnique.K1 CFSG.Sporadic.Schreier.Tits

theorem titsD_noStronglyClosedElemAbelian :
    NoStronglyClosedElemAbelian titsD := by
  intro P A hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hW.sylow
  refine QT_unique_Tits_no_abelian_strong_closure (hp.toSylow hi) A
    (And.intro (fun a ha => hW.le ha) fun a ha g hg => hW.closed a ha g hg) fun a ha b hb => ?_
  have h := hW.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem tits_model_noStronglyClosedElemAbelian
    (X : Type) [Group X]
    (h : CFSG.Blueprint.ReeTitsModel X .Tits 2 1) : NoStronglyClosedElemAbelian X := by
  obtain ⟨e⟩ := titsModelEquiv X 2 1 h
  exact NoStronglyClosedElemAbelian.of_mulEquiv e titsD_noStronglyClosedElemAbelian

end CFSG.Sporadic.Schreier.TitsQT
