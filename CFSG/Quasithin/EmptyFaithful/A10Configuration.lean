module

public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationBridge
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveFinal

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin

@[expose] def A10Remainder : Prop := L32AutFact

theorem theorem1391_of_remainder
    (hrem : A10Remainder) : Theorem1391Statement := by
  intro G _ _ T hG _ hQ hT M hM hTM hiso
  obtain ⟨E⟩ := nonempty_emb_of_wreath hT hTM hiso
  exact E.false_of_through hrem hQ hT hM (E.through_13_9_9 hG hQ.2.1 hT hM)
    (E.lemma_13_9_10 hG hQ.2.1 hT hM)

end CFSG.Quasithin.A10
