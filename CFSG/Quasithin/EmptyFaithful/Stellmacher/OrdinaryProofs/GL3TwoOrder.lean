module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
