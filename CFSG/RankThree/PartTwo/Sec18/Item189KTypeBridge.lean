module

public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.KFacts.K71Residual

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Census (typeAGroupEquivProjSL typeTwistedAGroupEquivProjSU)

private theorem nonempty_alt5_mulEquiv_projSL :
    Nonempty (alternatingGroup (Fin 5) ≃* projSL 2 (GaloisField 2 2)) := by
  obtain ⟨ι⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 2) (f := 2)
    (GaloisField.card 2 2 (by norm_num))
  obtain ⟨κ⟩ := CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5
  exact ⟨κ.symm.trans ι⟩

section Certified


theorem isRankOneType189_of_index
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (i : TauCeti.CFSGIndex) (e : S ≃* i.Group)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1) : IsRankOneType189 S := by
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple S hS hnab i
      ⟨e⟩ h3 with ⟨⟨d, hv⟩, hfam, ⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · rcases hfam with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ <;> simp only at hd <;> subst hd <;>
      have : Fact q.p.Prime := ⟨q.prime_p⟩
    · exact Or.inl ⟨q.p, q.exponent, this, hq, q.exponent_pos,
        ⟨f.trans (typeAGroupEquivProjSL 1 q hv)⟩⟩
    · have hq' : q.p ^ q.exponent % 3 = 2 := by rwa [← TauCeti.PrimePower.card_def]
      exact Or.inr (Or.inl ⟨q.p, q.exponent, this, q.exponent_pos, hq',
        ⟨f.trans (typeAGroupEquivProjSL 2 q hv)⟩⟩)
    · have hq' : q.p ^ q.exponent % 3 = 1 := by rwa [← TauCeti.PrimePower.card_def]
      exact Or.inr (Or.inr (Or.inl ⟨q.p, q.exponent, this, q.exponent_pos, hq',
        ⟨f.trans (typeTwistedAGroupEquivProjSU 2 q hv)⟩⟩))
  · obtain ⟨g⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr ⟨f.trans g.symm⟩))
  · obtain ⟨g⟩ := nonempty_alt5_mulEquiv_projSL
    exact Or.inl ⟨2, 2, Nat.fact_prime_two, by norm_num, by norm_num, ⟨f.trans g⟩⟩

end Certified

end CFSG.RankThree.PartTwo.Sec18
