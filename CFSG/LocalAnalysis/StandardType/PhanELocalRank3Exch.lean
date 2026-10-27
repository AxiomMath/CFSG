module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchDef
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchGal
import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchNbr

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

theorem exchA2A1_models (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((PhanCode.exchA2A1.sys K).restrict (PhanCode.exchA2A1.set K f)).Connected ∧
      ((PhanCode.exchA2A1.sys K).restrict (PhanCode.exchA2A1.set K f)).SimplyTwoConnected := by
  have hI : ∀ i : Fin 2 ⊕ Fin 1, i = Sum.inl 0 ∨ i = Sum.inl 1 ∨ i = Sum.inr 0 := by
    intro i
    rcases i with i | j
    · fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (by rw [Subsingleton.elim j 0]))
  exact simplyTwoConnected_of_pointGraph (Exch.X K f) (Sum.inl 0) (Sum.inl 1) (Sum.inr 0) hI
    (Exch.P K f) (fun p => by obtain ⟨c, hc⟩ := p.2; exact ⟨c, Subtype.ext hc⟩)
    (fun h => Exch.P_b h) (fun h => Exch.P_c h) (fun h hP => Exch.inj_a h hP)
    (fun e e' h => Exch.fib_exch e e' h)
    (fun h1 h2 hee hgg hne => Exch.edge_exch h1 h2 hee hgg hne)
    (fun s hs hc => Exch.cn_exch hK hq s hs hc)
    (fun h1 h2 h3 => Exch.cone_exch hK hq h1 h2 h3)

end CFSG.ClassicalInvolution.Phan.PhanE

end
