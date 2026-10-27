module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.RankThree.GF2n.Parrott.PSp43Model

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

structure QuotientData (z : G) (hN : ((J z).subgroupOf (H z)).Normal) : Type 1 where
  X : Type
  instX : Group X
  lie : CFSG.Blueprint.LieModel X .PSp 2 3 1
  iso : letI := hN; (↥(H z) ⧸ (J z).subgroupOf (H z)) ≃* MulAut X

attribute [instance] QuotientData.instX

namespace QuotientData

noncomputable def toQA45 {hN : ((J z).subgroupOf (H z)).Normal}
    (D : QuotientData z hN) :
    letI := hN; (↥(H z) ⧸ (J z).subgroupOf (H z)) ≃* QA45.originalSubgroup := by
  letI := hN
  let eX : D.X ≃* ↥(QP45.originalSubgroup) := Classical.choice (equiv_of_lieModel D.lie)
  let M : CFSG.GH74.KGroups.AutModel D.X (Equiv.Perm (Fin 45)) :=
    Classical.choose (exists_model eX)
  have hA : M.A = QA45.originalSubgroup :=
    (Classical.choose_spec (exists_model eX)).2
  exact D.iso.trans (M.Φ.trans (MulEquiv.subgroupCongr hA))

end QuotientData

theorem parrottQuotientDataExists (h : Tim79a.ParrottHyp z) :
    ∃ (hN : ((J z).subgroupOf (H z)).Normal), Nonempty (QuotientData z hN) := by
  classical
  obtain ⟨h1, h2, hcomm, h4, hnorm, X, instX, hLM, hiso⟩ := h
  exact ⟨hnorm, ⟨{ X := X, instX := instX, lie := hLM, iso := Classical.choice hiso }⟩⟩

end CFSG.RankThree.GF2n.Parrott
