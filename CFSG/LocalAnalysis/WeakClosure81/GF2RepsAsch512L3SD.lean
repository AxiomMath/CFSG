module

public import CFSG.GH74.Defs
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.CGT.PushingUpLit.SolK.GenFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)

theorem sectionalTwoRankLE_two_of_lieModel_psl_three {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSL 3 p f) (hq : p ^ f % 4 = 3) :
    CFSG.GH74.SectionalTwoRankLE X 2 := by
  obtain ⟨-, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨m, hm, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_sd hp hp2
    (Or.inl ⟨rfl, F, iF, hfin, hF, he⟩) hq S
  exact CFSG.CGT.PushingUpLit.SolK.gen2_of_dihedral_or_semidihedral (Or.inr ⟨S, m, hm, hS⟩)

theorem sectionalTwoRankLE_two_of_lieModel_psu_three {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSU 3 p f) (hq : p ^ f % 4 = 1) :
    CFSG.GH74.SectionalTwoRankLE X 2 := by
  obtain ⟨⟨-, hf, -⟩, F, iF, hfin, hF, he⟩ := h.statedClassicalModel (by decide)
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨m, hm, hS⟩ := CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_sd hp hp2
    (Or.inr ⟨rfl, F, iF, hfin, hF, he⟩) hq (Nat.one_lt_pow (by omega) hp.one_lt) S
  exact CFSG.CGT.PushingUpLit.SolK.gen2_of_dihedral_or_semidihedral (Or.inr ⟨S, m, hm, hS⟩)

end CFSG.LocalAnalysis.WeakClosure81

end
