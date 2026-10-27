module

public import CFSG.Quasithin.Background.RonanG73Odd1
public import CFSG.Quasithin.Background.RonanG73OddL2
public import CFSG.Quasithin.Background.RonanG73OddU3

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem clause1
    {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hq : CFSG.IsQuasisimple ↥L) (hS : CFSG.SectionRank.IsSQTKCat ↥L)
    (hodd : ∃ (t : StatedLieTag) (n p f : ℕ), p ≠ 2 ∧
      (StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) t n p f ∨
        ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) t p f ∨
        ReeTitsModel (↥L ⧸ Subgroup.center ↥L) t p f)) :
    (IsPSL 2 2 2 ↥L ∨ IsPSL 3 2 1 ↥L ∨
        Nonempty (↥L ≃* ↥⁅StatedSp 2 (ZMod 2), StatedSp 2 (ZMod 2)⁆) ∨
        IsHat ↥L ↥(alternatingGroup (Fin 6))) ∨
      (IsPSU 3 3 1 ↥L ∧ Module.finrank (ZMod 2) V = 6) := by
  haveI : Finite (GLV V) :=
    CFSG.Quasithin.Background.Harris.OrdinaryProofs.finite_GLV_of_finite (V := V)
  have hSQT : CFSG.IsStronglyQuasithin (↥L ⧸ Subgroup.center ↥L) := sqt_quotient_center hS hq
  obtain ⟨p, hp, hp2, hcases⟩ := odd_model_restriction hSQT hodd
  rcases hcases with ⟨f, hf, hm⟩ | hm | hm
  · exact Or.inl (clause1_psl2 h hq hp hp2 hf hm)
  · exact (false_of_psl3 h hp hp2 hm).elim
  · exact Or.inr (clause1_psu3 h hq hp hp2 hm)

end CFSG.Quasithin.RonanG73
