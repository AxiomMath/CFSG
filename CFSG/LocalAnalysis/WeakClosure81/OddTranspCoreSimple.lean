module

public import CFSG.Milestones.CL_LIT_Fischer_three_transposition_theorem
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarUnitary
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarOrth
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarRefl
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarFischer
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarSp
import CFSG.LargeExtraspecial.S12InspFamSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Open

theorem permOrStar_of_hyp
    {G : Type} [Group G] [Finite G] {t : G} (hP : Pair G {x | IsConj t x})
    (hZ : Subgroup.center G = ⊥) (hS : IsSimpleGroup (commutator G)) :
    (∃ n : ℕ, ∃ e : G ≃* Equiv.Perm (Fin n), (e t).IsSwap) ∨ HasCoreStar G t := by
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned G {x | IsConj t x}
      ⟨t, rfl⟩ hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hZ hS with
    ⟨m, -, φ, hφ⟩ | ⟨m, hm, b, halt, hnd, hM⟩ | ⟨m, hm, Q, hnd, hex, hM⟩ | ⟨m, hm, hM⟩ |
      ⟨m, hm, f, hsym, hnd, hM⟩ | ⟨φ, hφ, hu⟩ | ⟨φ, hφ, hu⟩ | ⟨φ, hφ, hu⟩
  · exact Or.inl ⟨m, φ, (hφ t).mp (IsConj.refl t)⟩
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      obtain ⟨φ, hφ⟩ := CFSG.LargeExtraspecial.S12Insp5.exists_perm_six_of_sp_two
        ⟨t, IsConj.refl t, fun _ => Iff.rfl⟩ halt hnd hM
      exact Or.inl ⟨6, φ, (hφ t).mp (IsConj.refl t)⟩
    · exact Or.inr (hasCoreStar_of_spModel hP hm3 halt hnd hM)
  · exact permOrStar_of_orthModel hP hm hnd hex hM
  · exact Or.inr (hasCoreStar_of_unitaryModel hP hm hM)
  · exact Or.inr (hasCoreStar_of_reflModel hP hm hsym hnd hM)
  · exact Or.inr (hasCoreStar_of_fi22 hP φ hφ hu)
  · exact Or.inr (hasCoreStar_of_fi23 hP φ hφ hu)
  · exact Or.inr (hasCoreStar_of_fi24 hP φ hφ hu)

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
