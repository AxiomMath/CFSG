module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0
import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L2

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering129C

theorem comm_centralizer_projSL_two {F : Type} [Field F] [Finite F] {S : Type} [Group S]
    (φ : S ≃* projSL 2 F) :
    ∀ s : S, orderOf s = 3 → ∀ a b : S, a ∈ Subgroup.centralizer ({s} : Set S) →
      b ∈ Subgroup.centralizer ({s} : Set S) → a * b = b * a := by
  intro s hs3 a b ha hb
  set ψ : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    φ.trans (Sec4.projSLEquivPSL F)
  have hπ : GH74.GLS.IVK.Proofs2.IsCentralQuot
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
    ⟨QuotientGroup.mk'_surjective _, fun x => QuotientGroup.eq_one_iff x⟩
  have hs1 : ψ s ≠ 1 := by
    intro h1
    have : s = 1 := ψ.injective (by rw [h1, map_one])
    rw [this, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have hs3' : ψ s ^ 3 = 1 := by
    rw [← map_pow, ← hs3, pow_orderOf_eq_one, map_one]
  have hca : ψ a * ψ s = ψ s * ψ a := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp ha]
  have hcb : ψ b * ψ s = ψ s * ψ b := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hb]
  have h := hπ.centralizer_comm_of_odd hs1 (r := 3) (by decide) hs3' hca hcb
  apply ψ.injective
  rw [map_mul, map_mul, h]

theorem kFCensus46One_holds : KFCensus46One := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨p, e, hp, hp2, he, ⟨φ⟩⟩ := hQ
  haveI : Finite (GaloisField p e) := inferInstance
  obtain ⟨g, hg⟩ := (ppair_self hD).map φ
  exact hg.false_of_comm_centralizer (comm_centralizer_projSL_two (S := projSL 2 (GaloisField p e))
    (MulEquiv.refl _) _ hg.orderOf_s)

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
