module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem isQuasisimple_of_mulEquiv_centralQuotient {A X : Type*} [Group A] [Group X]
    (hA : CFSG.IsQuasisimple A) (e : X ≃* A ⧸ Subgroup.center A) : CFSG.IsQuasisimple X := by
  obtain ⟨-, hs, a, b, hab⟩ := hA
  have : IsSimpleGroup X := e.isSimpleGroup
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩).1

theorem rankTwoQuasisimple_holds : RankTwoQuasisimple := by
  intro X _ n _ h
  rcases h with ⟨K, _, _, -, ⟨e⟩⟩ | h | h | h
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)
  · rcases h with ⟨-, -, K, _, _, -, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact isQuasisimple_of_mulEquiv_centralQuotient
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 K le_rfl)
        (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm)
    all_goals exact absurd h0 (by decide)
  · rcases h with ⟨-, hadm, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact isQuasisimple_of_mulEquiv_centralQuotient
        (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible 2 K hadm hK)
        (e.trans (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 2 K).symm)
    all_goals exact absurd h0 (by decide)
  · rcases h with ⟨ht, -⟩ | ⟨-, -, ⟨-, -, -, h3⟩, K, _, _, hK, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact isQuasisimple_of_mulEquiv_centralQuotient
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K (hK ▸ h3)) e
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)

end CFSG.Quasithin.Vol2.Ch11
