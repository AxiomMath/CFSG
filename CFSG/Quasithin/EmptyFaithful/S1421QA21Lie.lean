module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21D4
public import CFSG.Quasithin.EmptyFaithful.S1421QA21F4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtMain

public section

namespace CFSG.Quasithin.QA21

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Rk2

theorem borelPkg_sp4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ∃ P : Fin 2 → Subgroup X, BorelPkg X U P := by
  obtain ⟨P, hP, hE⟩ := rank2PkgExt_exists_sp4 hf hX hU
  exact ⟨P, ⟨hP.res, hP.norm, hE.solvable_le_normalizer⟩⟩

theorem borelPkg_of_isLieBig
    {X : Type} [Group X] [Finite X]
    (h : (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel X .PSp 2 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .trialityD4 2 f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel X .twistedF4 2 f))
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : ∃ P : Fin 2 → Subgroup X, BorelPkg X U P := by
  rcases h with ⟨f, hf, hX⟩ | ⟨f, -, hX⟩ | ⟨f, hf, hX⟩ | ⟨f, -, -, hX⟩
  · exact borelPkg_sp4 hf hX hU
  · exact borelPkg_g2 hX hU
  · exact borelPkg_3d4 hf hX hU
  · exact borelPkg_2f4 hX hU

end CFSG.Quasithin.QA21
