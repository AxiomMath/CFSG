module

import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem lieModel_twistedE6_iff {G : Type} [Group G] {n f : ℕ} :
    LieModel G .twistedE6 n 2 f ↔ n = 0 ∧ ChevalleyExceptionalModel G .twistedE6 2 f :=
  CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)

theorem lieModel_trialityD4_iff {G : Type} [Group G] {n f : ℕ} :
    LieModel G .trialityD4 n 2 f ↔ n = 0 ∧ ChevalleyExceptionalModel G .trialityD4 2 f :=
  CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)

theorem lieModel_twistedF4_iff {G : Type} [Group G] {n f : ℕ} :
    LieModel G .twistedF4 n 2 f ↔ n = 0 ∧ ReeTitsModel G .twistedF4 2 f :=
  CFSG.Blueprint.LieModel.reeTits_iff (by decide)

theorem lieModel_Tits_iff {G : Type} [Group G] {n f : ℕ} :
    LieModel G .Tits n 2 f ↔ n = 0 ∧ ReeTitsModel G .Tits 2 f :=
  CFSG.Blueprint.LieModel.reeTits_iff (by decide)

theorem lieModel_twistedB2_iff {G : Type} [Group G] {n f : ℕ} :
    LieModel G .twistedB2 n 2 f ↔ n = 0 ∧ SuzukiModel G 2 f :=
  CFSG.Blueprint.LieModel.twistedB2_iff

end CFSG.RankThree.PartOne.Sec66T
