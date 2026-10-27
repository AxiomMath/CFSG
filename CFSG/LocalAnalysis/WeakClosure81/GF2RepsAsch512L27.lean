module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.Quasithin.EmptyFaithful.E22QTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.Blueprint (LieModel)

theorem not_hasUniqueMaxOver_of_psl_two_seven {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 2 7 1) {T : Subgroup Y} (hT : IsSylowIn 2 T ⊤) :
    ¬ HasUniqueMaxOver T := by
  rintro ⟨M, hMtop, hM⟩
  have h32 : StatedClassicalModel Y .PSL 3 2 1 :=
    StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven
      (h.statedClassicalModel (by decide))
  obtain ⟨P, hne, hTP, hmax, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_classical_proper_Sylow_overgroup_residual
      (U := T) hT (Or.inl ⟨1, h32⟩)
  have hPM : ∀ j, P j = M := fun j => by
    have hcov : P j ⋖ ⊤ := (hmax (P j) (hTP j)).2 ⟨j, rfl⟩
    exact (hM (P j) (hTP j) hcov.lt).eq_of_not_lt fun hlt => hcov.2 hlt hMtop
  exact hne ((hPM 0).trans (hPM 1).symm)

theorem isPGL2_seven_of_ne_top {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y} [E.Normal]
    (hE : LieModel ↥E .PSL 2 7 1) (hC : Subgroup.centralizer (E : Set Y) = ⊥) (hne : E ≠ ⊤) :
    CFSG.Quasithin.F6.IsPGL2 7 Y := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  rcases CFSG.Quasithin.E2.E22N.typeIIo_transport (p := 7) le_rfl
      (hE.statedClassicalModel (by decide)) hC with h | ⟨e, -⟩
  · exact absurd h hne
  · have hcs : Subgroup.center (GL (Fin 2) (ZMod 7)) = StatedScalars (Fin 2) (ZMod 7) :=
      Matrix.GeneralLinearGroup.center_eq_range_scalar
    exact ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod 7,
      ⟨e.trans (QuotientGroup.quotientMulEquivOfEq hcs)⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
