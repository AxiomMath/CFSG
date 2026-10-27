module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

open CFSG.Assembly.LowTwoRank

theorem mem_statedSL_iff (m : ℕ) {K : Type} [Field K] (A : Matrix.GeneralLinearGroup (Fin m) K) :
    A ∈ StatedSL m K ↔ (A : Matrix (Fin m) (Fin m) K).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

@[expose] def statedSLEquiv (m : ℕ) {K : Type} [Field K] :
    Matrix.SpecialLinearGroup (Fin m) K ≃* StatedSL m K where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g, (mem_statedSL_iff m _).mpr g.2⟩
  invFun x := ⟨(x.1 : Matrix (Fin m) (Fin m) K), (mem_statedSL_iff m x.1).mp x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Units.ext rfl)
  map_mul' g h := Subtype.ext (map_mul Matrix.SpecialLinearGroup.toGL g h)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
