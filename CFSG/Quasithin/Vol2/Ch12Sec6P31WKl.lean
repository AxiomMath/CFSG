module

public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

theorem psl224Alt5_w31 (X : Type) [Group X]
    (h : IsPSL 2 2 2 X) : IsAlt 5 X := by
  obtain ⟨-, F, hFld, hFin, hcard, ⟨e⟩⟩ := h
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
    (Or.inl (by rw [hcard]; norm_num))
  exact ⟨e.trans e5⟩

end CFSG.Quasithin.H13
