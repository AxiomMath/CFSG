module

public import CFSG.Monster.SteinbergMCatalogInner
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Blueprint

theorem ggSporK_inner_M_of_simple
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group] :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic .M).Group, ∃ g, φ = MulAut.conj g := by
  intro hS φ
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.BMCase.catalogM_mulAut_mem_inner _ hS
    ⟨e.symm⟩ φ
  exact ⟨g, hg.symm⟩

end CFSG.StandardType.SporadicShape
