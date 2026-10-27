module

public import CFSG.Quasithin.EmptyFaithful.ModHS12
public import CFSG.Quasithin.EmptyFaithful.ModHS22
public import CFSG.Quasithin.EmptyFaithful.ModHS23
public import CFSG.Quasithin.EmptyFaithful.ModHS24
public import CFSG.Quasithin.EmptyFaithful.SBd13Main

public section

namespace CFSG.Quasithin.ModH

open CFSG.Blueprint CFSG.Quasithin.R3c14 CFSG.QuasithinUnique.Ch1

@[expose] def NoElConfigRest : Prop :=
  ¬ ElConfig (NativeSporadic.Carrier .J2) ∧ ¬ ElConfig (NativeSporadic.Carrier .J4) ∧
    ¬ ElConfig (NativeSporadic.Carrier .HS) ∧ ¬ ElConfig (NativeSporadic.Carrier .He) ∧
    ¬ ElConfig (NativeSporadic.Carrier .Ru)

theorem input15343ElimSporadicNoM11_of_elRest
    (h : NoElConfigRest) : SBd13.Input15343ElimSporadicNoM11 := by
  apply SBd13.input15343ElimSporadicNoM11_of_el
  intro s hs hne
  obtain ⟨hJ2, hJ4, hHS, hHe, hRu⟩ := h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact S12.not_elConfig
  · exact S22.not_elConfig
  · exact S23.not_elConfig
  · exact S24.not_elConfig
  · exact hJ2
  · exact hJ4
  · exact hHS
  · exact hHe
  · exact hRu

end CFSG.Quasithin.ModH
