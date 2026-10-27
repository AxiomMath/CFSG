module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

theorem excl_M12 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .M12) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12
  rw [CFSG.Sporadic.Mathieu.card_M12]
  norm_num

theorem excl_M24 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .M24) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.M24
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

theorem excl_J2 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .J2) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2
  rw [CFSG.Sporadic.J2.card_J2]
  norm_num

theorem excl_He {J : Type} [Group J] [Finite J]
    (e : IsSpor J .He) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.He
  rw [CFSG.Sporadic.He.card_He]
  norm_num

theorem excl_Ru {J : Type} [Group J] [Finite J]
    (e : IsSpor J .Ru) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Ru
  rw [CFSG.Sporadic.Ru.card_Ru]
  norm_num

theorem excl_J4 {J : Type} [Group J] [Finite J]
    (e : IsSpor J .J4) : Excl J := by
  obtain ⟨e⟩ := e
  refine Or.inl ?_
  unfold Big27
  rw [Nat.card_congr e.toEquiv]
  change 27 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J4
  rw [CFSG.Sporadic.J4.card_J4]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
