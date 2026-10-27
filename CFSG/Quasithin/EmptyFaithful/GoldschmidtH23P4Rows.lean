module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Cen
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

structure P4Rows : Prop where
  alt6 : RowOK ↥(alternatingGroup (Fin 6))
  alt7 : RowOK ↥(alternatingGroup (Fin 7))
  sl32 : RowOK ↥(StatedSL 3 (ZMod 2))
  psl4 : ∀ {X : Type} [Group X] [Finite X], IsPSL 4 2 1 X → RowOK X
  psl5 : ∀ {X : Type} [Group X] [Finite X], IsPSL 5 2 1 X → RowOK X
  psu33 : ∀ {X : Type} [Group X] [Finite X], IsPSU 3 3 1 X → RowOK X
  d4 : ∀ {X : Type} [Group X] [Finite X], Is3D4 2 1 X → RowOK X
  tits : ∀ {X : Type} [Group X] [Finite X], IsTits X → RowTits X
  m11 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .M11 X → RowOK X
  m12 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .M12 X → RowOK X
  m22 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .M22 X → RowOK X
  m23 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .M23 X → RowOK X
  m24 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .M24 X → RowOK X
  j2 : ∀ {X : Type} [Group X] [Finite X], IsSporadic .J2 X → RowOK X
  hs : ∀ {X : Type} [Group X] [Finite X], IsSporadic .HS X → RowOK X
  he : ∀ {X : Type} [Group X] [Finite X], IsSporadic .He X → RowOK X
  ru : ∀ {X : Type} [Group X] [Finite X], IsSporadic .Ru X → RowOK X

end CFSG.Quasithin.H23P4
