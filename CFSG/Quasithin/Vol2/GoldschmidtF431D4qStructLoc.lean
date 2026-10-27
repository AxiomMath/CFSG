module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructExt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructTwoOut

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique

section Local

variable {D D' : Type} [Group D] [Group D'] {G : Type} [Group G] {M1 M2 : Subgroup G}

theorem KIso.map_Mb1 {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A') :
    A'.Mb1.map L.ψ.symm.toMonoidHom = A.Mb1 := by
  ext k
  rw [Subgroup.mem_map_equiv]
  simpa using L.mem1 k

theorem KIso.map_Mb2 {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A') :
    A'.Mb2.map L.ψ.symm.toMonoidHom = A.Mb2 := by
  ext k
  rw [Subgroup.mem_map_equiv]
  simpa using L.mem2 k

theorem KIso.card_K {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A') :
    Nat.card ↥A'.K = Nat.card ↥A.K :=
  (Nat.card_congr L.ψ.toEquiv).symm

end Local

section TwoOut

variable {D D' : Type} [Group D] [Group D']

@[expose] def TwoOutConcl (A : LieAmalgamExt D) : Prop :=
  ∃ (T S : Subgroup ↥A.K) (g z : ↥A.K) (I : Finset ↥A.K),
    F431TwoOut T S g A.Mb1 A.Mb2 z I ∨ F431TwoOut T S g A.Mb2 A.Mb1 z I

theorem KIso.twoOutConcl {A : LieAmalgamExt D} {A' : LieAmalgamExt D'} (L : KIso A A')
    [Finite ↥A.K] [Finite ↥A'.K] : TwoOutConcl A' → TwoOutConcl A := by
  rintro ⟨T', S', g', z', I', h | h⟩
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g',
      L.ψ.symm z', I'.map L.ψ.symm.toEquiv.toEmbedding, Or.inl ?_⟩
    have := F431TwoOut.map L.ψ.symm h
    rwa [L.map_Mb1, L.map_Mb2] at this
  · refine ⟨T'.map L.ψ.symm.toMonoidHom, S'.map L.ψ.symm.toMonoidHom, L.ψ.symm g',
      L.ψ.symm z', I'.map L.ψ.symm.toEquiv.toEmbedding, Or.inr ?_⟩
    have := F431TwoOut.map L.ψ.symm h
    rwa [L.map_Mb1, L.map_Mb2] at this

end TwoOut

end CFSG.Quasithin.H13.F431.D4q.Struct
