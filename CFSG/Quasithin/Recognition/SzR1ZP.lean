module

public import CFSG.Quasithin.Recognition.SzR1Fam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F112W CFSG.Quasithin.CosetGeom CFSG.Quasithin.A5Model
open scoped commutatorElement

namespace SzR1

@[expose] noncomputable def famCtxOfFive {G : Type} [Group G] [Finite G]
    {K1 L2 S Zs : Subgroup G} (C : F112J2.FiveCtx K1 L2 S Zs) : FamCtx K1 L2 S Zs (Fin 5) where
  h := C.h
  hR := C.hR
  D :=
    { act := (alternatingGroup (Fin 5)).subtype.comp C.D.θ
      pt := 4
      trans := fun ω => by
        obtain ⟨k, hk⟩ := C.D.exists_kf ω
        exact ⟨k, hk⟩
      stab := fun k => C.D.stab k }
  twoTrans := fun {a b c d} hab hcd => by
    obtain ⟨g, hg1, hg2⟩ := F112J2.a5_two_trans hab hcd
    obtain ⟨k, hk⟩ := C.D.surj g
    refine ⟨k, ?_, ?_⟩
    · show ((C.D.θ k : A5) : Equiv.Perm (Fin 5)) a = c
      rw [hk]
      exact hg1
    · show ((C.D.θ k : A5) : Equiv.Perm (Fin 5)) b = d
      rw [hk]
      exact hg2
  hcomm := C.hcomm

end SzR1

end CFSG.Quasithin
