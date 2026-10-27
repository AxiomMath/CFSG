module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumI
public import CFSG.Quasithin.EmptyFaithful.Insp7NumK
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def SmallSimple' (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨ StatedClassicalModel L .PSU 3 2 2 ∨
    StatedClassicalModel L .PSp 2 2 2 ∨ StatedClassicalModel L .PSL 4 2 1 ∨
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel L .PSU 3 3 1

theorem numFactAt_smallSimple
    (h : NumFactAt SmallSimple') : NumFactAt SmallSimple :=
  numFactAt_of_cover (G := SmallSimple') (H := fun L _ => SuzukiModel L 2 3)
    (fun L _ hL => by
      unfold SmallSimple at hL
      unfold SmallSimple'
      tauto) h numFactAt_sz8

theorem lemma14320Inspect_final
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallSimple') (hT : NumFactAt LargeReeTits) (hO : NumFactAt L33Fam)
    (hP : NumFactAt SporSimple) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_simple_groups hbig hsimple (numFactAt_smallSimple hS) hT hO hP

end Insp7

end CFSG.Quasithin
