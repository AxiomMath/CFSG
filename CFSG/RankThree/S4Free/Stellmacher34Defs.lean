module

public import CFSG.RankThree.S4Free.Stellmacher24Ext
public import CFSG.RankThree.S4Free.StellmacherNatSz
public import CFSG.RankThree.S4Free.StellmacherHosts
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.RankThree.S4Free.Stell34

universe u

@[expose] def Hyp24Sz : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], SzSections H → ∀ {S M A : Subgroup H},
    Stell.Hyp24 S M A → ∃ L, Stell.IsL24 S M A L ∨ Stell.IsL24Sz S M A L

@[expose] def Hyp25dSz : Prop :=
  ∀ (V : Type u) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (S M A L : Subgroup (MulAut V)) (Z₀ : Subgroup V),
      Stell.IsL24Sz S M A L → IsPGroup 2 S → S ≤ M → CFSG.Open.IsElemAbelian 2 A →
      CFSG.Quasithin.IsQuadratic A → Z₀ ≤ CFSG.Quasithin.fixV A →
      L ⊓ CFSG.Quasithin.stabSub Z₀ ≤ M →
      (∀ U : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ U) → U = ⊤) →
      CFSG.Quasithin.fixV L = ⊥ → oTwo ↥L = ⊥ →
      ∃ n, 1 ≤ n ∧ ∃ ψ : ↥L →* CFSG.Open.Sz n, Function.Surjective ψ ∧
        Stell.IsNatSzProduct n ψ L.subtype

end CFSG.RankThree.S4Free.Stell34
