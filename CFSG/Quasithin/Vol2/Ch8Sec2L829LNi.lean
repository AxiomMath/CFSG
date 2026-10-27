module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNk
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def L32Residual {G : Type} [Group G] (H T M K : Subgroup G) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (E2.StarQuot M H))
  T ≤ Subgroup.normalizer (K : Set G) ∧
  (∀ x : G, x ∈ kerIn M H ↔
    x ∈ K ⊔ pCoreOf 2 H ∧ ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
  ((IsPSL 3 2 1 ↥Ks ∧ E2.IsDiagramNontrivial Ts Ks TKs ∧ E2.IsBorelIn Ks MKs) ∨
   (IsPSL 2 7 1 ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (E2.StarQuot M H)) ∧
    8 < E2.autCard Ts Ks))

end CFSG.Quasithin.H13.L829N
