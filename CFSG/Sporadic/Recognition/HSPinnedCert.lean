module

public import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public import Mathlib.Data.Fintype.Card
public meta import Certificates.Data.CFSGNative.Recognition.HSPinnedData
public meta import Mathlib.Data.Fintype.Card
public import Certificates.Certificate6101

public section

namespace CFSG.Sporadic.Recognition.HSPinned

open CFSG.Sporadic.Recognition.HSPinned.Native CFSG.Sporadic.HS.Native
  CFSG.Sporadic.SmallF2.Native

theorem starsClosed_check :
    starsClosedOK (hsData.orbit ()).alpha (hsData.orbit ()).beta = true :=
  Certificates.certificate6101.1

theorem stars_lt : ∀ i < 100, ∀ t ∈ stars[i]!, t < 1100 :=
  Certificates.certificate6101.2.1

theorem stars_inj :
    ∀ i < 100, ∀ j < 100, i = j ∨ ∃ x ∈ stars[i]!, x ∉ stars[j]! :=
  Certificates.certificate6101.2.2.1

theorem tree_check : ∀ i < 100, 0 < i →
    vtxPar[i]! < i ∧ ((vtxLab[i]! = 1 ∧ vtxA[vtxPar[i]!]! = i) ∨
      (vtxLab[i]! = 2 ∧ vtxB[vtxPar[i]!]! = i)) :=
  Certificates.certificate6101.2.2.2.1

theorem wit_check : ∀ k < 20, wit[k]!.1 < 100 ∧ wit[k]!.2 < 100 ∧
    ∀ x < 1100, (x ∈ stars[wit[k]!.1]! ∧ x ∈ stars[wit[k]!.2]!) ↔ x = hsData.basis[k]! :=
  Certificates.certificate6101.2.2.2.2.1

theorem adj_spec : ∀ x < 100, ∀ y < 100,
    adjB x y = true ↔ (x ≠ y ∧ ∃ t ∈ stars[x]!, t ∈ stars[y]!) :=
  Certificates.certificate6101.2.2.2.2.2.1

end CFSG.Sporadic.Recognition.HSPinned
