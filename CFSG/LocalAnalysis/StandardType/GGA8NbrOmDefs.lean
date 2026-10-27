module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LieType.Universal.Catalog
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue

public section

namespace CFSG.StandardType

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal

namespace A8Coord

abbrev OmV : Type := Fin (2 * 4) → GaloisField 2 3

noncomputable abbrev omQ : QuadraticForm (GaloisField 2 3) OmV :=
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus 4
    (GaloisField 2 3) (by norm_num) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2

noncomputable abbrev omΩ : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV) := orthDerived omQ

end A8Coord

namespace CoordOm

open Multiplicative

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def FrameMovesAll {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) (O : Subgroup (ZMod p)ˣ) : Prop :=
  ∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ), (∀ i, η i ∈ O) →
    ∃ w ∈ orthDerived Q ⊓ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)), ∀ s : Fin r → ZMod p,
      w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd fun i => (η i : ZMod p) * s (π i))

@[expose] def FrameAligned {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q p A r) (ζ : Kˣ) : Prop :=
  ∀ i : Fin r, ∃ u ∈ F.U i, u ≠ 0 ∧ F.ι (ofAdd (Pi.single i 1)) u = (ζ : K) • u

end CoordOm

namespace A8Coord

@[expose] noncomputable def omA {G : Type} [Group G] (φ : ↥omΩ →* G) (Bs : Subgroup G) :
    Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV) :=
  (Bs.comap φ).map omΩ.subtype

theorem omA_le {G : Type} [Group G] (φ : ↥omΩ →* G) (Bs : Subgroup G) : omA φ Bs ≤ omΩ :=
  Subgroup.map_subtype_le _

end A8Coord

end CFSG.StandardType

end
