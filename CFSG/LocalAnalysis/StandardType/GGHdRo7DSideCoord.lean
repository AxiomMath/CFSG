module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideData
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideModel

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

theorem d_sideCoord_exact (hFr : DFrameOmegaLeaf) (hRig : GGLabelRigidInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G} {z : G} (hz : z ∈ Bs) (hp3 : p = 3)
    (hBs : GGBstar p B Bs) (hM : GGInnerDiagOn Bs X) {lab : LargeEvenLabel}
    (hlabΛ : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1) (hr : 4 ≤ lab.rank) (hz1 : z ≠ 1)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z)
    (h4 : p ^ 4 ≤ Nat.card Bs) :
    ∃ (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod p)) ≃* ↥Bs),
      τ (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod p))) = ⟨z, hz⟩ ∧
      ((n = lab.rank ∧ DCoordModel p Bs X n τ) ∨
        (n + 1 = lab.rank ∧ C2CoordModel p Bs X n τ)) := by
  obtain ⟨hnorm, hinner, hcop, hfr⟩ := d_sideData hRig hFr hp3 hM hlabΛ hhas htag hn hr
  have hp : p.Prime := hp3 ▸ Nat.prime_three
  have hsplit := ggBstar_split_of_inner_coprime hp hBs
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop) hnorm hinner
  exact d_coordModel_of_frame hp hBs hsplit hcop hz hz1 hC h4 hfr

theorem d_sideCoord_of_frame (hFr : DFrameOmegaLeaf) : DSideCoordLeaf := by
  intro hRig G _ _ p B Bs X z hz hp3 hBs hM hlab hz1 hC h4
  obtain ⟨lab, hlabΛ, hhas, htag, hn, hr⟩ := hlab
  obtain ⟨n, τ, hτ, hmod⟩ :=
    d_sideCoord_exact hFr hRig hz hp3 hBs hM hlabΛ hhas htag hn (by omega) hz1 hC h4
  refine ⟨n, τ, hτ, ?_⟩
  rcases hmod with ⟨hnr, hc⟩ | ⟨hnr, hc⟩
  · exact Or.inl ⟨by omega, hc⟩
  · exact Or.inr ⟨by omega, hc⟩

end CFSG.StandardType.HdRo7D
