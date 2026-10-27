module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueeze
import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLin

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_jBlockOmega_of (hA : DFixBlockLeaf) (hB : DPlaneCountLeaf) : DJBlockOmegaLeaf := by
  intro hRig F _ _ _ hF V _ _ _ Q hQ ℓ hdim hℓ E hE hsc t ht C hC hlab
  obtain ⟨hfix, htriv⟩ := hA hRig F hF V Q hQ ℓ hdim hℓ t (hE.2 t ht) C hC hlab
  exact hB F hF V Q hQ ℓ hdim hℓ E hE hsc t ht hfix C hC.1 htriv

theorem d_kModel_of_side (hFr : DFrameOmegaLeaf) (hT3 : DJBlockOmegaLeaf) (hS : DSideCoordLeaf) :
    DKModelLeaf := by
  intro hRig hLB G _ _ p B Bs x L D J y K hH hpFact hrow
  have hsq := d_kSqueeze hRig hLB hFr hT3 hH hrow
  obtain ⟨-, labX, -, hX2, -, hXlab, hp3, -, hXtag, -, hXn, -, hXr6⟩ := hrow
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hy1 : y ≠ 1 := hH.2.2.2.2.1.1.2.2.1
  have h4 : p ^ 4 ≤ Nat.card ↥Bs := hH.1.tableB_facts.2.2.2.2
  have hM : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨n, τ, hτ, hmod⟩ :=
    hS hRig G p B Bs K y hyBs hp3 hBs hM ⟨labX, hX2, hXlab, hXtag, hXn, hXr6⟩ hy1 hsq h4
  refine ⟨?_, fun e he => by rwa [← hsq]⟩
  rcases hmod with ⟨hn6, hcoord⟩ | ⟨hn5, hcoord⟩
  · obtain ⟨V, hV, hVp, ι, b, hyb, hAK⟩ :=
      d_linearModel_of_dcoord p Bs K n y hyBs τ hτ hcoord
    exact ⟨n, V, hV, hVp, ι, b, hyBs, hp3, hyb, Or.inl ⟨hn6, hAK⟩⟩
  · obtain ⟨V, hV, hVp, ι, b, hyb, hAK⟩ :=
      c2_linearModel_of_coord p Bs K n y hyBs τ hτ hcoord
    exact ⟨n, V, hV, hVp, ι, b, hyBs, hp3, hyb, Or.inr ⟨hn5, hAK⟩⟩

end CFSG.StandardType.HdRo7D
