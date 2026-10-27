module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CAssembly
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLOrderDict
import CFSG.LocalAnalysis.StandardType.GGHdRo7CAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7CFixGen
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKContra
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7CKStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLin
import CFSG.LocalAnalysis.StandardType.GGHdRo7CNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7CRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResCorank2CInput_proved
    (hTCJ : GGTCJKnown) (hX : GGResXDichotomyInput) (hJ : GGTBJInputR) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hKG : GGPumpCLabelKnown) : GGResCorank2CInput :=
  ggResCorank2CInput_of_leaves hTCJ hX hJ hRig hLB c2_normalizer_holds c2_refl_holds
    c2_kcontra_holds (c2_lmodel_of_coord c2_lcoord_holds hRig)
    noTV_holds xDatumGraph_holds c2_aj_holds (c2_kmodel_of_coord c2_kcoord_holds)
    c2_kstab_holds (c2_lorder_of_dict hKG) c2_lfixgen_holds

theorem ggResLeviLE3_join_of_sp_innerDiag
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L)
    (hD23 : GGResLeviDatumLE3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumLE3 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨n, hx, τ, hp3, hn, hτx, hcoord⟩ :=
    hdRo7CLCoordAux_coordModel_of_innerDiag p B Bs x L D J y K hH hM
  obtain ⟨V, hV, hVp, ι, b, hxb, hAL⟩ :=
    c2_linearModel_of_coord p Bs L n x hx τ hτx hcoord
  let := hV
  let := hVp
  exact ggResLeviLE3_join_of_signedModel hH hp3 ι b hx hn hxb hAL
    (HdRo7LNC.lnc_of_innerDiag_sp hM) hD23

theorem ggResLeviExact2_join_of_sp_innerDiag
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L)
    (hD2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  apply ggResLeviLE3_join_of_sp_innerDiag hH hM
  rcases hD2 with hD | hD
  · exact Or.inl
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K ggSelAny ggTypAny).mpr (Or.inl hD))
  · exact Or.inr
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs K J L ggSelAny ggTypAny).mpr (Or.inl hD))

theorem ggResLeviExact3_join_of_sp_innerDiag
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L)
    (hD3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  apply ggResLeviLE3_join_of_sp_innerDiag hH hM
  rcases hD3 with hD | hD
  · exact Or.inl
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs L J K ggSelAny ggTypAny).mpr (Or.inr hD))
  · exact Or.inr
      ((ggResLeviDatumLE3_iff_exact2_or_exact3 p Bs K J L ggSelAny ggTypAny).mpr (Or.inr hD))

end CFSG.StandardType.HdRo7C

end
