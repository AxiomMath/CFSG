module

public import CFSG.LocalAnalysis.StandardType.GGDepED4ReadDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4L58RowDefs
public import CFSG.LocalAnalysis.StandardType.GGHL58NbrTorRow
public import CFSG.LocalAnalysis.StandardType.GGDepED4KGuard
public import CFSG.LocalAnalysis.StandardType.GGTWHLTorRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4LCovered (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTBTorCov p lab ∧ ¬ GGTBWExcl lab ∧ ¬ GGOutdiagTwistedLabel lab

@[expose] def GGDepED4L58NbrRestInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p k : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → p = 3 →
    Nat.card ↥Bs = 3 ^ 6 →
    (x ∉ L → y ∉ K → (k = 1 ∨ k = 2) → GGDepED4Aligned p k Bs L J K →
      GGResRowAt ggRowTwoNodeSmallJD p J L → (k = 2 → GGResRowAt ggRowTwoNode p J K) →
      (¬ GGInnerDiagOnLabel GGDepED4LCovered p Bs L → GGTWHLAt p Bs L x) ∧
        (Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
          ¬ GGInnerDiagOnLabel GGDepED4KCovered p Bs K → GGTWHLAt p Bs K y)) ∧
    (y ∉ K → GGDepED4Aligned p 1 Bs K J L → GGResRowAt ggRowTwoNodeSmallJD p J K →
      (¬ GGInnerDiagOnLabel GGDepED4LCovered p Bs L → GGTWHLAt p Bs L x) ∧
        (Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
          ¬ GGInnerDiagOnLabel GGDepED4KCovered p Bs K → GGTWHLAt p Bs K y))

theorem ggDepED4L58RowInput_of_nbrrest
    (hRig : GGLabelRigidInput) (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hW : GGTBWNormLabelInput) (hFixK : GGTBFixNbrInput) (hRest : GGDepED4L58NbrRestInput) :
    GGDepED4L58RowInput := by
  intro G _ _ p k _ B Bs x L D J y K hH hp3 hc
  have hbaseL : (¬ GGInnerDiagOnLabel GGDepED4LCovered p Bs L → GGTWHLAt p Bs L x) →
      GGTWHLAt p Bs L x := by
    intro hr
    by_cases hcov : GGInnerDiagOnLabel GGDepED4LCovered p Bs L
    · exact ggTWHL_of_tbTor_row hRig hT hLift hW hH hcov
    · exact hr hcov
  have hbaseK : y ∉ K → Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
      (¬ GGInnerDiagOnLabel GGDepED4KCovered p Bs K → GGTWHLAt p Bs K y) → GGTWHLAt p Bs K y := by
    intro hyK hCent hr
    by_cases hcov : GGInnerDiagOnLabel GGDepED4KCovered p Bs K
    · exact ggHL58Nbr_of_tbTor_row hT hLift hW hH hyK hCent hcov
    · exact hr hcov
  refine ⟨fun hxL hyK hk hA hrL hrK => ?_, fun hyK hA hrK => ?_⟩
  · have hCent := ggDepED4KGuard_holds hFixK G p k B Bs x L D J y K hH hp3 hc hxL hyK hk hA
    obtain ⟨h1, h2⟩ := (hRest G p k B Bs x L D J y K hH hp3 hc).1 hxL hyK hk hA hrL hrK
    exact ⟨hbaseL h1, hbaseK hyK hCent (h2 hCent)⟩
  · obtain ⟨h1, h2⟩ := (hRest G p k B Bs x L D J y K hH hp3 hc).2 hyK hA hrK
    exact ⟨hbaseL h1, fun hCent => hbaseK hyK hCent (h2 hCent)⟩

end CFSG.StandardType

end
