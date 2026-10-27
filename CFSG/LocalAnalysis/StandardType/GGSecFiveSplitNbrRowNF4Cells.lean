module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNInvol
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNF4Frame
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_frame_F4Split
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  rintro Q ⟨K, _, _, hK, hQ⟩
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
    ggTorusFrame_of_involFrameElt hp (TableBF4.center_recipeGroup_eq_bot K)
      (fun _ hφ _ => TableBF4.idImage_subset_inn K hφ) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
      (ggTorusInvolFrameElt_F4Split hp hp2 hpq)⟩

theorem largeEvenLabelAll_frame_F4Plus
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel}
    (h : lab.tag = .F4 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  rintro Q ⟨K, _, _, hK, hQ⟩
  have : CharP K 2 := charP_two_of_card hK
  have hp2 : p ≠ 2 := by omega
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 3, ggTorusLift_F4Plus hp hp2 hpq,
    ggTorusFrame_of_involFrameElt hp (TableBF4.center_recipeGroup_eq_bot K)
      (fun _ hφ _ => TableBF4.idImage_subset_inn K hφ) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
      (ggTorusInvolFrameElt_F4Plus hp hp5 hpq 3)⟩

theorem ggRowNF4Cells_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_NF4 p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))
      p Bs K) : False :=
  ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun q hp hp2 _ _ h => h.1.2.elim
      (fun hd => largeEvenLabelAll_frame_F4Split hp hp2 ⟨h.1.1, hd⟩)
      (fun hd => largeEvenLabelAll_frame_F4Plus hp (by
        have h4 : q ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        have h3 : q ≠ 3 := fun h3 => h.2 ⟨h3, hd⟩
        have := hp.two_le
        omega) ⟨h.1.1, hd⟩))
    hcfg hpres hle3 hK hrow

end CFSG.StandardType

end
