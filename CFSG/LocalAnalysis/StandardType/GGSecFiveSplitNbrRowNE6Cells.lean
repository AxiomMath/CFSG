module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Frame
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwE6Frame
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwAMCells
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_frame_E6Two
    {lab : LargeEvenLabel} (h : lab.tag = .E6 ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A → GGTorusFrame 3 A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hn1⟩ := h
  dsimp only at ht hn1
  subst ht hn1
  rintro Q ⟨K, _, _, hK, hQ⟩
  have : CharP K 2 := charP_two_of_card hK
  have hK2 : Nat.card K = 2 := hK.trans (pow_one 2)
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4, TableBExc.E6Three.ggTorusLift_E6_two,
    ggTorusFrame_of_involFrameElt Nat.prime_three (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun _ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK2 hφ)
      (ggCenterPrime_recipe_E6_two hK2 Nat.prime_three) (ggTorusInvolFrameElt_E6Two hK2)⟩

theorem largeEvenLabelAll_frame_twE6Dvd
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  refine TwE6Delta.labelAll h.1 fun K _ _ hK => ⟨4, ggTorusLift_twE6Dvd hlab.1 hK hp hp2 h.2, ?_⟩
  have hZ := TwE6Delta.center_recipeR_eq_bot hlab.1 hK
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have := hp.two_le
  rcases (by omega : p = 3 ∨ 5 ≤ p) with rfl | hp5
  · have h3 : ¬ 3 ∣ 2 ^ lab.n + 1 := fun h' => by
      have : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
      omega
    exact ggTorusFrame_of_involFrameElt hp hZ
      (fun _ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hlab.1 hK h3 hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 hlab.1 hK h3)
      (ggTorusInvolFrameElt_twE6Three hlab.1 hK h.2)
  · have hp3 : p ≠ 3 := by omega
    exact ggTorusFrame_of_involFrameElt hp hZ (TwE6Delta.ggOutdiagPrime_twE6 hlab.1 hK hp hp3)
      (TwE6Delta.ggCenterPrime_twE6 hlab.1 hK hp hp2 hp3)
      (ggTorusInvolFrameElt_twE6Split hlab.1 hK hp hp5 h.2 4)

theorem ggRowNE6_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NE6 p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hcov : ∀ lab, ggRowP_NE6 p lab →
      ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGNbrNsE6Label p lab := by
    rintro lab (⟨ht, hd⟩ | h)
    · by_cases h13 : lab.n = 1 ∧ p = 3
      · exact Or.inl (Or.inl ⟨ht, h13⟩)
      · refine Or.inr ⟨ht, fun h1 => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 h1 hd, h13,
          fun h17 => ?_⟩
        rw [h17.1, h17.2] at hd
        norm_num at hd
    · exact Or.inl (Or.inr h)
  have hor : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGNbrNsE6Label p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · refine ggRow_absurd_of_frame ggLabelRigidInput_holds (fun q hq hq2 lab hlab h => ?_)
      hcfg hpres hle3 hK h
    rcases h with ⟨ht, hn, rfl⟩ | h
    · exact largeEvenLabelAll_frame_E6Two ⟨ht, hn⟩
    · exact largeEvenLabelAll_frame_twE6Dvd hq hq2 hlab h
  · exact ggRow_absurd_of_clauseFive
      (fun _ _ h => Or.inr fun _ _ hX _ hc => NbrInnerMore.not_markedModel_char_ne_two_E6 h.1 hX hc)
      (fun _ _ hp _ _ h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp h.1 h.2.1)
      (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
        NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab h hX hlab' hc' hX' c)
      hcfg hK h

end CFSG.StandardType

end
