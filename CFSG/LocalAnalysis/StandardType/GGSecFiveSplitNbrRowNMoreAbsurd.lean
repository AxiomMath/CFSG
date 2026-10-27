module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNBCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwAMCells
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRowNB_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NB p Bs K) : False :=
  ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun _ hp _ _ hlab h => h.2.2.elim
      (fun hd => largeEvenLabelAll_frame_symplectic hp hlab ⟨h.1, hd⟩)
      (fun hd => largeEvenLabelAll_frame_symplecticNs hp hlab ⟨h.1, hd⟩))
    hcfg hpres hle3 hK hrow

theorem ggRowNTwAM_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K)
    (hrow : GGInnerDiagOnLabel ggRowP_NTwAM p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hcov : ∀ lab, ggRowP_NTwAM p lab →
      ((lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) ∨
        (((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
          p ∣ 2 ^ lab.n - 1)) ∨ GGNbrNsUnitLabel p lab := by
    rintro lab ⟨⟨ht, hl⟩ | ⟨ht, hl⟩, hd⟩
    · rcases (by omega : lab.rank = 3 ∨ lab.rank = 4 ∨ lab.rank = 5 ∨ 6 ≤ lab.rank) with
        h | h | h | h
      · exact Or.inl (Or.inr ⟨Or.inl ⟨ht, Or.inl h⟩, hd⟩)
      · exact Or.inl (Or.inr ⟨Or.inl ⟨ht, Or.inr h⟩, hd⟩)
      · exact Or.inl (Or.inl ⟨ht, h, hd⟩)
      · exact Or.inr ⟨ht, by omega, not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hd,
          fun h5 => by omega⟩
    · exact Or.inl (Or.inr ⟨Or.inr ⟨ht, hl⟩, hd⟩)
  have hor : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) ∨
        (((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
          p ∣ 2 ^ lab.n - 1)) ∨ GGNbrNsUnitLabel p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact ggRow_absurd_of_cells ggLabelRigidInput_holds
      (Sf := fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) (fun _ _ h => h)
      (fun p hp hp2 lab hlab h => ggNbrFrameInputOne_holds p hp hp2 lab hlab (Or.inr (Or.inr h)))
      ggRowPRankLeTwo_smallMinus hcfg hpres hle3 hK h
  · exact ggRow_absurd_of_clauseFive
      (fun _ _ h => Or.inr fun _ _ hX _ hc =>
        NbrInnerMore.not_markedModel_char_ne_two_unit h.1 h.2.1 hX hc)
      (fun _ _ hp _ hlab h =>
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab h.1 h.2.2.1).mono
          fun _ _ _ _ h _ _ => h)
      (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
        NbrInnerMore.not_halfSplit_of_markedModel_unit h hX hc' hX' c)
      hcfg hK h

end CFSG.StandardType

end
