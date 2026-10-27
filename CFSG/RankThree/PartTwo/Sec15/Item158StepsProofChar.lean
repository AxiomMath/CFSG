module

public import CFSG.RankThree.PartTwo.Sec17.RouteWire15
public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
public import CFSG.RankThree.PartTwo.Sec15.Item15Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def CharNormal153 (Y S : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧
    Y ⊔ S ≤ Subgroup.normalizer (C : Set G)

@[expose] noncomputable def Step153CharPush : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S →
        (∃ H : Subgroup G, Y ⊔ S ≤ H ∧ H ≤ n155 A Y ∧
            (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal ∧
            Hyp315 H S) ∨
          ∃ M L' : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ IsScriptLBlock M L'

@[expose] noncomputable def Step153CharBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A),
      ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), ¬ CharNormal153 Y S →
        ∀ H : Subgroup G, Y ⊔ S ≤ H → H ≤ n155 A Y →
          (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal → Hyp315 H S →
          IsScriptLBlock ⊤ (oResidual 2 ↥H) →
            ∃ M L' : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ IsScriptLBlock M L'

theorem false_of_isScriptLBlock_of_sec13Data (h316 : Sec19.Item316) {A L : Subgroup G} {c : G}
    (h : Sec13Data G A c L) {M L' : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hL' : IsScriptLBlock M L') : False :=
  h.not_inCatalog (h316 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType h.evenRank_eq M L'
    hM hL')

theorem claim153CharR_of (h315 : Item3_15) (h316 : Sec19.Item316) (hpush : Step153CharPush)
    (hbl : Step153CharBlock) : Claim153CharR := by
  intro G _ _ A c L hR Y hY S hS
  by_contra hno
  have hno' : ¬ CharNormal153 Y S := hno
  rcases hpush G A c L hR Y hY S hS hno' with ⟨H, hYSH, hHN, hsub, hyp⟩ | ⟨M, L', hM, hL'⟩
  · rcases exists_char_normal_of_hyp315 h315 hyp with ⟨C, hC1, hCS, hCc, hHC⟩ | hb
    · exact hno ⟨C, hC1, hCS, hCc, hYSH.trans hHC⟩
    · obtain ⟨M, L', hM, hL'⟩ := hbl G A c L hR Y hY S hS hno' H hYSH hHN hsub hyp hb
      exact false_of_isScriptLBlock_of_sec13Data h316 hR.toSec13Data hM hL'
  · exact false_of_isScriptLBlock_of_sec13Data h316 hR.toSec13Data hM hL'

end CFSG.RankThree.PartTwo.Sec15
