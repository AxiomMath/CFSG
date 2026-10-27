module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Row
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeRow
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5O2
public import CFSG.LocalAnalysis.StandardType.GGNSJoinRMDefs
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace NSJoin


theorem nsJA2_of_torusNoncommAt {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg0 : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hNC : ∀ hN : Bs ≤ Subgroup.normalizer (L : Set G), GGTBJTorusNoncommAt p Bs L hN) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 := by
  obtain ⟨hcfg, hns, ι, M, e, hpres, hTM, hbig⟩ := hcfg0
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGInnerDiagOn.le_normalizer hcfg.1.2.2.1.1
  obtain ⟨hp, hBs_ea, -, -, -⟩ := GGConfig.tableB_facts hconf
  have hp2 : p ≠ 2 := hconf.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hconf.2.1.2.2.2
  obtain ⟨r, hr, r', hr', hrefl, hrefl', hne⟩ :=
    exists_noncomm_reflections_of_weylReflSetIn hp hp2 hBs_ea hSC hN
      (ggTBJTorusReflSetIn_noncomm_of_at hconf hN (hNC hN))
  have hJ_le_L : J ≤ L := hconf.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hle : ggAutomizer J Bs ≤ ggAutomizer L Bs := ggAutomizer_mono Bs hJ_le_L
  have hrA : r ∈ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (hle hr)
  have hrA' : r' ∈ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (hle hr')
  have hx₁ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres (hT3 hTM) hrA hrefl
  have hx₂ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres (hT3 hTM) hrA' hrefl'
  refine ⟨r, hr, r', hr', hrefl, hrefl', ?_⟩
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 (hT3 hTM) hx₁ hx₂ with h2 | h3
  · exfalso
    apply hne
    have h2' : (r * r') * (r * r') = 1 := by simpa [pow_two] using h2
    have hinv : (r * r')⁻¹ = r * r' := inv_eq_of_mul_eq_one_right h2'
    calc r * r' = (r * r')⁻¹ := hinv.symm
      _ = r'⁻¹ * r⁻¹ := mul_inv_rev r r'
      _ = r' * r := by
        rw [inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrefl'.1),
          inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrefl.1)]
  · refine orderOf_eq_prime h3 ?_
    intro h1
    apply hne
    have hrr : r' = r := by
      rw [eq_inv_of_mul_eq_one_right h1,
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrefl.1)]
    rw [hrr]

theorem nsJA2_of_rowR5O2 {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg0 : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hLF : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab) p Bs L) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 :=
  nsJA2_of_torusNoncommAt hT3 hcfg0 fun hN => ggTBJTorusNoncommAt_of_rowR5O2 hcfg0.1.1.1 hLF hN


theorem nsJA2_of_twE6Plus {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg0 : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hLF : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 :=
  nsJA2_of_torusNoncommAt hT3 hcfg0 fun hN => ggTBJTorusNoncommAt_of_twE6Plus hcfg0.1.1.1 hLF hN


theorem nsJA2_of_twE6Bad {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg0 : NSRegularCfgOf T p B Bs x L D J 𝒦)
    (hLF : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTwE6BadLabel p lab) p Bs L) :
    ∃ r ∈ ggAutomizer J Bs, ∃ r' ∈ ggAutomizer J Bs,
      GGIsReflection p r ∧ GGIsReflection p r' ∧ orderOf (r * r') = 3 :=
  nsJA2_of_torusNoncommAt hT3 hcfg0 fun hN => ggTBJTorusNoncommAt_of_twE6Bad hcfg0.1.1.1 hLF hN

end NSJoin

end CFSG.StandardType

end
