module

public import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofBlock
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofChar
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Claim153TwinR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153Twin A (lB A)

@[expose] noncomputable def Claim153TwinXR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153TwinX A (lB A)

@[expose] noncomputable def Claim153TwinNR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153TwinN A (lB A)

theorem claim153TwinR_of_twinX (h149 : Sec16.Item149S14) (h152 : Item152R)
    (htx : Claim153TwinXR) : Claim153TwinR :=
  fun G _ _ A c L hR => claim153Twin_of_twinX hR.toSec14Std (h149 G A c L hR.toSec14Std)
    (h152 G A c L hR) (htx G A c L hR)

theorem claim153TwinXR_of_twinN (h149 : Sec16.Item149S14) (h152 : Item152R)
    (htn : Claim153TwinNR) : Claim153TwinXR :=
  fun G _ _ A c L hR => claim153TwinX_of_twinN hR.toSec14Std (h149 G A c L hR.toSec14Std)
    (h152 G A c L hR) (htn G A c L hR)
    (fun _ hY _ => Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1)

theorem step153CharBlock_of_twin (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) :
    Step153CharBlock := by
  intro G _ _ A c L hR Y hY S _ _ H _ hHN hsub _ hb
  have h1 := rank3II_15_3_1_of hR.toSec14Std (h149 G A c L hR.toSec14Std) (htwin G A c L hR) hY
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hM₀N : M₀ = n155 A Y := by
    have hmem : M₀ ∈ ({n155 A Y} : Set (Subgroup G)) := h1 ▸ hM₀
    exact Set.mem_singleton_iff.mp hmem
  exact ⟨n155 A Y, _, hM₀N ▸ hM₀.1, Proof153Block.isScriptLBlock_map_subtype hb hHN hsub⟩

theorem claim153CharR_of_twin (h315 : Item3_15) (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (htwin : Claim153TwinR) (hpush : Step153CharPush) : Claim153CharR :=
  claim153CharR_of h315 h316 hpush (step153CharBlock_of_twin h149 htwin)

theorem item153MainR_of_twin (h149 : Sec16.Item149S14) (htwin : Claim153TwinR)
    (hchar : Claim153CharR) : Item153MainR :=
  fun G _ _ A c L hR => rank3II_15_3_main_of hR.toSec14Std (h149 G A c L hR.toSec14Std)
    (htwin G A c L hR) (hchar G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
