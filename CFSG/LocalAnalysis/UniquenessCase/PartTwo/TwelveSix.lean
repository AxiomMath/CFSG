module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace TwelveSix

theorem lGen_le_inf (D : Data G) {H₀ : Subgroup G} (hmin : Hyp124Min D H₀)
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ X : Subgroup G, ¬ F12.HasCompFactor X P →
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M X) :
    lGen P H₀ D.T ≤ H₀ ⊓ D.M := by
  refine iSup₂_le fun X hX => le_inf hX.2.1.le ?_
  by_contra hXM
  obtain ⟨hTX, hXH, hXP⟩ := hX
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hO : pCoreOf 2 H₀ ≤ D.T := E1.pCoreOf_two_le_of_isSylowIn hT
  have hXc : X ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M := by
    refine ⟨hTX, hXM, ?_⟩
    have hO2HX : pCoreOf 2 H₀ ≤ X := hO.trans hTX
    have hO2Hnorm : X ≤ normalizer (pCoreOf 2 H₀ : Set G) :=
      hXH.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H₀)
    have hO2Hle : pCoreOf 2 H₀ ≤ pCoreOf 2 X :=
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO2HX hO2Hnorm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀)
    intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : x ∈ centralizer (pCoreOf 2 H₀ : Set G) :=
      Subgroup.centralizer_le hO2Hle hxC
    exact hO2Hle (hmin.1.2.2 (Subgroup.mem_inf.mpr ⟨hXH.le hxX, hxC'⟩))
  exact hXH.ne (hmin.2.2 X hXc (hP X hXP) hXH.le)

theorem calNIn_eq_inf (D : Data G) {H₀ L : Subgroup G} (hH₀ : ¬ H₀ ≤ D.M) (hT : D.T ≤ H₀)
    (hcalN : calNIn H₀ D.T = {L}) (hL : L ≤ H₀ ⊓ D.M) : calNIn H₀ D.T = {H₀ ⊓ D.M} := by
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hlt : H₀ ⊓ D.M < H₀ := lt_of_le_of_ne inf_le_left fun h => hH₀ (inf_eq_left.1 h)
  obtain ⟨X, hX, hle⟩ := exists_mem_calNIn_of_lt (le_inf hT hTM) hlt
  rw [hcalN, Set.mem_singleton_iff] at hX
  subst hX
  rw [hcalN, le_antisymm hL hle]

end TwelveSix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
