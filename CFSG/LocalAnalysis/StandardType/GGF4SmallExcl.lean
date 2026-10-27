module

public import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
public import CFSG.LocalAnalysis.StandardType.GGF4SmallA4
public import CFSG.LocalAnalysis.StandardType.GGF4SmallE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4Contracts
public import CFSG.LocalAnalysis.StandardType.GGF4SmallFFDefs
public import CFSG.LocalAnalysis.StandardType.GGF4QTwoHypA
public import CFSG.LocalAnalysis.StandardType.GGSLTwoAutBound
import CFSG.LocalAnalysis.StandardType.GGF4QTwoReduction
import CFSG.LocalAnalysis.StandardType.GGF4TypeCards
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreDeltaTransfer
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

theorem ggSecFiveF4SmallExclusionInput_of_ff81b
    (hFF : FF81bThmAAtFiveSixLab) (hE6 : GGE6TwoThreeComp) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGSecFiveF4SmallExclusionInput := by
  intro G _ _ p B Bs x L D J ks hR _hT1 ι M e hP hF hA3 _hnospan hp3 hLlab hKlab
  subst hp3
  have hRH : GGSecFiveRestHyp 3 B Bs x L D J := hR.1
  obtain ⟨⟨hsimp, hna, hKP, hchar, -, hβ, hS, -⟩, hBs, -⟩ := hRH.1
  have := hsimp
  have hW4 : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks) :=
    ggF4Small_weylOfType_F4 e hP hF
  obtain ⟨K, hK⟩ := ggF4Small_ks_nonempty hW4 hA3
  obtain ⟨y, hNb⟩ := hR.2.2.2.1.2 K hK
  obtain ⟨hBmax, hyB, hy1, hKy, hPC, -⟩ := hNb.1
  have hy3 : y ^ 3 = 1 := hS.1.1.2 y hyB
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hox : orderOf x = 3 := orderOf_eq_prime (hS.1.1.2 x hxB) hx1
  have hLcomp : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.2.2.2.1
  have hcardBs : Nat.card Bs = 3 ^ 4 := ggF4Small_card_Bs hTBF hWI hR hW4 ⟨K, hK⟩
  have hm4 : twoLocalPrimeRank 3 G ≤ 4 := by
    have hB : Nat.card B = 3 ^ twoLocalPrimeRank 3 G := hS.1.2.1
    have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    rw [hB, hcardBs] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hmarkK := ggF4Small_markingK hRH hNb (hKlab K hK)
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_f4EndMarking
      (P := fun lab => lab.tag = .A ∧ lab.rank = 5 ∧ lab.n = 1)
      (fun lab hl => ⟨Or.inl ⟨hl.1, hl.2.1⟩, hl.2.2⟩) hmarkK
  obtain ⟨U, E, hUK, hEK, hU, hU2, hEU, hE, hEcard⟩ :=
    exists_torus_of_markingA (n := 5) le_rfl hmarkK
  have hcycK : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S →
      IsCyclic S := fun S hS hS3 =>
    isCyclic_of_le_centralizer_of_torus hZ hUK hEK hU hU2 hEU hE hEcard
      (by omega) hS hS3
  have hcomp : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKy, hPC.2.1, isQuasisimple_of_largeEvenMarking hmarkK⟩
  have hN := le_normalizer_of_isComponentOf_cyclic hcomp (fun S _ hSK hS3 => hcycK S hSK hS3)
    ⟨E, hEK, (haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩; IsPGroup.of_card hEcard),
      not_isCyclic_of_isElemAbelian_three_pow hE hEcard (by norm_num)⟩
  have hM := statedClassicalModel_of_markingA hmarkK hZ
  have hA2 : ∀ P : Sylow 3 ↥(Subgroup.centralizer (K : Set G)), IsCyclic P := fun P =>
    isCyclic_sylow_of_le_centralizer_of_forall hcycK le_rfl P
  have hyK : y ∉ K := by
    intro hyK'
    have : (⟨y, hyK'⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKy k.2) y (Set.mem_singleton y)).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact hy1 (congrArg Subtype.val this)
  have hA3' : twoLocalPrimeRank 3 G =
      twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) := by
    have h1 := le_twoLocalPrimeRank_centralizer_of_torus hy3 hy1 hKy hyK hUK hEK
      hU hU2 hEU hE hEcard
    have h2 : twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ twoLocalPrimeRank 3 G :=
      CFSG.LargeEvenClassification.Helpers.twoLocalPRank_subgroup_le
        (by norm_num : 1 < 3) (Subgroup.centralizer ({y} : Set G))
    have h4 : 4 ≤ twoLocalPrimeRank 3 G := hβ.2.2.2
    omega
  have hA4 := ffNotWeaklyClosed_of_conj (ggF4Small_a4 hTBF hWI hR hW4 ⟨K, hK⟩ hyB hy1)
  rcases hFF G hna hchar hKP 5 (Or.inl rfl) y hoy K hKy hN hM hA2 hA3' hA4 with hPSL | ⟨-, hE6lab⟩
  ·
    exfalso
    have hle := card_automizer_le_384_of_slTwo hPSL hBs.2.1 hcardBs hBs.2.2.2
      (A := ggAutomizerJoin L Bs ks) (ggF4Small_join_induced L ks)
    have h1152 := ggF4Orig_card_weylOfType_F4 hW4
    omega
  ·
    exact ggF4Small_e6_false hE6 hna hE6lab hox hLcomp hLlab

theorem ggSecFiveF4SmallData_of_ff81b
    (hFF : FF81bThmAAtFiveSixLab) (hE6 : GGE6TwoThreeComp) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGSecFiveF4SmallDataInput :=
  ggSecFiveF4SmallData_of_exclusion (ggSecFiveF4SmallExclusionInput_of_ff81b hFF hE6 hTBF hWI)

end CFSG.StandardType

end
