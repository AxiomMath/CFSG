module

public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
public import CFSG.LocalAnalysis.StandardType.TitsGeneratorsBase
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.LocalDataSimpleOfCheck
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupWordsSound
public import CFSG.LocalAnalysis.StandardType.SimpleOrder5616Overgroup
public import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerivedSylow
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTits
public import Certificates.Certificate465005
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.TitsThree

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowPair
open CFSG.StandardType.SylowOvergroup CFSG.StandardType.TitsGenerators
open CFSG.AGLEmbedding.MaxD2 (Gsub Rsub)
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDArr)

theorem titsThreeCheck_parts (h : titsThreeCheck () = true) :
    pairCheck pairData = true ∧ checkMemW pairData memWords = true ∧
      ∀ k < 2, Certificates.MaxD2Perm.check (lLocalData k ()) = true := by
  simp only [titsThreeCheck, Bool.and_eq_true, allBelow_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem conjugatorWords_ne_zero :
    ∀ k < 2, ∀ i < 2, ∀ z ∈ (conjugatorWords.getD k []).getD i [], z ≠ 0 := by
  decide

theorem conjugatorWords_length {k : ℕ} (hk : k < 2) : (conjugatorWords.getD k []).length = 2 := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem repKinds_cases : ∀ k ∈ repKinds, k = 0 ∨ k = 3 ∨ k = 4 := by
  decide +kernel

theorem sideW_getD_L {k : ℕ} (hk : k < 2) : pairData.sideW.getD k [] = lWords k := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem sideW_getD_M {k : ℕ} (hk : k < 2) : pairData.sideW.getD (k + 2) [] = mWords k := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem memWords_getD {k : ℕ} (hk : k < 2) :
    memWords.getD k [] = pWords ++ conjugatorWords.getD k [] := by
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem sideOrder_getD {k : ℕ} (hk : k < 2) :
    pairData.sideOrder.getD k 0 = 5616 ∧ pairData.sideOrder.getD (k + 2) 0 = 11232 := by
  rcases k with _ | _ | k
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · omega

theorem kind_eq_cases (hGen : checkGen pairData = true) {i : ℕ} (hi : i < pairData.repW.length) :
    pairData.kind[i]! = 0 ∨ pairData.kind[i]! = 3 ∨ pairData.kind[i]! = 4 := by
  have hlen : pairData.kind.length = pairData.repW.length := by
    simp only [checkGen, Bool.and_eq_true, beq_iff_eq] at hGen
    exact hGen.1.1
  have hi' : i < pairData.kind.length := by rw [hlen]; exact hi
  have hmem : pairData.kind[i]! ∈ pairData.kind := by
    rw [getElem!_pos pairData.kind i hi']
    exact List.getElem_mem hi'
  exact repKinds_cases _ hmem

theorem wordVal_one {G : Type*} [Group G] (S : List G) : wordVal S [1] = S.getD 0 1 := by
  simp [wordVal]

theorem wordVal_two {G : Type*} [Group G] (S : List G) : wordVal S [2] = S.getD 1 1 := by
  simp [wordVal]

@[expose] noncomputable def sideGensVals (k : ℕ) : List (Equiv.Perm (Fin 1755)) :=
  (pairData.sideW.getD k []).map (wordVal titsS)

section Core


theorem pairData_rep :
    ∀ j, TabRep (pairData.gT.getD j (idTab pairData.n)) (titsS.getD j 1) := by
  intro j
  rcases j with _ | _ | j
  · simpa [pairData, titsS] using tab_titsDGen (j := 0) (by norm_num)
  · simpa [pairData, titsS] using tab_titsDGen (j := 1) (by norm_num)
  · simpa [pairData, titsS] using TabRep.idTab (n := 1755)

theorem sound_pairData (hinv : checkInv pairData = true) : Sound pairData titsS := by
  have hlen : titsS.length = pairData.gT.size := by simp [titsS, pairData]
  have hG : pairG pairData titsS = titsD := (titsD_eq_closure_titsS).symm
  refine ⟨pairData_rep, hlen, hinv, ?_⟩
  have h2 : Nat.card ↥(pairG pairData titsS) =
      Nat.card ↥(titsD : Subgroup (Equiv.Perm (Fin 1755))) :=
    congrArg (fun H : Subgroup (Equiv.Perm (Fin 1755)) => Nat.card ↥H) hG
  exact h2.trans CFSG.Sporadic.Schreier.Tits.card_titsD

theorem pairN_le_pairSide {k : ℕ} (hk : k < 2) :
    pairN pairData titsS ≤ pairSide pairData titsS (k + 2) := by
  unfold pairN pairSide
  apply Subgroup.closure_mono
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  refine List.mem_map.2 ⟨w, ?_, rfl⟩
  rw [sideW_getD_M hk]
  exact List.mem_append.2 (Or.inr hw)

theorem pairSide_le_pairSide {k : ℕ} (hk : k < 2) :
    pairSide pairData titsS k ≤ pairSide pairData titsS (k + 2) := by
  unfold pairSide
  apply Subgroup.closure_mono
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  refine List.mem_map.2 ⟨w, ?_, rfl⟩
  rw [sideW_getD_L hk] at hw
  rw [sideW_getD_M hk]
  exact List.mem_append.2 (Or.inl hw)

theorem mem_pairSide (hpair : pairCheck pairData = true)
    (hmem : checkMemW pairData memWords = true) {k : ℕ} (hk : k < 2) {w : List Int}
    (hw : w ∈ pWords ++ conjugatorWords.getD k []) :
    wordVal titsS w ∈ pairSide pairData titsS k := by
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMemS⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  exact memW_sound hS hSide hmem (k := k) (by simpa [memWords] using hk)
    (by rw [memWords_getD hk]; exact hw)

theorem pairP_le_pairSide (hpair : pairCheck pairData = true)
    (hmem : checkMemW pairData memWords = true) {k : ℕ} (hk : k < 2) :
    pairP pairData titsS ≤ pairSide pairData titsS k := by
  unfold pairP
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  exact mem_pairSide hpair hmem hk (List.mem_append.2 (Or.inl hw))

theorem isSimpleGroup_pairSide (hc : titsThreeCheck () = true) {k : ℕ} (hk : k < 2) :
    IsSimpleGroup ↥(pairSide pairData titsS k) ∧
      commutator ↥(pairSide pairData titsS k) = ⊤ := by
  obtain ⟨hpair, hmem, hloc⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMemS⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hX0 : ∀ z ∈ (conjugatorWords.getD k []).getD 0 [], z ≠ 0 :=
    conjugatorWords_ne_zero k hk 0 (by norm_num)
  have hY0 : ∀ z ∈ (conjugatorWords.getD k []).getD 1 [], z ≠ 0 :=
    conjugatorWords_ne_zero k hk 1 (by norm_num)
  obtain ⟨rU, hrU⟩ : ∃ r : Equiv.Perm (Fin 1755),
      r = wordVal titsS ((rGenWords.getD k []).getD 0 []) := ⟨_, rfl⟩
  obtain ⟨rV, hrV⟩ : ∃ r : Equiv.Perm (Fin 1755),
      r = wordVal titsS ((rGenWords.getD k []).getD 1 []) := ⟨_, rfl⟩
  obtain ⟨xe, hxe⟩ : ∃ r : Equiv.Perm (Fin 1755),
      r = wordVal titsS ((conjugatorWords.getD k []).getD 0 []) := ⟨_, rfl⟩
  obtain ⟨ye, hye⟩ : ∃ r : Equiv.Perm (Fin 1755),
      r = wordVal titsS ((conjugatorWords.getD k []).getD 1 []) := ⟨_, rfl⟩
  have hSeq : sideGensVals k =
      [rU, rV, xe * rU * xe⁻¹, xe * rV * xe⁻¹, ye * rU * ye⁻¹, ye * rV * ye⁻¹] := by
    unfold sideGensVals
    rw [sideW_getD_L hk]
    simp only [lWords, List.map_cons, List.map_nil, wordVal_conjWord titsS hX0,
      wordVal_conjWord titsS hY0, hrU, hrV, hxe, hye]
  have hgs : ∀ j, TabRep ((lLocalData k ()).gT.getD j (idTab (lLocalData k ()).n))
      ((sideGensVals k).getD j 1) := sideGens_rep hS k
  have hlen : (sideGensVals k).length = (lLocalData k ()).gT.size := by
    simp [sideGensVals, lLocalData, sideGens]
  have hcard : Nat.card (Gsub (D := lLocalData k ()) (sideGensVals k)) =
      (lLocalData k ()).gOrder :=
    (card_pairSide hS hSide (k := k) (by simp [pairData]; omega)).trans (sideOrder_getD hk).1
  have hRU : rU ∈ Rsub (lLocalData k ()) (sideGensVals k) := by
    apply Subgroup.subset_closure
    show rU ∈ [wordVal (sideGensVals k) [1], wordVal (sideGensVals k) [2]]
    simp [wordVal_one, wordVal_two, hSeq]
  have hRV : rV ∈ Rsub (lLocalData k ()) (sideGensVals k) := by
    apply Subgroup.subset_closure
    show rV ∈ [wordVal (sideGensVals k) [1], wordVal (sideGensVals k) [2]]
    simp [wordVal_one, wordVal_two, hSeq]
  have hxeG : xe ∈ Gsub (D := lLocalData k ()) (sideGensVals k) := by
    show xe ∈ pairSide pairData titsS k
    rw [hxe]
    exact mem_pairSide hpair hmem hk (List.mem_append.2 (Or.inr
      (CFSG.AGLEmbedding.MaxD2.getD_mem_of_lt (i := 0) (L := conjugatorWords.getD k [])
        (by rw [conjugatorWords_length hk]; norm_num) [])))
  have hyeG : ye ∈ Gsub (D := lLocalData k ()) (sideGensVals k) := by
    show ye ∈ pairSide pairData titsS k
    rw [hye]
    exact mem_pairSide hpair hmem hk (List.mem_append.2 (Or.inr
      (CFSG.AGLEmbedding.MaxD2.getD_mem_of_lt (i := 1) (L := conjugatorWords.getD k [])
        (by rw [conjugatorWords_length hk]; norm_num) [])))
  have hconj : ∀ s ∈ sideGensVals k, ∃ g ∈ Gsub (D := lLocalData k ()) (sideGensVals k),
      ∃ r ∈ Rsub (lLocalData k ()) (sideGensVals k), s = g * r * g⁻¹ := by
    intro s hs
    rw [hSeq] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · have e : s = (1 : Equiv.Perm (Fin 1755)) * s * (1 : Equiv.Perm (Fin 1755))⁻¹ := by simp
      exact ⟨1, one_mem _, s, hRU, e⟩
    · have e : s = (1 : Equiv.Perm (Fin 1755)) * s * (1 : Equiv.Perm (Fin 1755))⁻¹ := by simp
      exact ⟨1, one_mem _, s, hRV, e⟩
    · exact ⟨xe, hxeG, rU, hRU, rfl⟩
    · exact ⟨xe, hxeG, rV, hRV, rfl⟩
    · exact ⟨ye, hyeG, rU, hRU, rfl⟩
    · exact ⟨ye, hyeG, rV, hRV, rfl⟩
  exact LocalDataSimpleOfCheck.isSimpleGroup_of_check_conj (D := lLocalData k ())
    (S := sideGensVals k) (by norm_num [lLocalData]) (by norm_num [lLocalData]) rfl hgs hlen hcard
    ⟨4, 1, by norm_num [lLocalData]⟩ (hloc k hk) hconj

theorem solvableOrSimpleDerived_of_pairP_le (hc : titsThreeCheck () = true)
    {Y : Subgroup (Equiv.Perm (Fin pairData.n))} (hPY : pairP pairData titsS ≤ Y)
    (hYG : Y ≤ titsD) (hY : Y ≠ titsD) : SolvableOrSimpleDerived 5616 ↥Y := by
  obtain ⟨hpair, hmem, hloc⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMemS⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := (titsD_eq_closure_titsS).symm
  have hcov : (Y : Set (Equiv.Perm (Fin pairData.n))) ⊆
      (pairSide pairData titsS 2 : Set (Equiv.Perm (Fin pairData.n))) ∪
        (pairSide pairData titsS 3 : Set (Equiv.Perm (Fin pairData.n))) := by
    intro y hy
    rcases dichotomy hS hpair hPY (hYG.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hy
      with h | ⟨i, hi, hk, ⟨a, ha, b, hb, hyi⟩, -⟩
    · exact Or.inl (pairN_le_pairSide (k := 0) (by norm_num) h)
    · rcases kind_eq_cases hGen hi with h0 | h3 | h4
      · exact absurd h0 hk
      · have hg : (pairReps pairData titsS).getD (i + 1) 1 ∈ pairSide pairData titsS 2 :=
          pairReps_mem_side hS hSide hMemS hi (k := 2) h3
        refine Or.inl ?_
        rw [hyi]
        exact (pairSide pairData titsS 2).mul_mem ((pairSide pairData titsS 2).mul_mem
          (pairN_le_pairSide (k := 0) (by norm_num) ha) hg)
          (pairN_le_pairSide (k := 0) (by norm_num) hb)
      · have hg : (pairReps pairData titsS).getD (i + 1) 1 ∈ pairSide pairData titsS 3 :=
          pairReps_mem_side hS hSide hMemS hi (k := 3) h4
        refine Or.inr ?_
        rw [hyi]
        exact (pairSide pairData titsS 3).mul_mem ((pairSide pairData titsS 3).mul_mem
          (pairN_le_pairSide (k := 1) (by norm_num) ha) hg)
          (pairN_le_pairSide (k := 1) (by norm_num) hb)
  have hP27 : Nat.card ↥(pairP pairData titsS) = 27 := card_pairP hS hP
  have key : ∀ k < 2, Y ≤ pairSide pairData titsS (k + 2) → SolvableOrSimpleDerived 5616 ↥Y := by
    intro k hk hYM
    obtain ⟨hsimple, -⟩ := isSimpleGroup_pairSide hc hk
    have hcardL : Nat.card ↥(pairSide pairData titsS k) = 5616 :=
      (card_pairSide hS hSide (k := k) (by simp [pairData]; omega)).trans (sideOrder_getD hk).1
    have hcardM : Nat.card ↥(pairSide pairData titsS (k + 2)) = 11232 :=
      (card_pairSide hS hSide (k := k + 2) (by simp [pairData]; omega)).trans (sideOrder_getD hk).2
    exact SimpleOrderFiveSixOneSix.solvableOrSimpleDerived_of_le_index_two
      (Q := Equiv.Perm (Fin pairData.n)) (M := pairSide pairData titsS (k + 2))
      (L := pairSide pairData titsS k) (Y := Y) (P := pairP pairData titsS)
      (pairSide_le_pairSide hk) (by rw [hcardM, hcardL]) hsimple hcardL hYM hPY
      (pairP_le_pairSide hpair hmem hk) hP27
  rcases le_or_le_of_subset_union hcov with h | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h

end Core

end CFSG.StandardType.TitsThree

namespace CFSG.StandardType

open CFSG.StandardType.TitsThree CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowOvergroup
open CFSG.StandardType.TitsGenerators
open CFSG.Sporadic.Schreier.Tits (titsD)

theorem ggSeitzExcTitsThreeInput_holds :
    GGSeitzExcTitsThreeInput := by
  intro K _ _ d hd he X hX1 h3
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = .tits := hd
  subst hd'
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, he⟩)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : titsThreeCheck () = true := Certificates.certificate465005
  obtain ⟨hpair, -, -⟩ := titsThreeCheck_parts hc
  obtain ⟨hInv, hP, -, -, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hPG : pairP pairData titsS ≤ titsD := hG ▸ pairP_le_pairG
  have hP27 : Nat.card ↥(pairP pairData titsS) = 3 ^ 3 := by
    rw [card_pairP hS hP]
    rfl
  have hD : Nat.card ↥titsD = 3 ^ 3 * 665600 := by
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  have hsol := solvableOrSimpleDerived_of_sylow_le (Q := Equiv.Perm (Fin pairData.n)) (G := titsD)
    (P := pairP pairData titsS) (p := 3) (m := 5616) hPG hP27 hD (by norm_num)
    (fun Y hPY hYG hY => solvableOrSimpleDerived_of_pairP_le hc hPY hYG hY)
  exact forall_of_mulEquiv e (fun A _ => SolvableOrSimpleDerived 5616 A)
    (fun A B _ _ f h => SolvableOrSimpleDerived.of_mulEquiv f h) hsol X hX1 h3

end CFSG.StandardType
