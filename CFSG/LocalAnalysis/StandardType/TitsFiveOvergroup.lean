module

public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
public import CFSG.LocalAnalysis.StandardType.TitsGeneratorsBase
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.LocalDataSimple
public import CFSG.LocalAnalysis.StandardType.LocalDataOfCheck
public import CFSG.LocalAnalysis.StandardType.LocalDataSimpleOfCheck
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupWordsSound
public import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerived
public import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerivedSylow
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTits
public import CFSG.Sporadic.Schreier.TitsCert
public import Certificates.Certificate465004
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

namespace CFSG.StandardType.TitsFive

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowPair
open CFSG.StandardType.SylowOvergroup CFSG.StandardType.TitsGenerators
open CFSG.AGLEmbedding.MaxD2 (Gsub Rsub)
open CFSG.Sporadic.Schreier.Tits (titsD titsDGen titsDArr)

theorem eq_map_conj_of_maximal {Q : Type*} [Group Q] {G L Y : Subgroup Q} {a : Q} (ha : a ∈ G)
    (hL : ∀ M : Subgroup Q, L ≤ M → M ≤ G → M = L ∨ M = G)
    (hLY : L.map (MulAut.conj a).toMonoidHom ≤ Y) (hYG : Y ≤ G) (hY : Y ≠ G) :
    Y = L.map (MulAut.conj a).toMonoidHom := by
  have hsurj : Function.Surjective (MulAut.conj a).toMonoidHom := (MulAut.conj a).surjective
  have hLM : L ≤ Y.comap (MulAut.conj a).toMonoidHom := fun x hx => hLY ⟨x, hx, rfl⟩
  have hMG : Y.comap (MulAut.conj a).toMonoidHom ≤ G := by
    intro x hx
    have h1 : a * x * a⁻¹ ∈ G := hYG (by simpa [Subgroup.mem_comap, MulAut.conj_apply] using hx)
    have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [this]
    exact G.mul_mem (G.mul_mem (G.inv_mem ha) h1) ha
  rcases hL _ hLM hMG with h | h
  · rw [← Subgroup.map_comap_eq_self_of_surjective hsurj Y, h]
  · exfalso
    apply hY
    refine le_antisymm hYG fun g hg => ?_
    have h1 : a⁻¹ * g * a ∈ Y.comap (MulAut.conj a).toMonoidHom := by
      rw [h]
      exact G.mul_mem (G.mul_mem (G.inv_mem ha) hg) ha
    have h2 := (Subgroup.mem_comap.1 h1)
    simpa [MulAut.conj_apply, mul_assoc] using h2

theorem pairData_rep :
    ∀ j, TabRep (pairData.gT.getD j (idTab pairData.n)) (titsS.getD j 1) := by
  intro j
  rcases j with _ | _ | j
  · simpa [pairData, titsS] using tab_titsDGen (j := 0) (by norm_num)
  · simpa [pairData, titsS] using tab_titsDGen (j := 1) (by norm_num)
  · simpa [pairData, titsS] using TabRep.idTab (n := 1755)

theorem sound_pairData (hinv : checkInv pairData = true) :
    Sound pairData titsS := by
  have hlen : titsS.length = pairData.gT.size := by simp [titsS, pairData]
  have hG : pairG pairData titsS = titsD := (titsD_eq_closure_titsS).symm
  refine ⟨pairData_rep, hlen, hinv, ?_⟩
  have h2 : Nat.card ↥(pairG pairData titsS) =
      Nat.card ↥(titsD : Subgroup (Equiv.Perm (Fin 1755))) :=
    congrArg (fun H : Subgroup (Equiv.Perm (Fin 1755)) => Nat.card ↥H) hG
  exact h2.trans CFSG.Sporadic.Schreier.Tits.card_titsD

theorem titsFiveCheck_parts (h : titsFiveCheck () = true) :
    pairCheck pairData = true ∧ checkSideGen pairData sideGenWords = true ∧ lMaxCheck = true ∧
      Certificates.MaxD2Perm.check (lLocalData ()) = true := by
  simp only [titsFiveCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem lWords_eq : lWords = rWords ++ rWords.map (conjWord lRepWord) := by
  decide

theorem lRepWord_ne_zero : ∀ z ∈ lRepWord, z ≠ 0 := by
  decide

theorem repWords_getLast : repWords.getD 23 [] = lRepWord := by
  decide

@[expose] noncomputable def lGens : List (Equiv.Perm (Fin 1755)) := lWords.map (wordVal titsS)

theorem Gsub_lGens : Gsub (D := lLocalData ()) lGens = pairSide pairData titsS 0 := rfl

section Core


theorem pairP_le_pairN : pairP pairData titsS ≤ pairN pairData titsS := by
  unfold pairP pairN
  rw [Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
  refine List.mem_map.2 ⟨w, ?_, rfl⟩
  simp only [pairData, rWords, nWords, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with rfl | rfl <;> simp

theorem isSolvable_pairN (hpair : pairCheck pairData = true) :
    Group.IsSolvable ↥(pairN pairData titsS) := by
  obtain ⟨hInv, hP, hN, hNorm, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  refine CFSG.AGLEmbedding.MaxD2.isSolvable_of_normal_sq (p := 5) (a := 4) (b := 1)
    Nat.prime_five pairP_le_pairN (pairN_le_normalizer hS hP hNorm) ?_ ?_
  · rw [card_pairP hS hP]
    rfl
  · rw [card_pairN hS hN]
    norm_num [pairData]

@[expose] noncomputable def rU : Equiv.Perm (Fin 1755) := wordVal titsS (rWords.getD 0 [])

@[expose] noncomputable def rV : Equiv.Perm (Fin 1755) := wordVal titsS (rWords.getD 1 [])

@[expose] noncomputable def lRep : Equiv.Perm (Fin 1755) := wordVal titsS lRepWord

theorem lGens_eq : lGens = [rU, rV, lRep * rU * lRep⁻¹, lRep * rV * lRep⁻¹] := by
  unfold lGens
  rw [lWords_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, rWords, wordVal_conjWord titsS
    lRepWord_ne_zero]
  rfl

theorem lRep_mem (hpair : pairCheck pairData = true) :
    lRep ∈ pairSide pairData titsS 0 := by
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMem⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have h := pairReps_mem_side hS hSide hMem (i := 23) (k := 0)
    (by show 23 < repWords.length; decide) (by show pairData.kind[23]! = 0 + 1; decide)
  have e : (pairReps pairData titsS).getD (23 + 1) 1 = lRep := by
    show (1 :: repWords.map (wordVal titsS)).getD (23 + 1) 1 = lRep
    rw [List.getD_cons_succ, show (1 : Equiv.Perm (Fin 1755)) = wordVal titsS [] from rfl,
      List.getD_map, repWords_getLast]
    rfl
  rwa [e] at h

theorem isSimpleGroup_pairSide (hc : titsFiveCheck () = true) :
    IsSimpleGroup ↥(pairSide pairData titsS 0) ∧ commutator ↥(pairSide pairData titsS 0) = ⊤ := by
  obtain ⟨hpair, hsg, hl, hloc⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMem⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hgs : ∀ j, TabRep ((lLocalData ()).gT.getD j (idTab (lLocalData ()).n)) (lGens.getD j 1) :=
    CFSG.AGLEmbedding.MaxD2.rep_map_words titsS baseTabs baseInv pairData_rep hS.gi lWords
  have hlen : lGens.length = (lLocalData ()).gT.size := by simp [lGens, lLocalData, lTabs]
  have h7800 : Nat.card ↥(pairSide pairData titsS 0) = pairData.sideOrder.getD 0 0 :=
    card_pairSide hS hSide (k := 0) (by simp [pairData])
  have hcard : Nat.card (Gsub (D := lLocalData ()) lGens) = (lLocalData ()).gOrder := h7800
  have hRU : rU ∈ Rsub (lLocalData ()) lGens := by
    apply Subgroup.subset_closure
    simp only [Certificates.MaxD2Perm.rWs, lLocalData, wordVal, lGens_eq, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    exact List.mem_cons.2 (Or.inl (mul_one rU).symm)
  have hRV : rV ∈ Rsub (lLocalData ()) lGens := by
    apply Subgroup.subset_closure
    simp only [Certificates.MaxD2Perm.rWs, lLocalData, wordVal, lGens_eq, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl (mul_one rV).symm)))
  have hl' : lRep ∈ Gsub (D := lLocalData ()) lGens := lRep_mem hpair
  have hconj : ∀ s ∈ lGens, ∃ g ∈ Gsub (D := lLocalData ()) lGens,
      ∃ r ∈ Rsub (lLocalData ()) lGens, s = g * r * g⁻¹ := by
    intro s hs
    rw [lGens_eq] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, rU, hRU, (by simp : (rU : Equiv.Perm (Fin 1755)) = 1 * rU * 1⁻¹)⟩
    · exact ⟨1, one_mem _, rV, hRV, (by simp : (rV : Equiv.Perm (Fin 1755)) = 1 * rV * 1⁻¹)⟩
    · exact ⟨lRep, hl', _, hRU, rfl⟩
    · exact ⟨lRep, hl', _, hRV, rfl⟩
  exact LocalDataSimpleOfCheck.isSimpleGroup_of_check_conj (D := lLocalData ()) (S := lGens)
    (by norm_num [lLocalData]) (by norm_num [lLocalData]) rfl hgs hlen hcard
    ⟨2, 1, by norm_num [lLocalData]⟩ hloc hconj

theorem pairSide_maximal (hc : titsFiveCheck () = true) :
    ∀ M : Subgroup (Equiv.Perm (Fin 1755)), pairSide pairData titsS 0 ≤ M → M ≤ titsD →
      M = pairSide pairData titsS 0 ∨ M = titsD := by
  obtain ⟨hpair, hsg, hl, hloc⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMem⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  simp only [lMaxCheck, Bool.and_eq_true] at hl
  obtain ⟨⟨⟨hlInv, hlN⟩, hlinv⟩, hlMax⟩ := hl
  have hlen : titsS.length = lMaxData.gT.size := by simp [titsS, lMaxData]
  have hcardD : Nat.card (Gsub (D := lMaxData) titsS) = lMaxData.gOrder := by
    have h2 : Nat.card ↥(Gsub (D := lMaxData) titsS) =
        Nat.card ↥(titsD : Subgroup (Equiv.Perm (Fin 1755))) :=
      congrArg (fun H : Subgroup (Equiv.Perm (Fin 1755)) => Nat.card ↥H)
        titsD_eq_closure_titsS.symm
    exact h2.trans CFSG.Sporadic.Schreier.Tits.card_titsD
  have hmax := CFSG.AGLEmbedding.MaxD2.maximal_N (D := lMaxData) (S := titsS) pairData_rep hS.gi
    hlen hcardD hlN hlinv hlMax
  intro M hLM hMD
  have h := hmax M hLM (hMD.trans (le_of_eq titsD_eq_closure_titsS))
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans titsD_eq_closure_titsS.symm)

theorem solvableOrSimpleDerived_of_pairP_le (hc : titsFiveCheck () = true)
    {Y : Subgroup (Equiv.Perm (Fin pairData.n))} (hPY : pairP pairData titsS ≤ Y) (hYG : Y ≤ titsD)
    (hY : Y ≠ titsD) : SolvableOrSimpleDerived 7800 ↥Y := by
  obtain ⟨hpair, hsg, hl, hloc⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMem⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  by_cases hYN : Y ≤ pairN pairData titsS
  · refine SolvableOrSimpleDerived.of_isSolvable ?_
    haveI := isSolvable_pairN hpair
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYN)
      (Subgroup.inclusion_injective hYN)
  · obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hYN
    rcases dichotomy hS hpair hPY (hYG.trans (le_of_eq hG.symm)) (fun h => hY (h.trans hG)) hyY
      with h | ⟨i, hi, hk, -, a, ha, hle⟩
    · exact absurd h hyN
    · have key : ∀ i < 24, pairData.kind[i]! ≠ 0 → i = 23 := by decide
      have hlen24 : pairData.repW.length = 24 := rfl
      have hi23 : i = 23 := key i (by omega) hk
      subst hi23
      have hL : pairSide pairData titsS 0 ≤
          pairClosure (pairP pairData titsS) ((pairReps pairData titsS).getD (23 + 1) 1) :=
        pairSide_le_pairClosure hS (invsOK_of_checkCover hCover) hsg (i := 23) (k := 0) hi
          (by show pairData.kind[23]! = 0 + 1; decide)
      have hLY : (pairSide pairData titsS 0).map (MulAut.conj a).toMonoidHom ≤ Y :=
        (Subgroup.map_mono hL).trans hle
      have haG : a ∈ titsD := (le_of_eq hG) (pairN_le_pairG ha)
      have hYeq : Y = (pairSide pairData titsS 0).map (MulAut.conj a).toMonoidHom :=
        eq_map_conj_of_maximal haG (pairSide_maximal hc) hLY hYG hY
      obtain ⟨hsimple, hperf⟩ := isSimpleGroup_pairSide hc
      haveI := hsimple
      have hcardL : Nat.card ↥(pairSide pairData titsS 0) = 7800 :=
        card_pairSide hS hSide (k := 0) (by simp [pairData])
      let e : ↥(pairSide pairData titsS 0) ≃* ↥Y :=
        (Subgroup.equivMapOfInjective (pairSide pairData titsS 0) (MulAut.conj a).toMonoidHom
          (MulAut.conj a).injective).trans (MulEquiv.subgroupCongr hYeq.symm)
      exact SolvableOrSimpleDerived.of_mulEquiv e
        (SolvableOrSimpleDerived.of_simple_perfect hperf hcardL)

end Core

end CFSG.StandardType.TitsFive

namespace CFSG.StandardType

open CFSG.StandardType.TitsFive CFSG.StandardType.TitsOvergroup CFSG.StandardType.SylowOvergroup
open CFSG.StandardType.TitsGenerators
open CFSG.Sporadic.Schreier.Tits (titsD)

theorem ggSeitzExcTitsFiveInput_holds :
    GGSeitzExcTitsFiveInput := by
  intro K _ _ d hd he X hX1 h5
  obtain ⟨d1, hv⟩ := d
  have hd' : d1 = .tits := hd
  subst hd'
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, he⟩)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc : titsFiveCheck () = true := Certificates.certificate465004
  obtain ⟨hpair, -, -, -⟩ := titsFiveCheck_parts hc
  obtain ⟨hInv, hP, -, -, -, -, -, -⟩ := pairCheck_parts hpair
  have hS := sound_pairData hInv
  have hG : pairG pairData titsS = titsD := titsD_eq_closure_titsS.symm
  have hPG : pairP pairData titsS ≤ titsD := hG ▸ pairP_le_pairG
  have hP25 : Nat.card ↥(pairP pairData titsS) = 5 ^ 2 := by
    rw [card_pairP hS hP]
    rfl
  have hD : Nat.card ↥titsD = 5 ^ 2 * 718848 := by
    rw [CFSG.Sporadic.Schreier.Tits.card_titsD]
    norm_num
  have hsol := solvableOrSimpleDerived_of_sylow_le (Q := Equiv.Perm (Fin pairData.n)) (G := titsD)
    (P := pairP pairData titsS) (p := 5) (m := 7800) hPG hP25 hD (by norm_num)
    (fun Y hPY hYG hY => solvableOrSimpleDerived_of_pairP_le hc hPY hYG hY)
  exact forall_of_mulEquiv e (fun A _ => SolvableOrSimpleDerived 7800 A)
    (fun A B _ _ f h => SolvableOrSimpleDerived.of_mulEquiv f h) hsol X hX1 h5

end CFSG.StandardType
