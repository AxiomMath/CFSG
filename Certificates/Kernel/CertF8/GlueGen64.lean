module

public import Certificates.Data.Kernel.CertF8.Gen64
public import CFSG.Certificates.Kernel.CertF8.F64Sound

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8 CFSG.KC.CertF8.G64 CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
  CFSG.AGLEmbedding.ChevOuter

theorem chGen64Let : ∀ k : Fin 16, codeA64 (letterArr k.val) = letK.getD k.val oneK := by
  decide +kernel

theorem chGen64One : codeA64 oneArr = oneK := by
  decide +kernel

theorem letV_eq {β : Sort _} (y : ℕ) (k : ℕ → β) : letV y k = k y := by
  cases y <;> rfl

theorem letQ_eq {β : Sort _} (p : ℕ × ℕ) (k : ℕ × ℕ → β) : letQ p k = k p := by
  simp only [letQ, letV_eq]

theorem eqQ_eq (x y : ℕ × ℕ) : eqQ x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [eqQ, Bool.and_eq_true, Nat.beq_eq, Prod.ext_iff]

theorem decide_code {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64) :
    decide (p = q) = eqQ (codePr64 p) (codePr64 q) := by
  rw [eqQ_eq]
  exact decide_eq_decide.mpr ⟨fun h => h ▸ rfl, codePr64_inj hp hq⟩

theorem codePr64_oneP : codePr64 oneP = oneQ := by
  simp only [codePr64, oneP, oneQ, chGen64One]

theorem codeA64_letterArr (k : ℕ) : codeA64 (letterArr k) = letK.getD k oneK := by
  by_cases hk : k < 16
  · exact chGen64Let ⟨k, hk⟩
  · have h1 : letterArr k = oneArr := by
      rw [letterArr, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [letterTable]; omega)]
      rfl
    have h2 : letK.getD k oneK = oneK := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [letK]; omega)]
      rfl
    rw [h1, h2, chGen64One]

theorem codePr64_symP (s : ℕ) : codePr64 (symP s) = symQ s := by
  unfold symP symQ
  split_ifs
  · simp only [codePr64, codeA64_letterArr]
  · simp only [codePr64, chGen64One]

theorem codePr64_wordP (w : List ℕ) : codePr64 (wordP w) = wordQ w := by
  induction w with
  | nil => exact codePr64_oneP
  | cons s w ih =>
    change codePr64 (mulP (symP s) (wordP w)) = mulPr64 (symQ s) (wordQ w)
    rw [codePr64_mulP, codePr64_symP, ih]

theorem codePr64_powP (p : Pr) (n : ℕ) : codePr64 (powP p n) = powQ (codePr64 p) n := by
  induction n with
  | zero => exact codePr64_oneP
  | succ n ih =>
    change codePr64 (mulP p (powP p n)) = mulPr64 (codePr64 p) (powQ (codePr64 p) n)
    rw [codePr64_mulP, ih]

theorem codePr64_foldl (alph : ℕ → Pr) (alphQ : ℕ → ℕ × ℕ)
    (h : ∀ s, codePr64 (alph s) = alphQ s) (w : List ℕ) (acc : Pr) :
    codePr64 (w.foldl (fun acc s => mulP acc (alph s)) acc) =
      w.foldl (fun acc s => mulPr64 acc (alphQ s)) (codePr64 acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons s w ih =>
    simp only [List.foldl_cons]
    rw [ih, codePr64_mulP, h]

theorem codePr64_prodP (alph : ℕ → Pr) (alphQ : ℕ → ℕ × ℕ)
    (h : ∀ s, codePr64 (alph s) = alphQ s) (w : List ℕ) :
    codePr64 (prodP alph w) = prodQ alphQ w := by
  rw [prodP, prodQ, codePr64_foldl alph alphQ h, codePr64_oneP]

theorem size_foldl (alph : ℕ → Pr) (w : List ℕ) (acc : Pr) (hacc : acc.1.size = 64) :
    (w.foldl (fun acc s => mulP acc (alph s)) acc).1.size = 64 := by
  induction w generalizing acc with
  | nil => exact hacc
  | cons s w ih =>
    rw [List.foldl_cons]
    exact ih _ (size_mulP _ _)

theorem size_prodP (alph : ℕ → Pr) (w : List ℕ) : (prodP alph w).1.size = 64 :=
  size_foldl alph w oneP size_oneP

theorem code_getD (A : Array Pr) (k : ℕ) :
    codePr64 (A.getD k oneP) = (A.toList.map codePr64).getD k oneQ := by
  rw [← codePr64_oneP, List.getD_map, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem tab12_code (f : ℕ → ℕ → List ℕ) :
    (#[wordP (f 0 0), wordP (f 0 1), wordP (f 0 2), wordP (f 1 0), wordP (f 1 1), wordP (f 1 2),
      wordP (f 2 0), wordP (f 2 1), wordP (f 2 2), wordP (f 3 0), wordP (f 3 1),
      wordP (f 3 2)] : Array Pr).toList.map codePr64 =
    [wordQ (f 0 0), wordQ (f 0 1), wordQ (f 0 2), wordQ (f 1 0), wordQ (f 1 1), wordQ (f 1 2),
      wordQ (f 2 0), wordQ (f 2 1), wordQ (f 2 2), wordQ (f 3 0), wordQ (f 3 1), wordQ (f 3 2)] := by
  simp only [List.map_toArray, List.map_cons, List.map_nil, codePr64_wordP]

theorem ePTable_code : ePTable.toList.map codePr64 = ePTabQ := tab12_code eWord

theorem nTable_code : nTable.toList.map codePr64 = nTabQ := tab12_code fun c j => (pEntry c j).2.2

theorem nInvTable_code : nInvTable.toList.map codePr64 = nInvTabQ :=
  tab12_code fun c j => invWord (pEntry c j).2.2

theorem codePr64_eP (c i : ℕ) : codePr64 (eP c i) = ePQ c i := by
  rw [eP, ePQ, code_getD, ePTable_code]

theorem codePr64_eAlph (c s : ℕ) : codePr64 (eAlph c s) = eAlphQ c s := by
  unfold eAlph eAlphQ
  split_ifs
  · exact codePr64_eP c _
  · rw [codePr64_powP, codePr64_eP]

theorem codePr64_nP (c j : ℕ) : codePr64 (nP c j) = nQ c j := by
  rw [nP, nQ, code_getD, nTable_code]

theorem codePr64_nInvP (c j : ℕ) : codePr64 (nInvP c j) = nInvQ c j := by
  rw [nInvP, nInvQ, code_getD, nInvTable_code]

theorem codePr64_pAlph (c s : ℕ) : codePr64 (pAlph c s) = pAlphQ c s := by
  unfold pAlph pAlphQ
  split_ifs
  · exact codePr64_nP c _
  · exact codePr64_nInvP c _

theorem rBase_code (c : ℕ) : (rBase c).toList.map codePr64 = rBaseQ c := by
  simp only [rBase, rBaseQ, List.map_toArray, List.map_cons, List.map_nil,
    codePr64_prodP (pAlph c) (pAlphQ c) (codePr64_pAlph c)]

theorem slp_code (rules : List (ℕ × ℕ)) (tab : Array Pr) :
    (rules.foldl slpStep tab).toList.map codePr64 =
      rules.foldl slpStepQ (tab.toList.map codePr64) := by
  induction rules generalizing tab with
  | nil => rfl
  | cons r rules ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    rw [slpStep, slpStepQ, letQ_eq, Array.toList_push, List.map_append, List.map_cons,
      List.map_nil, codePr64_mulP, code_getD, code_getD]

theorem symTab_code (c : ℕ) : (symTab c).toList.map codePr64 = symTabQ c := by
  rw [symTab, symTabQ, slp_code, rBase_code]

theorem poolCheck_code (e : List ℕ × List ℕ × List ℕ) (u v n ni : Pr) :
    (e.1.all (· < 6) && e.2.1.all (· < 6) && e.2.2.all (· < 16) &&
      decide (powP u 3 = oneP) && decide (powP v 3 = oneP) && decide (mulP u v = mulP v u) &&
      (List.range 3).all (fun a => (List.range 3).all fun b =>
        (a == 0 && b == 0) || decide (mulP (powP u a) (powP v b) ≠ oneP)) &&
      decide (mulP u n = mulP n u) && decide (mulP v n = mulP n v) &&
      decide (mulP n ni = oneP)) =
    poolChkQ e (codePr64 u) (codePr64 v) (codePr64 n) (codePr64 ni) := by
  simp only [poolChkQ, decide_not, decide_code (size_powP _ _) size_oneP,
    decide_code (size_mulP _ _) (size_mulP _ _), decide_code (size_mulP _ _) size_oneP,
    codePr64_mulP, codePr64_powP, codePr64_oneP]

theorem genPoolCheck_eq (c j : ℕ) : genPoolCheck c j = genPoolChkQ c j := by
  rw [genPoolCheck, genPoolChkQ, letQ_eq, letQ_eq, letQ_eq, letQ_eq, poolCheck_code,
    codePr64_prodP (eAlph c) (eAlphQ c) (codePr64_eAlph c),
    codePr64_prodP (eAlph c) (eAlphQ c) (codePr64_eAlph c), codePr64_nP, codePr64_nInvP]

theorem genRCheck_eq (c : ℕ) : genRCheck c = genRChkQ c := by
  rw [genRCheck, genRChkQ, rChkQ, decide_code (size_mulP _ _) size_oneP,
    decide_code (size_mulP _ _) size_oneP, codePr64_mulP, codePr64_mulP, code_getD, code_getD,
    code_getD, code_getD, rBase_code, codePr64_oneP]

theorem genSlpCheck_eq {c : ℕ} (hc : c < 4) : genSlpCheck c = genSlpChkQ c := by
  have hs : sAlph c = fun s => (symTab c).getD s oneP := by
    funext s
    rw [sAlph, symTabs_eq hc]
  have ha : ∀ s, codePr64 ((symTab c).getD s oneP) = (symTabQ c).getD s oneQ := fun s => by
    rw [code_getD, symTab_code]
  have hk : ∀ k, decide (prodP (sAlph c) (tWord c k) = (letterArr k, 0)) =
      eqQ (prodQ (fun s => (symTabQ c).getD s oneQ) (tWord c k)) (letK.getD k oneK, 0) := by
    intro k
    rw [decide_code (size_prodP _ _) (size_letterArr k), hs, codePr64_prodP _ _ ha]
    simp only [codePr64, codeA64_letterArr]
  rw [genSlpCheck, genSlpChkQ, slpChkQ]
  simp only [hk]

theorem genCheckClass_eq {c : ℕ} (hc : c < 4) : genCheckClass c = genCheckClassQ c := by
  have hp : genPoolCheck c = genPoolChkQ c := funext (genPoolCheck_eq c)
  rw [genCheckClass, genCheckClassQ, genRCheck_eq, genSlpCheck_eq hc, hp]

end Certificates.Kernel.CertF8

end
