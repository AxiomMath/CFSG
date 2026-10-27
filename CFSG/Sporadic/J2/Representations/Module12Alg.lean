module

public import CFSG.Sporadic.J2.Representations.Module12
public import CFSG.RepresentationTheory.GF2.Independence

public section

namespace CFSG.Sporadic.J2.Module12

open Module
open CFSG.RepresentationTheory.GF2

@[expose] def matOfMask (m : ℕ) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun r c => ((m >>> (12 * r.val + c.val)) &&& 1 : ℕ)

private def bitZ (m j : ℕ) : ZMod 2 := ((m >>> j) &&& 1 : ℕ)

private theorem bitZ_eq (m j : ℕ) : bitZ m j = if m.testBit j then 1 else 0 := by
  rw [bitZ, Nat.and_one_is_mod, ← Nat.decide_shiftRight_mod_two_eq_one]
  rcases Nat.mod_two_eq_zero_or_one (m >>> j) with h | h <;> simp [h]

private theorem bitZ_zero (j : ℕ) : bitZ 0 j = 0 := by
  simp [bitZ_eq]

private theorem bitZ_xor (a b j : ℕ) : bitZ (a ^^^ b) j = bitZ a j + bitZ b j := by
  rw [bitZ_eq, bitZ_eq, bitZ_eq, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

private theorem bitZ_two_pow (i j : ℕ) : bitZ (2 ^ i) j = if i = j then 1 else 0 := by
  simp [bitZ_eq, Nat.testBit_two_pow]

private def xorSum {n : ℕ} (f : Fin n → ℕ) : ℕ :=
  (List.finRange n).foldr (fun k acc => f k ^^^ acc) 0

private theorem bitZ_xorSum {n : ℕ} (f : Fin n → ℕ) (j : ℕ) :
    bitZ (xorSum f) j = ∑ k, bitZ (f k) j := by
  rw [Fin.sum_univ_def, xorSum]
  generalize List.finRange n = l
  induction l with
  | nil => simp [bitZ_zero]
  | cons k l ih => rw [List.foldr_cons, bitZ_xor, ih, List.map_cons, List.sum_cons]

private theorem mul_eq_one_of_xorSum {n : ℕ} {X Y : Matrix (Fin n) (Fin n) (ZMod 2)}
    (ys : Fin n → ℕ) (hY : ∀ k j, Y k j = bitZ (ys k) j.val)
    (h : ∀ i, (xorSum fun k => if X i k = 1 then ys k else 0) = 2 ^ i.val) : X * Y = 1 := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h10 : (0 : ZMod 2) ≠ 1 := by decide
  ext i j
  have hij : (X * Y) i j = bitZ (xorSum fun k => if X i k = 1 then ys k else 0) j.val := by
    rw [bitZ_xorSum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases h01 (X i k) with hk | hk <;> simp [hk, hY, h10, bitZ_zero]
  rw [hij, h, bitZ_two_pow, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

private def mulMask (x y : ℕ) : ℕ :=
  xorSum fun r : Fin 12 => xorSum fun k : Fin 12 =>
    if x.testBit (12 * r.val + k.val) then ((y >>> (12 * k.val)) % 2 ^ 12) <<< (12 * r.val)
    else 0

private theorem bitZ_moveRow (y : ℕ) (r k r' c : Fin 12) :
    bitZ (((y >>> (12 * k.val)) % 2 ^ 12) <<< (12 * r.val)) (12 * r'.val + c.val) =
      if r = r' then bitZ y (12 * k.val + c.val) else 0 := by
  have hc := c.isLt
  rw [bitZ_eq, bitZ_eq, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases h : r = r'
  · subst h
    simp [hc]
  · have h' : r.val ≠ r'.val := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rintro ⟨h1, h2, -⟩
    omega

private theorem matOfMask_mulMask (x y : ℕ) :
    matOfMask (mulMask x y) = matOfMask x * matOfMask y := by
  ext r' c
  have hterm (r k : Fin 12) :
      bitZ (if x.testBit (12 * r.val + k.val) then
          ((y >>> (12 * k.val)) % 2 ^ 12) <<< (12 * r.val) else 0) (12 * r'.val + c.val) =
        if r = r' then matOfMask x r' k * matOfMask y k c else 0 := by
    by_cases h : r = r'
    · rw [if_pos h, ← h, show matOfMask x r k = bitZ x (12 * r.val + k.val) from rfl,
        show matOfMask y k c = bitZ y (12 * k.val + c.val) from rfl, bitZ_eq x]
      cases x.testBit (12 * r.val + k.val)
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, bitZ_zero, zero_mul]
      · rw [if_pos rfl, if_pos rfl, one_mul, bitZ_moveRow, if_pos rfl]
    · rw [if_neg h]
      split_ifs
      · rw [bitZ_moveRow, if_neg h]
      · exact bitZ_zero _
  have hrow (r : Fin 12) :
      bitZ (xorSum fun k : Fin 12 => if x.testBit (12 * r.val + k.val) then
          ((y >>> (12 * k.val)) % 2 ^ 12) <<< (12 * r.val) else 0) (12 * r'.val + c.val) =
        if r = r' then (matOfMask x * matOfMask y) r' c else 0 := by
    rw [bitZ_xorSum, Matrix.mul_apply]
    split_ifs with h
    · exact Finset.sum_congr rfl fun k _ => (hterm r k).trans (if_pos h)
    · exact Finset.sum_eq_zero fun k _ => (hterm r k).trans (if_neg h)
  show bitZ (mulMask x y) (12 * r'.val + c.val) = _
  rw [mulMask, bitZ_xorSum, Finset.sum_congr rfl fun r _ => hrow r, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ r')]

private theorem matOfMask_xor (a b : ℕ) : matOfMask (a ^^^ b) = matOfMask a + matOfMask b := by
  ext r c
  exact bitZ_xor a b _

private def idMask : ℕ := xorSum fun r : Fin 12 => 2 ^ (13 * r.val)

private theorem matOfMask_idMask : matOfMask idMask = 1 := by decide +kernel

def amask : ℕ := 11150416308292851365123079521382911506124866
def bmask : ℕ := 16728282320928131553089370956672205175587749
def jmask : ℕ := 106432203643881961226294606737284164996951

def Amat : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfMask amask

def Bmat : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfMask bmask

def Jm : Matrix (Fin 12) (Fin 12) (ZMod 2) := matOfMask jmask

theorem Amat_toM : Amat = toM12 a12 := by decide +kernel

theorem Bmat_toM : Bmat = toM12 b12 := by decide +kernel

theorem Amat_eq : Amat = (A12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
  Amat_toM.trans rfl

theorem Bmat_eq : Bmat = (B12 : Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
  Bmat_toM.trans rfl

theorem Jm_sq : Jm * Jm = Jm + 1 := by
  rw [Jm, ← matOfMask_mulMask, ← matOfMask_idMask, ← matOfMask_xor]
  exact congrArg matOfMask (by decide +kernel)

theorem Jm_mul_A : Jm * Amat = Amat * Jm := by
  rw [Jm, Amat, ← matOfMask_mulMask, ← matOfMask_mulMask]
  exact congrArg matOfMask (by decide +kernel)

theorem Jm_mul_B : Jm * Bmat = Bmat * Jm := by
  rw [Jm, Bmat, ← matOfMask_mulMask, ← matOfMask_mulMask]
  exact congrArg matOfMask (by decide +kernel)

@[expose] def CJ : Subalgebra (ZMod 2) (Matrix (Fin 12) (Fin 12) (ZMod 2)) where
  carrier := {X | X * Jm = Jm * X}
  add_mem' := by
    intro X Y hX hY
    show (X + Y) * Jm = Jm * (X + Y)
    rw [Matrix.add_mul, Matrix.mul_add, hX, hY]
  zero_mem' := by
    show (0 : Matrix (Fin 12) (Fin 12) (ZMod 2)) * Jm = Jm * 0
    rw [Matrix.zero_mul, Matrix.mul_zero]
  mul_mem' := by
    intro X Y hX hY
    show (X * Y) * Jm = Jm * (X * Y)
    rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  one_mem' := by
    show (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) * Jm = Jm * 1
    rw [Matrix.one_mul, Matrix.mul_one]
  algebraMap_mem' := by
    intro a
    show (algebraMap (ZMod 2) (Matrix (Fin 12) (Fin 12) (ZMod 2)) a) * Jm =
      Jm * (algebraMap (ZMod 2) (Matrix (Fin 12) (Fin 12) (ZMod 2)) a)
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]

theorem Amat_mem_CJ : Amat ∈ CJ := by
  show Amat * Jm = Jm * Amat
  exact Jm_mul_A.symm

theorem Bmat_mem_CJ : Bmat ∈ CJ := by
  show Bmat * Jm = Jm * Bmat
  exact Jm_mul_B.symm

@[expose] def Aalg : Subalgebra (ZMod 2) (Matrix (Fin 12) (Fin 12) (ZMod 2)) :=
  Algebra.adjoin (ZMod 2) ({Amat, Bmat} : Set (Matrix (Fin 12) (Fin 12) (ZMod 2)))

theorem Aalg_le_CJ : Aalg ≤ CJ := by
  refine Algebra.adjoin_le ?_
  rintro X (rfl | rfl)
  · exact Amat_mem_CJ
  · exact Bmat_mem_CJ

noncomputable def evalWord : List ℕ → Matrix (Fin 12) (Fin 12) (ZMod 2)
  | [] => 1
  | g :: w => (if g = 0 then Amat else Bmat) * evalWord w

theorem evalWord_mem_Aalg : ∀ w : List ℕ, evalWord w ∈ Aalg
  | [] => by simpa [evalWord] using Aalg.one_mem
  | g :: w => by
      have hg : (if g = 0 then Amat else Bmat) ∈ Aalg := by
        split_ifs with h
        · exact Algebra.subset_adjoin (by simp)
        · exact Algebra.subset_adjoin (by simp)
      simpa [evalWord] using Aalg.mul_mem hg (evalWord_mem_Aalg w)

private def evalMask : List ℕ → ℕ
  | [] => idMask
  | g :: w => mulMask (if g = 0 then amask else bmask) (evalMask w)

private theorem evalWord_eq : ∀ w : List ℕ, evalWord w = matOfMask (evalMask w)
  | [] => by rw [evalWord, evalMask, matOfMask_idMask]
  | g :: w => by
      rw [evalWord, evalMask, matOfMask_mulMask, ← evalWord_eq w]
      split_ifs <;> rfl

@[expose] def wmask : List ℕ := [
  11150416308292851365123079521382911506124866,
  16728282320928131553089370956672205175587749,
  11151733894906779683522195341810241573494785,
  16730493367314927144662170889205167573466258,
  11327319928797318861169379350024125193326430,
  5579270518823497350734924246754656039731876,
  11329372435930512503709686455254642309820537,
  5578462483304617101647074120010102872952016,
  3488575324385187616969941454157724656602635,
  176989875212440286363718572473392200647276,
  3487883749320131227750223002714475355654463,
  177447230910569803985132768685296446521464,
  8583326121830134660999228032190717956820611,
  18991839961175054011417248916401886087620717,
  20210901748489267515149593944124930001178363,
  8581123891978013772624525779956423400343975,
  18991917521696514496137966211441563807923084,
  20212637271805521875780668836475668964678298,
  15985956005348285625608145380339237571495989,
  13023330445458908566219240093326948987966662,
  19558803057843685055751111644666543424275163,
  13419929678937748740156297015916667306476207,
  15990496824726178821700336837262796093756052,
  13027691437513927160756307621702385295145884,
  19557954634141652389864414479224978695530233,
  13419429216809197247229952424247388726360360,
  13387261439730639910647301816185123775286084,
  12690661564190059050031841643642596393251859,
  13898312549407774209629066035715315950168111,
  13386956423503853679365223586056784092190657,
  12690287302278465349858208433759778568329529,
  13895256575297370594727773148541298072038559,
  7892287081582528133215891208031254642002772,
  19000697946922733015190618873055529189634099,
  7712712689019380632167682158674621814096085,
  5894236095892741931166887560483364855677900,
  7893521936950885807931251575933557778639738,
  18996379180736253370314126756331631109794210,
  7712019475291438612144430615820668634516125,
  5892370631739931644196964713783984377499564,
  6258848508659187588142730965130756809131971,
  16059276096890567644408294884213996500600405,
  18039613991151365147961275689379948324619228,
  6260726954645065157747458420859071962225578,
  16057359862618960092012121496304784311095824,
  18040650823881276659481812386410838516338620,
  18069548649359919764195360961968508896021307,
  2952811838761148278448845079172893235710871,
  197442166421540294012147955889913714282854,
  18681668920222697209108029442571216763071387,
  18067249705274454090471246058718046283247513,
  2951498725725809190798322563843615520227304,
  201090039469894789592642291179838282659648,
  18683166810306012006782393558078570162524089,
  22059661909905059688781325406677712123209389,
  5949817867904289163372726716854912686008629,
  10573975161199634593432257981589891025775501,
  22056781859495345699478664124728175213224381,
  5948937762365492500571342657169492256027440,
  10577554182527788757367144159395309048540989,
  20683772207162198962272698913435590131386460,
  7686776427003074637294621803202518684838468,
  20688457478201827134127687195390349198951964,
  7684787016352269730793749597461339666966720,
  19683384578026218861746597240095980784910484,
  15622904308161016760511179511206376931897219,
  19682562159613689749111933337833409633257172,
  15622337495796764034196430389086004115190018,
  2854802987281228325459999769765868203674049,
  2854472257012263451549116453130789193130339,
  20698426791186697483769748326996345412920231,
  20698154007465012296288035242502066608873655]

def wordL : List (List ℕ) := [
  [0],
  [1],
  [0, 0],
  [0, 1],
  [1, 0],
  [1, 1],
  [0, 1, 0],
  [0, 1, 1],
  [1, 0, 1],
  [1, 1, 0],
  [0, 1, 0, 1],
  [0, 1, 1, 0],
  [1, 0, 1, 0],
  [1, 0, 1, 1],
  [1, 1, 0, 1],
  [0, 1, 0, 1, 0],
  [0, 1, 0, 1, 1],
  [0, 1, 1, 0, 1],
  [1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0],
  [1, 1, 0, 1, 0],
  [1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0],
  [0, 1, 1, 0, 1, 0],
  [0, 1, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1],
  [1, 0, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0],
  [1, 0, 1, 1, 0, 1, 0],
  [1, 0, 1, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0],
  [0, 1, 0, 1, 1, 0, 1, 0],
  [0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 0],
  [0, 1, 0, 1, 0, 1, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0],
  [1, 0, 1, 0, 1, 1, 0, 1, 0],
  [1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
  [1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
  [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]]

@[expose] noncomputable def wmat (i : Fin 72) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  matOfMask (wmask.getD i.val 0)

private theorem wmask_eq :
    ∀ i : Fin 72, wmask.getD i.val 0 = evalMask (wordL.getD i.val []) := by
  decide +kernel

theorem wmat_words : ∀ i : Fin 72, wmat i = evalWord (wordL.getD i.val []) := fun i =>
  (congrArg matOfMask (wmask_eq i)).trans (evalWord_eq _).symm

theorem wmat_mem_Aalg (i : Fin 72) : wmat i ∈ Aalg := by
  have h := wmat_words i
  rw [h]
  exact evalWord_mem_Aalg _

@[expose] def rawEq (i j : Fin 12) : Matrix (Fin 12) (Fin 12) (ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun X := (X * Jm + Jm * X) i j
  map_add' X Y := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
    abel
  map_smul' a X := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

@[expose] def singleMat (p : Fin 12 × Fin 12) : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  fun r c => if r = p.1 ∧ c = p.2 then 1 else 0

private theorem rawEq_singleMat (a b : Fin 12) (p : Fin 12 × Fin 12) :
    rawEq a b (singleMat p) =
      (if a = p.1 then Jm p.2 b else 0) + (if b = p.2 then Jm a p.1 else 0) := by
  have h1 : (singleMat p * Jm) a b = if a = p.1 then Jm p.2 b else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single p.2]
    · simp [singleMat, ite_mul]
    · intro k _ hk
      simp [singleMat, hk]
    · simp
  have h2 : (Jm * singleMat p) a b = if b = p.2 then Jm a p.1 else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single p.1]
    · simp [singleMat, mul_ite]
    · intro k _ hk
      simp [singleMat, hk]
    · simp
  show (singleMat p * Jm + Jm * singleMat p) a b = _
  rw [Matrix.add_apply, h1, h2]

def eqIdxList : List (Fin 12 × Fin 12) := [
  (⟨0, by decide⟩, ⟨0, by decide⟩),
  (⟨0, by decide⟩, ⟨1, by decide⟩),
  (⟨0, by decide⟩, ⟨2, by decide⟩),
  (⟨0, by decide⟩, ⟨3, by decide⟩),
  (⟨0, by decide⟩, ⟨4, by decide⟩),
  (⟨0, by decide⟩, ⟨5, by decide⟩),
  (⟨0, by decide⟩, ⟨6, by decide⟩),
  (⟨0, by decide⟩, ⟨7, by decide⟩),
  (⟨0, by decide⟩, ⟨8, by decide⟩),
  (⟨0, by decide⟩, ⟨9, by decide⟩),
  (⟨0, by decide⟩, ⟨10, by decide⟩),
  (⟨0, by decide⟩, ⟨11, by decide⟩),
  (⟨1, by decide⟩, ⟨0, by decide⟩),
  (⟨1, by decide⟩, ⟨1, by decide⟩),
  (⟨1, by decide⟩, ⟨2, by decide⟩),
  (⟨1, by decide⟩, ⟨3, by decide⟩),
  (⟨1, by decide⟩, ⟨4, by decide⟩),
  (⟨1, by decide⟩, ⟨5, by decide⟩),
  (⟨1, by decide⟩, ⟨6, by decide⟩),
  (⟨1, by decide⟩, ⟨7, by decide⟩),
  (⟨1, by decide⟩, ⟨8, by decide⟩),
  (⟨1, by decide⟩, ⟨9, by decide⟩),
  (⟨1, by decide⟩, ⟨10, by decide⟩),
  (⟨1, by decide⟩, ⟨11, by decide⟩),
  (⟨2, by decide⟩, ⟨0, by decide⟩),
  (⟨2, by decide⟩, ⟨1, by decide⟩),
  (⟨2, by decide⟩, ⟨2, by decide⟩),
  (⟨2, by decide⟩, ⟨3, by decide⟩),
  (⟨2, by decide⟩, ⟨4, by decide⟩),
  (⟨2, by decide⟩, ⟨5, by decide⟩),
  (⟨2, by decide⟩, ⟨6, by decide⟩),
  (⟨2, by decide⟩, ⟨7, by decide⟩),
  (⟨2, by decide⟩, ⟨8, by decide⟩),
  (⟨2, by decide⟩, ⟨9, by decide⟩),
  (⟨2, by decide⟩, ⟨10, by decide⟩),
  (⟨2, by decide⟩, ⟨11, by decide⟩),
  (⟨3, by decide⟩, ⟨0, by decide⟩),
  (⟨3, by decide⟩, ⟨1, by decide⟩),
  (⟨3, by decide⟩, ⟨2, by decide⟩),
  (⟨3, by decide⟩, ⟨3, by decide⟩),
  (⟨3, by decide⟩, ⟨4, by decide⟩),
  (⟨3, by decide⟩, ⟨5, by decide⟩),
  (⟨3, by decide⟩, ⟨6, by decide⟩),
  (⟨3, by decide⟩, ⟨7, by decide⟩),
  (⟨3, by decide⟩, ⟨8, by decide⟩),
  (⟨3, by decide⟩, ⟨9, by decide⟩),
  (⟨3, by decide⟩, ⟨10, by decide⟩),
  (⟨3, by decide⟩, ⟨11, by decide⟩),
  (⟨4, by decide⟩, ⟨0, by decide⟩),
  (⟨4, by decide⟩, ⟨1, by decide⟩),
  (⟨4, by decide⟩, ⟨2, by decide⟩),
  (⟨4, by decide⟩, ⟨3, by decide⟩),
  (⟨4, by decide⟩, ⟨4, by decide⟩),
  (⟨4, by decide⟩, ⟨5, by decide⟩),
  (⟨4, by decide⟩, ⟨6, by decide⟩),
  (⟨4, by decide⟩, ⟨7, by decide⟩),
  (⟨4, by decide⟩, ⟨8, by decide⟩),
  (⟨4, by decide⟩, ⟨9, by decide⟩),
  (⟨4, by decide⟩, ⟨10, by decide⟩),
  (⟨4, by decide⟩, ⟨11, by decide⟩),
  (⟨5, by decide⟩, ⟨0, by decide⟩),
  (⟨5, by decide⟩, ⟨1, by decide⟩),
  (⟨5, by decide⟩, ⟨2, by decide⟩),
  (⟨5, by decide⟩, ⟨3, by decide⟩),
  (⟨5, by decide⟩, ⟨4, by decide⟩),
  (⟨5, by decide⟩, ⟨5, by decide⟩),
  (⟨5, by decide⟩, ⟨6, by decide⟩),
  (⟨5, by decide⟩, ⟨7, by decide⟩),
  (⟨5, by decide⟩, ⟨8, by decide⟩),
  (⟨5, by decide⟩, ⟨9, by decide⟩),
  (⟨5, by decide⟩, ⟨10, by decide⟩),
  (⟨5, by decide⟩, ⟨11, by decide⟩)]

@[expose] def qIdxList : List (Fin 12 × Fin 12) := [
  (⟨6, by decide⟩, ⟨0, by decide⟩),
  (⟨6, by decide⟩, ⟨1, by decide⟩),
  (⟨6, by decide⟩, ⟨2, by decide⟩),
  (⟨6, by decide⟩, ⟨3, by decide⟩),
  (⟨6, by decide⟩, ⟨4, by decide⟩),
  (⟨6, by decide⟩, ⟨5, by decide⟩),
  (⟨6, by decide⟩, ⟨6, by decide⟩),
  (⟨6, by decide⟩, ⟨7, by decide⟩),
  (⟨6, by decide⟩, ⟨8, by decide⟩),
  (⟨6, by decide⟩, ⟨9, by decide⟩),
  (⟨6, by decide⟩, ⟨10, by decide⟩),
  (⟨6, by decide⟩, ⟨11, by decide⟩),
  (⟨7, by decide⟩, ⟨0, by decide⟩),
  (⟨7, by decide⟩, ⟨1, by decide⟩),
  (⟨7, by decide⟩, ⟨2, by decide⟩),
  (⟨7, by decide⟩, ⟨3, by decide⟩),
  (⟨7, by decide⟩, ⟨4, by decide⟩),
  (⟨7, by decide⟩, ⟨5, by decide⟩),
  (⟨7, by decide⟩, ⟨6, by decide⟩),
  (⟨7, by decide⟩, ⟨7, by decide⟩),
  (⟨7, by decide⟩, ⟨8, by decide⟩),
  (⟨7, by decide⟩, ⟨9, by decide⟩),
  (⟨7, by decide⟩, ⟨10, by decide⟩),
  (⟨7, by decide⟩, ⟨11, by decide⟩),
  (⟨8, by decide⟩, ⟨0, by decide⟩),
  (⟨8, by decide⟩, ⟨1, by decide⟩),
  (⟨8, by decide⟩, ⟨2, by decide⟩),
  (⟨8, by decide⟩, ⟨3, by decide⟩),
  (⟨8, by decide⟩, ⟨4, by decide⟩),
  (⟨8, by decide⟩, ⟨5, by decide⟩),
  (⟨8, by decide⟩, ⟨6, by decide⟩),
  (⟨8, by decide⟩, ⟨7, by decide⟩),
  (⟨8, by decide⟩, ⟨8, by decide⟩),
  (⟨8, by decide⟩, ⟨9, by decide⟩),
  (⟨8, by decide⟩, ⟨10, by decide⟩),
  (⟨8, by decide⟩, ⟨11, by decide⟩),
  (⟨9, by decide⟩, ⟨0, by decide⟩),
  (⟨9, by decide⟩, ⟨1, by decide⟩),
  (⟨9, by decide⟩, ⟨2, by decide⟩),
  (⟨9, by decide⟩, ⟨3, by decide⟩),
  (⟨9, by decide⟩, ⟨4, by decide⟩),
  (⟨9, by decide⟩, ⟨5, by decide⟩),
  (⟨9, by decide⟩, ⟨6, by decide⟩),
  (⟨9, by decide⟩, ⟨7, by decide⟩),
  (⟨9, by decide⟩, ⟨8, by decide⟩),
  (⟨9, by decide⟩, ⟨9, by decide⟩),
  (⟨9, by decide⟩, ⟨10, by decide⟩),
  (⟨9, by decide⟩, ⟨11, by decide⟩),
  (⟨10, by decide⟩, ⟨0, by decide⟩),
  (⟨10, by decide⟩, ⟨1, by decide⟩),
  (⟨10, by decide⟩, ⟨2, by decide⟩),
  (⟨10, by decide⟩, ⟨3, by decide⟩),
  (⟨10, by decide⟩, ⟨4, by decide⟩),
  (⟨10, by decide⟩, ⟨5, by decide⟩),
  (⟨10, by decide⟩, ⟨6, by decide⟩),
  (⟨10, by decide⟩, ⟨7, by decide⟩),
  (⟨10, by decide⟩, ⟨8, by decide⟩),
  (⟨10, by decide⟩, ⟨9, by decide⟩),
  (⟨10, by decide⟩, ⟨10, by decide⟩),
  (⟨10, by decide⟩, ⟨11, by decide⟩),
  (⟨11, by decide⟩, ⟨0, by decide⟩),
  (⟨11, by decide⟩, ⟨1, by decide⟩),
  (⟨11, by decide⟩, ⟨2, by decide⟩),
  (⟨11, by decide⟩, ⟨3, by decide⟩),
  (⟨11, by decide⟩, ⟨4, by decide⟩),
  (⟨11, by decide⟩, ⟨5, by decide⟩),
  (⟨11, by decide⟩, ⟨6, by decide⟩),
  (⟨11, by decide⟩, ⟨7, by decide⟩),
  (⟨11, by decide⟩, ⟨8, by decide⟩),
  (⟨11, by decide⟩, ⟨9, by decide⟩),
  (⟨11, by decide⟩, ⟨10, by decide⟩),
  (⟨11, by decide⟩, ⟨11, by decide⟩)]

def FinvList : List ℕ := [
  1152921504606846976,
  2305843009213693952,
  4611686018427387904,
  9223372036854775808,
  18446744073709551616,
  36893488147419103232,
  73786976294838206464,
  147573952589676412928,
  295147905179352825856,
  590295810358705651712,
  1180591620717411303424,
  2361183241434822606848,
  68736253953,
  137472507906,
  274945015812,
  549890031624,
  1099780063248,
  2199560126496,
  4399120252992,
  8798240505984,
  17596481011968,
  35192962023936,
  70385924047872,
  140771848095744,
  281543696191488,
  563087392382976,
  1126174784765952,
  2252349569531904,
  4504699139063808,
  9009398278127616,
  18018796556255232,
  36037593112510464,
  72075186225020928,
  144150372450041856,
  288300744900083712,
  576601489800167424,
  16781312,
  33562624,
  67125248,
  134250496,
  268500992,
  537001984,
  1074003968,
  2148007936,
  4296015872,
  8592031744,
  17184063488,
  34368126976,
  1152921573343105024,
  2305843146686210048,
  4611686293372420096,
  9223372586744840192,
  18446745173489680384,
  36893490346979360768,
  73786980693958721536,
  147573961387917443072,
  295147922775834886144,
  590295845551669772288,
  1180591691103339544576,
  2361183382206679089152,
  281474976714753,
  562949953429506,
  1125899906859012,
  2251799813718024,
  4503599627436048,
  9007199254872096,
  18014398509744192,
  36028797019488384,
  72057594038976768,
  144115188077953536,
  288230376155907072,
  576460752311814144]

def eqIdx (i : Fin 72) : Fin 12 × Fin 12 :=
  eqIdxList.getD i.val (0, 0)

@[expose] def qIdx (j : Fin 72) : Fin 12 × Fin 12 :=
  qIdxList.getD j.val (0, 0)

@[expose] def Fmat : Matrix (Fin 72) (Fin 72) (ZMod 2) :=
  fun i j => rawEq (eqIdx i).1 (eqIdx i).2 (singleMat (qIdx j))

def FinvMat : Matrix (Fin 72) (Fin 72) (ZMod 2) :=
  fun i j => ((FinvList.getD i.val 0 >>> j.val) &&& 1 : ℕ)

private theorem Fmat_rows : ∀ i : Fin 72,
    (xorSum fun k =>
      if (if (eqIdx i).1 = (qIdx k).1 then Jm (qIdx k).2 (eqIdx i).2 else 0) +
          (if (eqIdx i).2 = (qIdx k).2 then Jm (eqIdx i).1 (qIdx k).1 else 0) = 1 then
        FinvList.getD k.val 0
      else 0) = 2 ^ i.val := by
  decide +kernel

theorem Fmat_mul : Fmat * FinvMat = 1 :=
  mul_eq_one_of_xorSum (fun k => FinvList.getD k.val 0) (fun _ _ => rfl) fun i => by
    simpa only [Fmat, rawEq_singleMat] using Fmat_rows i

theorem FinvMat_mul : FinvMat * Fmat = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp Fmat_mul

@[expose] def Phi : Matrix (Fin 12) (Fin 12) (ZMod 2) →ₗ[ZMod 2] (Fin 72 → ZMod 2) where
  toFun X i := rawEq (eqIdx i).1 (eqIdx i).2 X
  map_add' X Y := by
    funext i
    exact (rawEq (eqIdx i).1 (eqIdx i).2).map_add X Y
  map_smul' a X := by
    funext i
    exact (rawEq (eqIdx i).1 (eqIdx i).2).map_smul a X

