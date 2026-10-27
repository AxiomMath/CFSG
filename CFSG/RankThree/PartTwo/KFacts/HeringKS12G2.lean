module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Config
public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Cases
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3168
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

namespace KS12G2

@[expose] def rowOf (m : List ℕ) (i : ℕ) : List ℕ :=
  (List.range 14).map fun k => m.getD (14 * i + k) 0

@[expose] def colOf (n : List ℕ) (j : ℕ) : List ℕ :=
  (List.range 14).map fun k => n.getD (14 * k + j) 0

@[expose] def mulF (m n : List ℕ) : List ℕ :=
  let R := (List.range 14).map (rowOf m)
  let C := (List.range 14).map (colOf n)
  (List.range 196).map fun t =>
    (List.zipWith (· * ·) (R.getD (t / 14) []) (C.getD (t % 14) [])).sum % 3

theorem rowOf_getD (m : List ℕ) {i : ℕ} (hi : i < 14) :
    ((List.range 14).map (rowOf m)).getD i [] = rowOf m i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem colOf_getD (n : List ℕ) {j : ℕ} (hj : j < 14) :
    ((List.range 14).map (colOf n)).getD j [] = colOf n j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hj]

theorem sum_zipWith_map (f g : ℕ → ℕ) (l : List ℕ) :
    (List.zipWith (· * ·) (l.map f) (l.map g)).sum = (l.map fun k => f k * g k).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]

theorem mulF_eq (m n : List ℕ) : mulF m n = mul14 m n := by
  simp only [mulF, mul14, dot, ent_toArray]
  refine List.map_congr_left fun t ht => ?_
  have ht' : t < 196 := List.mem_range.mp ht
  rw [rowOf_getD m (by omega : t / 14 < 14), colOf_getD n (Nat.mod_lt _ (by norm_num))]
  simp only [rowOf, colOf, sum_zipWith_map]

theorem canon14_mulF (m n : List ℕ) : canon14 (mulF m n) = true := by
  rw [mulF_eq]
  exact canon14_mul14 _ _

theorem dec14_mulF (m n : List ℕ) : dec14 (mulF m n) = dec14 m * dec14 n := by
  rw [mulF_eq, dec14_mul14]

@[expose] def genCode : ℕ → List ℕ
  | 0 => x0c
  | 1 => x1c
  | 2 => y0c
  | _ => y1c

@[expose] def wordCode : List ℕ → List ℕ
  | [] => one14
  | i :: w => mulF (genCode i) (wordCode w)

theorem wordCode_nil : wordCode [] = one14 := by
  simp only [wordCode]

theorem wordCode_cons (i : ℕ) (w : List ℕ) :
    wordCode (i :: w) = mulF (genCode i) (wordCode w) := by
  simp only [wordCode]

theorem canon14_wordCode (w : List ℕ) : canon14 (wordCode w) = true := by
  induction w with
  | nil => rw [wordCode_nil]; exact canon14_one14
  | cons i w _ => rw [wordCode_cons]; exact canon14_mulF _ _

@[expose] noncomputable def genGL :
    ℕ → GL (Fin 14) (ZMod 3)
  | 0 => gX 0
  | 1 => gX 1
  | 2 => gY 0
  | _ => gY 1

@[expose] noncomputable def wordGL
    (w : List ℕ) : GL (Fin 14) (ZMod 3) :=
  (w.map genGL).prod

theorem coe_genGL (i : ℕ) :
    ((genGL i : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (genCode i) := by
  match i with
  | 0 => exact coe_gX0
  | 1 => exact coe_gX1
  | 2 => exact coe_gY0
  | n + 3 => exact coe_gY1

theorem genGL_mem (i : ℕ) :
    genGL i ∈ R3 := by
  match i with
  | 0 => exact gX_mem 0
  | 1 => exact gX_mem 1
  | 2 => exact gY_mem 0
  | n + 3 => exact gY_mem 1

theorem wordGL_mem (w : List ℕ) :
    wordGL w ∈ R3 := by
  unfold wordGL
  refine Subgroup.list_prod_mem R3 fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact genGL_mem i

theorem wordGL_nil :
    wordGL [] = 1 := by
  simp [wordGL]

theorem wordGL_append (w w' : List ℕ) :
    wordGL (w ++ w') = wordGL w * wordGL w' := by
  simp only [wordGL, List.map_append, List.prod_append]

theorem wordGL_cons (i : ℕ)
    (w : List ℕ) : wordGL (i :: w) = genGL i * wordGL w := by
  simp only [wordGL, List.map_cons, List.prod_cons]

theorem coe_wordGL (w : List ℕ) :
    ((wordGL w : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (wordCode w) := by
  induction w with
  | nil => rw [wordGL_nil, Units.val_one, wordCode_nil, dec14_one14]
  | cons i w ih =>
    rw [wordGL_cons, Units.val_mul, coe_genGL, ih, wordCode_cons, dec14_mulF]

theorem wordGL_eq_iff_code
    {w w' : List ℕ} : wordGL w = wordGL w' ↔ wordCode w = wordCode w' := by
  constructor
  · intro e
    refine dec14_injective (canon14_wordCode w) (canon14_wordCode w') ?_
    rw [← coe_wordGL, ← coe_wordGL, e]
  · intro e
    refine Units.ext ?_
    rw [coe_wordGL, coe_wordGL, e]

@[expose] noncomputable def wordR3
    (w : List ℕ) : ↥R3 :=
  ⟨wordGL w, wordGL_mem w⟩

theorem wordR3_eq_iff
    {w w' : List ℕ} : wordR3 w = wordR3 w' ↔ wordCode w = wordCode w' := by
  rw [← wordGL_eq_iff_code]
  exact Subtype.ext_iff

theorem wordR3_eq_of_code
    {w w' : List ℕ} (h : wordCode w = wordCode w') : wordR3 w = wordR3 w' :=
  wordR3_eq_iff.mpr h

theorem wordR3_append (w w' : List ℕ) :
    wordR3 (w ++ w') = wordR3 w * wordR3 w' :=
  Subtype.ext (wordGL_append w w')

theorem wordR3_nil :
    wordR3 [] = 1 :=
  Subtype.ext wordGL_nil

theorem wordR3_sq (w : List ℕ) :
    wordR3 w ^ 2 = wordR3 (w ++ w) := by
  rw [wordR3_append, pow_two]

theorem wordR3_ne_one_of
    {w : List ℕ} (h : wordCode w ≠ one14) : wordR3 w ≠ 1 := by
  intro e
  exact h (wordR3_eq_iff.mp (e.trans wordR3_nil.symm))

theorem wordR3_ne_of_code
    {w w' : List ℕ} (h : wordCode w ≠ wordCode w') : wordR3 w ≠ wordR3 w' :=
  fun e => h (wordR3_eq_iff.mp e)

theorem conj_inv_of_mul_eq {Q : Type*} [Group Q] {g x : Q} (h3 : x ^ 3 = 1)
    (h : g * x = x ^ 2 * g) : g * x * g⁻¹ = x⁻¹ := by
  have hinv : x⁻¹ = x ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact h3
  rw [hinv, h, mul_inv_cancel_right]

@[expose] def wX : List ℕ := [1]

@[expose] def wY : List ℕ := [2]

@[expose] def wG : List ℕ := [0, 2, 0]

@[expose] def wH : List ℕ := [3, 1, 3]

@[expose] def wT : List ℕ := [1, 3, 1, 3]

theorem wX_cube :
    wordR3 wX ^ 3 = 1 := by
  rw [pow_three', ← wordR3_append, ← wordR3_append,
    wordR3_eq_of_code (w := wX ++ wX ++ wX) (w' := []) (by decide +kernel), wordR3_nil]

theorem wY_cube :
    wordR3 wY ^ 3 = 1 := by
  rw [pow_three', ← wordR3_append, ← wordR3_append,
    wordR3_eq_of_code (w := wY ++ wY ++ wY) (w' := []) (by decide +kernel), wordR3_nil]

theorem wX_mul_wY :
    wordR3 wX * wordR3 wY = wordR3 wY * wordR3 wX := by
  rw [← wordR3_append, ← wordR3_append]
  exact wordR3_eq_of_code (w := wX ++ wY) (w' := wY ++ wX) (by decide +kernel)

theorem wX_ne_one :
    wordR3 wX ≠ 1 :=
  wordR3_ne_one_of (w := wX) (by decide +kernel)

theorem wY_ne_one :
    wordR3 wY ≠ 1 :=
  wordR3_ne_one_of (w := wY) (by decide +kernel)

theorem wY_ne_wX :
    wordR3 wY ≠ wordR3 wX :=
  wordR3_ne_of_code (w := wY) (w' := wX) (by decide +kernel)

theorem wY_ne_wX_sq :
    wordR3 wY ≠ wordR3 wX ^ 2 := by
  rw [wordR3_sq]
  exact wordR3_ne_of_code (w := wY) (w' := wX ++ wX) (by decide +kernel)

theorem wG_mul_wX :
    wordR3 wG * wordR3 wX = wordR3 wX ^ 2 * wordR3 wG := by
  rw [wordR3_sq, ← wordR3_append, ← wordR3_append]
  exact wordR3_eq_of_code (w := wG ++ wX) (w' := wX ++ wX ++ wG) (by decide +kernel)

theorem wG_mul_wY :
    wordR3 wG * wordR3 wY = wordR3 wY * wordR3 wG := by
  rw [← wordR3_append, ← wordR3_append]
  exact wordR3_eq_of_code (w := wG ++ wY) (w' := wY ++ wG) (by decide +kernel)

theorem wH_mul_wY :
    wordR3 wH * wordR3 wY = wordR3 wY ^ 2 * wordR3 wH := by
  rw [wordR3_sq, ← wordR3_append, ← wordR3_append]
  exact wordR3_eq_of_code (w := wH ++ wY) (w' := wY ++ wY ++ wH) (by decide +kernel)

theorem wT_sq :
    wordR3 wT ^ 2 = 1 := by
  rw [wordR3_sq, wordR3_eq_of_code (w := wT ++ wT) (w' := []) (by decide +kernel), wordR3_nil]

theorem wT_ne_one :
    wordR3 wT ≠ 1 :=
  wordR3_ne_one_of (w := wT) (by decide +kernel)

theorem wT_mul_wX :
    wordR3 wT * wordR3 wX = wordR3 wX * wordR3 wT := by
  rw [← wordR3_append, ← wordR3_append]
  exact wordR3_eq_of_code (w := wT ++ wX) (w' := wX ++ wT) (by decide +kernel)

end KS12G2

open KS12G2

theorem ks12Config_R3 :
    KS12Config ↥R3 :=
  KS12Config.of_involution (x := wordR3 wX) (y := wordR3 wY) (g := wordR3 wG)
    (h := wordR3 wH) (t := wordR3 wT) wX_cube wY_cube wX_mul_wY wX_ne_one wY_ne_one
    wY_ne_wX wY_ne_wX_sq (conj_inv_of_mul_eq wX_cube wG_mul_wX)
    ((mul_inv_eq_iff_eq_mul).mpr wG_mul_wY) (conj_inv_of_mul_eq wY_cube wH_mul_wY)
    wT_ne_one wT_sq wT_mul_wX

theorem ks12Config_g2
    {Lb : Type} [Group Lb] (h : CFSG.Blueprint.ChevalleyExceptionalModel Lb .G2 3 1) :
    KS12Config Lb := by
  obtain ⟨e⟩ := CFSG.CGT.PushingUpLit.CGT6.EmbG23.exists_equiv_g23 h
  have hL : Lb ≃* ↥R3 := e.trans adjointEquivR3
  have hR : KS12Config ↥R3 := ks12Config_R3
  exact KS12Config.of_mulEquiv (Q := ↥R3) (Q' := Lb) hL.symm hR

theorem ks12CoverG2 :
    KS12CoverG2 := by
  intro X _ _ _ hZ hm
  exact ks12Concl_of_config hZ (MulEquiv.refl (X ⧸ Subgroup.center X)) (ks12Config_g2 hm)

end CFSG.RankThree.PartTwo.KFacts
