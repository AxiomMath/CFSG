module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardUT

import CFSG.GroupTheory.ConjTransport
import CFSG.RankThree.GF2n.Parrott.SpinForms

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open scoped Matrix

theorem v_eq_x45_mul_f45 : v = x45 * f45 := by
  decide +kernel

theorem y45_pow_five : y45 ^ 5 = 1 := by
  decide +kernel

theorem y45_ne_one : y45 ≠ 1 := by
  decide +kernel

theorem fixCard_matWord_uWord_mul_Mx_mul_Mf :
    fixCard (matWord (toSpinWord uWord) * Mx * Mf) = 16 := by
  decide +kernel

theorem fixCard_My : fixCard My = 1 := by
  decide +kernel

theorem fixCard_My_sq : fixCard (My * My) = 1 := by
  decide +kernel

theorem fixCard_My_cube : fixCard (My * My * My) = 1 := by
  decide +kernel

theorem fixCard_My_fourth : fixCard (My * My * My * My) = 1 := by
  decide +kernel

namespace SpinFaithful

private def letterPerm : ℕ → Equiv.Perm (Fin 45)
  | 0 => x45
  | 1 => y45
  | _ => f45

private def letterMat : ℕ → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | 0 => Mx
  | 1 => My
  | _ => Mf

private def permOfWord (w : List ℕ) : Equiv.Perm (Fin 45) := (w.map letterPerm).prod

private def matOfWord (w : List ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) := (w.map letterMat).prod

private def genWord : Bool → List ℕ
  | false => [0]
  | true => [2, 1, 1, 1, 2, 1, 1, 2, 1]

private def genMat (b : Bool) : Matrix (Fin 8) (Fin 8) (ZMod 2) := matOfWord (genWord b)

private theorem uv_mul_self : (u * v) * (u * v) = 1 := by
  decide +kernel

private theorem uv_ne_one : u * v ≠ 1 := by
  decide +kernel

private theorem genWord_commute (b : Bool) :
    (u * v) * permOfWord (genWord b) = permOfWord (genWord b) * (u * v) := by
  cases b <;> decide +kernel

private def conjWords : List (List ℕ) :=
  [ [], [1], [1, 1], [2, 1], [0, 1, 1], [1, 1, 1], [2, 1, 1], [1, 2, 1], [1, 0, 1, 1], [2, 0, 1, 1],
    [0, 1, 1, 1], [1, 1, 1, 1], [2, 1, 1, 1], [1, 2, 1, 1], [0, 1, 2, 1], [2, 1, 2, 1],
    [1, 1, 0, 1, 1], [2, 1, 0, 1, 1], [1, 2, 0, 1, 1], [2, 0, 1, 1, 1], [2, 1, 1, 1, 1],
    [1, 2, 1, 1, 1], [1, 1, 2, 1, 1], [2, 1, 2, 1, 1], [1, 0, 1, 2, 1], [2, 0, 1, 2, 1],
    [2, 1, 1, 0, 1, 1], [1, 1, 2, 0, 1, 1], [2, 1, 2, 0, 1, 1], [1, 2, 0, 1, 1, 1],
    [1, 2, 1, 1, 1, 1], [0, 1, 2, 1, 1, 1], [1, 1, 2, 1, 1, 1], [0, 1, 1, 2, 1, 1],
    [2, 1, 1, 2, 1, 1], [1, 1, 1, 2, 0, 1, 1]]

private def conjKey (w : List ℕ) : List ℕ :=
  List.ofFn fun i : Fin 45 => ((permOfWord w * (u * v) * (permOfWord w)⁻¹) i : ℕ)

private theorem conjKey_nodup : (conjWords.map conjKey).Nodup := by
  decide +kernel

private theorem conjWords_length : conjWords.length = 36 := by
  decide +kernel

private def fVec (m : ℕ) : V := fun i => (((m >>> (i : ℕ)) % 2 : ℕ) : ZMod 2)

private def fBasis : List ℕ := [12, 22, 64, 134]

private theorem bitmask_fVec : ∀ m ∈ fBasis, bitmask (fVec m) = m := by
  decide +kernel

private theorem bitmask_lt : ∀ x : V, bitmask x < 256 := by
  decide +kernel

private theorem fBasis_singular : ∀ m ∈ fBasis, q (fVec m) = 0 := by
  decide +kernel

private theorem fBasis_fixed :
    ∀ m ∈ fBasis, bitRow (matWord (toSpinWord uWord) * Mx * Mf) m = m := by
  decide +kernel

private def stepChunks : Bool → List ℕ
  | false =>
    [ 0x1b1e03061f1a0702090c11140d0815100b0e13160f0a1712191c01041d180500,
      0x3f3a27223b3e23262d283530292c31342f2a37322b2e33363d382520393c2124,
      0x5b5e43465f5a4742494c51544d4855504b4e53564f4a5752595c41445d584540,
      0x7f7a67627b7e63666d687570696c71746f6a77726b6e73767d786560797c6164,
      0x9b9e83869f9a8782898c91948d8895908b8e93968f8a9792999c81849d988580,
      0xbfbaa7a2bbbea3a6ada8b5b0a9acb1b4afaab7b2abaeb3b6bdb8a5a0b9bca1a4,
      0xdbdec3c6dfdac7c2c9ccd1d4cdc8d5d0cbced3d6cfcad7d2d9dcc1c4ddd8c5c0,
      0xfffae7e2fbfee3e6ede8f5f0e9ecf1f4efeaf7f2ebeef3f6fdf8e5e0f9fce1e4]
  | true =>
    [ 0x942e3288269c803a3c869a208e34289206bca01ab40e12a8ae1408b21ca6ba00,
      0x2f9589339d273b81873d219b358f9329bd071ba10fb5a91315afb309a71d01bb,
      0xce7468d27cc6da6066dcc07ad46e72c85ce6fa40ee5448f2f44e52e846fce05a,
      0x75cfd369c77d61dbdd677bc16fd5c973e75d41fb55eff3494ff5e953fd475be1,
      0x4af0ec56f8425ee4e25844fe50eaf64cd8627ec46ad0cc7670cad66cc27864de,
      0xf14b57ed43f9e55f59e3ff45eb514df763d9c57fd16b77cdcb716dd779c3df65,
      0x10aab60ca21804beb8021ea40ab0ac168238249e308a962c2a908c3698223e84,
      0xab110db719a3bf0503b9a51fb10b17ad39839f258b312d97912b378d2399853f]

private def step (b : Bool) (m : ℕ) : ℕ :=
  ((stepChunks b).getD (m / 32) 0 >>> (8 * (m % 32))) % 256

private theorem step_spec : ∀ b : Bool, ∀ m ∈ List.range 256, step b m = bitRow (genMat b) m := by
  decide +kernel

private def decode : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, c => if c ≤ 1 then [] else (c % 2 == 1) :: decode n (c / 2)

private def wordImage (w : List Bool) (m : ℕ) : ℕ := w.foldr step m

private def key (c : ℕ) : ℕ :=
  (fBasis.map (wordImage (decode 20 c))).foldr (fun m acc => m + 256 * acc) 0

private def codes : List ℕ :=
  [ 214, 1495, 118, 731, 110, 218, 122, 62, 1975, 23, 1783, 426, 234, 685, 1911, 1451, 693, 349,
    3005, 107, 2990, 3963, 59, 1462, 55, 109, 61, 31, 213, 117, 1370, 3003, 46, 3566, 2902, 1386,
    698, 3822, 699, 2903, 1387, 1398, 2774, 2742, 938, 47, 1371, 469, 94, 474, 858, 237, 429, 490,
    250, 874, 442, 2926, 245, 125, 437, 221, 1463, 4026, 366, 1517, 2747, 1909, 3805, 1493, 2986,
    3933, 2013, 3034, 183, 3549, 2779, 1391, 1973, 21, 1403, 726, 363, 3765, 3946, 42, 2782, 2806,
    4013, 758, 3758, 3502, 1774, 91, 1006, 1966, 687, 2006, 3926, 3542, 10, 986, 701, 695, 1389,
    181, 2733, 1367, 1882, 2923, 3438, 746, 1902, 1373, 954, 379, 1879, 1751, 887, 182, 503, 983,
    1374, 1003, 1963, 1771, 5, 493, 445, 1390, 877, 1709, 2734, 941, 3435, 1899, 362, 861, 477,
    1719, 373, 951, 85, 170, 734, 2987, 367, 4027, 2906, 1454, 1453, 727, 86, 3947, 43, 1466, 3035,
    733, 3819, 1750, 502, 982, 886, 2798, 1, 123, 111, 2925, 219, 93, 1718, 950, 1002, 1962, 1397,
    2773, 119, 215, 378, 1878, 2741, 235, 1898, 427, 1725, 4011, 957, 1515, 3029, 3030, 4021, 749,
    375, 1498, 750, 989, 13, 1757, 879, 495, 7, 4022, 3547, 2011, 3931, 3421, 1711, 1885, 3422, 943,
    1886, 1978, 26, 3514, 1758, 14, 990, 3565, 3949, 45, 90, 175, 350, 347, 694, 2939, 2989, 686,
    3037, 343, 2922, 1461, 683, 1366, 875, 251, 491, 443, 1399, 2, 246, 222, 438, 186, 475, 859,
    238, 2797, 430, 501, 981, 885, 1749, 1717, 470, 949, 854, 939, 189, 3806, 1494, 1518, 171, 1469,
    4014, 173, 1450, 87, 3934, 341, 730, 3550, 2933, 1467, 2909, 2907, 1455, 3510, 1782, 1974, 22,
    3437, 1901, 374, 187, 2795, 862, 478, 2005, 239, 4010, 431, 439, 878, 3, 247, 6, 494, 1965,
    1005, 3501, 1773, 471, 1710, 855, 942, 3797, 757, 1514, 3930, 2010, 3546, 3957, 53, 1981, 29,
    3517, 106, 3773, 58, 3771, 3451, 3830, 1915, 30, 15, 3515, 54, 1979, 27, 1501, 2997, 1499, 751,
    3002, 2998, 1502, 1903, 747, 759, 342, 2749, 3927, 2007, 346, 174, 725, 1723, 955, 1967, 682,
    365, 1775, 2781, 1755, 891, 987, 11, 3419, 1883, 2910]

private theorem key_chain : List.IsChain (· < ·) (codes.map key) := by
  decide +kernel

private theorem codes_length : codes.length = 361 := by
  decide +kernel

private theorem step_bitmask (b : Bool) (x : V) :
    step b (bitmask x) = bitmask (genMat b *ᵥ x) := by
  rw [step_spec b (bitmask x) (List.mem_range.2 (bitmask_lt x)), bitRow_bitmask]

private theorem wordImage_bitmask (w : List Bool) (x : V) :
    wordImage w (bitmask x) = bitmask (((w.map genMat).prod) *ᵥ x) := by
  induction w with
  | nil => simp [wordImage, Matrix.one_mulVec]
  | cons b w ih =>
    have h : wordImage (b :: w) (bitmask x) = step b (wordImage w (bitmask x)) := rfl
    rw [h, ih, step_bitmask, List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

end SpinFaithful


theorem rhoA_u_mul_v :
    rhoA ((⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩) =
      evalW MxUnit MyUnit uWord * MxUnit * MfUnit := by
  have hu : (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) =
      evalW (⟨x45, Q45_le_A45 x45_mem_Q⟩ : ↥QA45.originalSubgroup) ⟨y45, Q45_le_A45 y45_mem_Q⟩
        uWord := by
    apply Subtype.ext
    have h2 := map_evalW (QA45.originalSubgroup).subtype
      (⟨x45, Q45_le_A45 x45_mem_Q⟩ : ↥QA45.originalSubgroup) ⟨y45, Q45_le_A45 y45_mem_Q⟩ uWord
    exact u_eq_evalW_uWord.trans h2.symm
  have hv : (⟨v, v_mem_A⟩ : ↥QA45.originalSubgroup) =
      ⟨x45, Q45_le_A45 x45_mem_Q⟩ * ⟨f45, f45_mem_A⟩ := Subtype.ext v_eq_x45_mul_f45
  rw [hu, hv, map_mul, map_mul, map_evalW, rhoA_x, rhoA_y, rhoA_f, mul_assoc]

theorem spinFixedCard_uv (a : ↥QA45.originalSubgroup)
    (ha : IsConj a ((⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩)) :
    fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have h1 : fixCard (((rhoA ((⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩) :
      Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    rw [← hc, map_mul, map_mul, map_inv]
    exact fixCard_conj (rhoA c) (rhoA a)
  rw [← h1, rhoA_u_mul_v, Units.val_mul, Units.val_mul, coe_evalW_genUnit]
  exact fixCard_matWord_uWord_mul_Mx_mul_Mf

theorem orderOf_y45_A :
    orderOf (⟨y45, Q45_le_A45 y45_mem_Q⟩ : ↥QA45.originalSubgroup) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact y45_pow_five
  · intro h
    apply y45_ne_one
    have h' := congrArg Subtype.val h
    simpa using h'

theorem fixCard_rhoA_of_mem_zpowers_y (y : ↥QA45.originalSubgroup)
    (hy : y ∈ Subgroup.zpowers (⟨y45, Q45_le_A45 y45_mem_Q⟩ : ↥QA45.originalSubgroup))
    (hy1 : y ≠ 1) :
    fixCard (((rhoA y : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 1 := by
  have hyord := orderOf_y45_A
  rcases (CFSG.GroupTheory.mem_zpowers_five_iff hyord y).1 hy with h | h | h | h | h
  · exact absurd h hy1
  · rw [h, rhoA_y]
    exact fixCard_My
  · rw [h, map_mul, rhoA_y, Units.val_mul]
    exact fixCard_My_sq
  · rw [h, map_mul, map_mul, rhoA_y, Units.val_mul, Units.val_mul]
    exact fixCard_My_cube
  · rw [h, map_mul, map_mul, map_mul, rhoA_y, Units.val_mul, Units.val_mul, Units.val_mul]
    exact fixCard_My_fourth

theorem spinFixedCard_five (a : ↥QA45.originalSubgroup) (ha : orderOf a = 5) :
    fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hyord := orderOf_y45_A
  have hindex : ∀ B : Subgroup ↥QA45.originalSubgroup, Nat.card B = 5 → B.index = 10368 := by
    intro B hB
    have h := Subgroup.card_mul_index B
    rw [hB, card_A45] at h
    omega
  have hBa : Nat.card (Subgroup.zpowers a) = 5 := by rw [Nat.card_zpowers, ha]
  have hBy : Nat.card (Subgroup.zpowers
      (⟨y45, Q45_le_A45 y45_mem_Q⟩ : ↥QA45.originalSubgroup)) = 5 := by
    rw [Nat.card_zpowers, hyord]
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.exists_conj_of_isPGroup 5 (B := Subgroup.zpowers a)
    (B₀ := Subgroup.zpowers (⟨y45, Q45_le_A45 y45_mem_Q⟩ : ↥QA45.originalSubgroup))
    (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hBa))
    (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hBy))
    (by rw [hindex _ hBa]; norm_num) (by rw [hindex _ hBy]; norm_num)
  have hmem : a ∈ (Subgroup.zpowers
      (⟨y45, Q45_le_A45 y45_mem_Q⟩ : ↥QA45.originalSubgroup)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hg]
    exact Subgroup.mem_zpowers a
  obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.1 hmem
  have hya' : g * y * g⁻¹ = a := hya
  have hy1 : y ≠ 1 := by
    rintro rfl
    have ha1 : a = 1 := by rw [← hya']; group
    rw [ha1, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hconj : fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      fixCard (((rhoA y : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    rw [← hya', map_mul, map_mul, map_inv]
    exact fixCard_conj (rhoA g) (rhoA y)
  rw [hconj]
  exact fixCard_rhoA_of_mem_zpowers_y y hy hy1

namespace SpinFaithful

private def letterA : ℕ → ↥QA45.originalSubgroup
  | 0 => ⟨x45, Q45_le_A45 x45_mem_Q⟩
  | 1 => ⟨y45, Q45_le_A45 y45_mem_Q⟩
  | _ => ⟨f45, f45_mem_A⟩

private def wordA (w : List ℕ) : ↥QA45.originalSubgroup := (w.map letterA).prod

private theorem coe_wordA (w : List ℕ) :
    ((wordA w : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = permOfWord w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h : wordA (i :: w) = letterA i * wordA w := rfl
    rw [h, Subgroup.coe_mul, ih]
    show _ = letterPerm i * permOfWord w
    congr 1
    rcases i with _ | _ | i <;> rfl

private theorem rhoA_wordA (w : List ℕ) :
    ((rhoA (wordA w) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = matOfWord w := by
  induction w with
  | nil => simp [wordA, matOfWord]
  | cons i w ih =>
    have h : wordA (i :: w) = letterA i * wordA w := rfl
    rw [h, map_mul, Units.val_mul, ih]
    show _ = letterMat i * matOfWord w
    congr 1
    rcases i with _ | _ | i
    · exact congrArg Units.val rhoA_x
    · exact congrArg Units.val rhoA_y
    · exact congrArg Units.val rhoA_f

private def uvA : ↥QA45.originalSubgroup := ⟨u, u_mem_A⟩ * ⟨v, v_mem_A⟩

private theorem coe_uvA : ((uvA : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) = u * v := rfl

private theorem uvA_mul_self : uvA * uvA = 1 := Subtype.ext uv_mul_self

private theorem uvA_ne_one : uvA ≠ 1 := by
  intro h
  apply uv_ne_one
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_one] at h'
  exact h'

private theorem rhoA_uvA :
    ((rhoA uvA : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      matWord (toSpinWord uWord) * Mx * Mf := by
  have h : rhoA uvA = evalW MxUnit MyUnit uWord * MxUnit * MfUnit := rhoA_u_mul_v
  rw [h, Units.val_mul, Units.val_mul, coe_evalW_genUnit]
  rfl

private theorem uvA_fix_fVec : ∀ m ∈ fBasis, actA uvA (fVec m) = fVec m := by
  intro m hm
  apply bitmask_injective
  have h1 : actA uvA (fVec m) = ((rhoA uvA : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ fVec m := rfl
  rw [h1, rhoA_uvA, ← bitRow_bitmask, bitmask_fVec m hm]
  exact fBasis_fixed m hm

private def genA (b : Bool) : ↥QA45.originalSubgroup := wordA (genWord b)

private theorem genA_mem_centralizer (b : Bool) :
    genA b ∈ Subgroup.centralizer ({uvA} : Set ↥QA45.originalSubgroup) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  have hc := genWord_commute b
  rw [← coe_wordA] at hc
  exact Subtype.ext hc

private theorem rhoA_prod_genA (w : List Bool) :
    ((rhoA ((w.map genA).prod) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = (w.map genMat).prod := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Units.val_mul, ih, List.map_cons, List.prod_cons]
    exact congrArg (· * _) (rhoA_wordA (genWord b))

private theorem card_conjugatesOf_uvA : 36 ≤ (conjugatesOf uvA).ncard := by
  let l : List ↥QA45.originalSubgroup := conjWords.map fun w => wordA w * uvA * (wordA w)⁻¹
  have hkey : conjWords.map conjKey =
      l.map fun x => List.ofFn fun i : Fin 45 => (((x : ↥QA45.originalSubgroup) :
        Equiv.Perm (Fin 45)) i : ℕ) := by
    rw [List.map_map]
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp, conjKey]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_wordA, coe_uvA]
  have hnd : l.Nodup := by
    have h := conjKey_nodup
    rw [hkey] at h
    exact List.Nodup.of_map _ h
  have hsub : (l.toFinset : Set ↥QA45.originalSubgroup) ⊆ conjugatesOf uvA := by
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset, l, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    exact (isConj_iff.2 ⟨wordA w, rfl⟩ : IsConj uvA (wordA w * uvA * (wordA w)⁻¹))
  calc 36 = l.toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd, List.length_map, conjWords_length]
    _ = (l.toFinset : Set ↥QA45.originalSubgroup).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (conjugatesOf uvA).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

private theorem card_centralizer_uvA_le :
    Nat.card (Subgroup.centralizer ({uvA} : Set ↥QA45.originalSubgroup)) ≤ 1440 := by
  have h1 := Subgroup.card_mul_index
    (Subgroup.centralizer ({uvA} : Set ↥QA45.originalSubgroup))
  rw [Subgroup.index_centralizer_eq_ncard, card_A45] at h1
  have h36 := card_conjugatesOf_uvA
  nlinarith [h1, h36]

private theorem faithful_core (b : ↥QA45.originalSubgroup) (hab : uvA * b = b * uvA)
    (hb : ∀ w : V, actA uvA w = w → q w = 0 → actA b w = w) : b = 1 ∨ b = uvA := by
  by_contra hcon
  have hb1 : b ≠ 1 := fun h => hcon (Or.inl h)
  have hbu : b ≠ uvA := fun h => hcon (Or.inr h)
  set C : Subgroup ↥QA45.originalSubgroup :=
    Subgroup.centralizer ({uvA} : Set ↥QA45.originalSubgroup) with hC
  have hCle : Nat.card C ≤ 1440 := card_centralizer_uvA_le
  have hmemC : ∀ x : ↥QA45.originalSubgroup, uvA * x = x * uvA → x ∈ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hx
  have huC : uvA ∈ C := hmemC uvA rfl
  have hbC : b ∈ C := hmemC b hab
  have h01 : (1 : ↥QA45.originalSubgroup) ≠ uvA := uvA_ne_one.symm
  have h02 : (1 : ↥QA45.originalSubgroup) ≠ b := hb1.symm
  have h03 : (1 : ↥QA45.originalSubgroup) ≠ uvA * b := by
    intro h
    apply hbu
    exact mul_left_cancel (a := uvA) (by rw [← h, uvA_mul_self])
  have h12 : uvA ≠ b := hbu.symm
  have h13 : uvA ≠ uvA * b := by
    intro h
    exact hb1 (left_eq_mul.1 h)
  have h23 : b ≠ uvA * b := by
    intro h
    exact uvA_ne_one (mul_eq_right.1 h.symm)
  let Kset : Finset ↥QA45.originalSubgroup := {1, uvA, b, uvA * b}
  have hKcard : Kset.card = 4 := by
    have e1 : (1 : ↥QA45.originalSubgroup) ∉ ({uvA, b, uvA * b} : Finset _) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02, h03⟩
    have e2 : uvA ∉ ({b, uvA * b} : Finset ↥QA45.originalSubgroup) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    have e3 : b ∉ ({uvA * b} : Finset ↥QA45.originalSubgroup) := by
      simp only [Finset.mem_singleton]
      exact h23
    simp only [Kset]
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_insert_of_notMem e3, Finset.card_singleton]
  have hKmem : ∀ k ∈ Kset, k ∈ C := by
    intro k hk
    simp only [Kset, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact C.one_mem
    · exact huC
    · exact hbC
    · exact C.mul_mem huC hbC
  have hKfix : ∀ k ∈ Kset, ∀ m ∈ fBasis, actA k (fVec m) = fVec m := by
    intro k hk m hm
    simp only [Kset, Finset.mem_insert, Finset.mem_singleton] at hk
    have hu := uvA_fix_fVec m hm
    have hbf := hb (fVec m) hu (fBasis_singular m hm)
    rcases hk with rfl | rfl | rfl | rfl
    · exact actA_one _
    · exact hu
    · exact hbf
    · rw [actA_mul, hbf, hu]
  let H : ℕ → ↥QA45.originalSubgroup := fun c => ((decode 20 c).map genA).prod
  have hHmem : ∀ c, H c ∈ C := by
    intro c
    refine Subgroup.list_prod_mem C fun x hx => ?_
    obtain ⟨b', _, rfl⟩ := List.mem_map.1 hx
    exact genA_mem_centralizer b'
  have hHtab : ∀ c ∈ codes, ∀ c' ∈ codes,
      (∀ m ∈ fBasis, actA (H c) (fVec m) = actA (H c') (fVec m)) → c = c' := by
    have hnd : (codes.map key).Nodup := (List.isChain_iff_pairwise.1 key_chain).imp ne_of_lt
    intro c hc c' hc' h
    refine List.inj_on_of_nodup_map hnd hc hc' ?_
    have himg : ∀ c'' : ℕ, ∀ m ∈ fBasis, wordImage (decode 20 c'') m =
        bitmask (actA (H c'') (fVec m)) := by
      intro c'' m hm
      have h1 : actA (H c'') (fVec m) = ((rhoA (H c'') : Matrix.GeneralLinearGroup (Fin 8)
          (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ fVec m := rfl
      rw [h1, rhoA_prod_genA, ← wordImage_bitmask, bitmask_fVec m hm]
    simp only [key]
    congr 1
    refine List.map_congr_left fun m hm => ?_
    rw [himg c m hm, himg c' m hm, h m hm]
  let S : Finset (ℕ × ↥QA45.originalSubgroup) := codes.toFinset ×ˢ Kset
  let f : ℕ × ↥QA45.originalSubgroup → ↥QA45.originalSubgroup := fun p => H p.1 * p.2
  have hf_inj : Set.InjOn f (S : Set (ℕ × ↥QA45.originalSubgroup)) := by
    rintro ⟨c, k⟩ hp ⟨c', k'⟩ hp' hfp
    simp only [S, Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hp hp'
    have hfp' : H c * k = H c' * k' := hfp
    have hcc : c = c' := by
      refine hHtab c hp.1 c' hp'.1 fun m hm => ?_
      have h1 := congrArg (fun x => actA x (fVec m)) hfp'
      simp only [actA_mul] at h1
      rw [hKfix k hp.2 m hm, hKfix k' hp'.2 m hm] at h1
      exact h1
    subst hcc
    rw [mul_left_cancel hfp']
  have hsub : ∀ p ∈ (S : Set (ℕ × ↥QA45.originalSubgroup)),
      f p ∈ (C : Set ↥QA45.originalSubgroup) := by
    rintro ⟨c, k⟩ hp
    simp only [S, Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hp
    exact C.mul_mem (hHmem c) (hKmem k hp.2)
  have hScard : S.card = 361 * 4 := by
    have hcn : codes.toFinset.card = 361 := by
      rw [List.toFinset_card_of_nodup (List.Nodup.of_map key (List.isChain_iff_pairwise.1
        key_chain |>.imp ne_of_lt)), codes_length]
    simp only [S, Finset.card_product, hcn, hKcard]
  have hle := Set.ncard_le_ncard_of_injOn f hsub hf_inj (Set.toFinite _)
  rw [Set.ncard_coe_finset, hScard] at hle
  have hnc : (C : Set ↥QA45.originalSubgroup).ncard = Nat.card C := (Nat.card_coe_set_eq _).symm
  omega

end SpinFaithful

theorem spinFaithful_uv (a b : ↥QA45.originalSubgroup)
    (ha : IsConj a ((⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩))
    (hab : a * b = b * a)
    (hb : ∀ w : V, ((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w → q w = 0 →
      ((rhoA b : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ w = w) :
    b = 1 ∨ b = a := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have hc' : SpinFaithful.uvA = c * a * c⁻¹ := hc.symm
  have hab' : SpinFaithful.uvA * (c * b * c⁻¹) = (c * b * c⁻¹) * SpinFaithful.uvA := by
    rw [hc']
    calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [hab]
      _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
  have hb' : ∀ w : V, actA SpinFaithful.uvA w = w → q w = 0 → actA (c * b * c⁻¹) w = w := by
    intro w hw hqw
    have hcc : ∀ x : V, actA c (actA c⁻¹ x) = x := by
      intro x
      rw [← actA_mul, mul_inv_cancel, actA_one]
    have hcc' : ∀ x : V, actA c⁻¹ (actA c x) = x := by
      intro x
      rw [← actA_mul, inv_mul_cancel, actA_one]
    have hwa : actA a (actA c⁻¹ w) = actA c⁻¹ w := by
      have h1 : actA (c * a * c⁻¹) w = w := by rw [← hc']; exact hw
      rw [actA_mul, actA_mul] at h1
      have h2 := congrArg (actA c⁻¹) h1
      rwa [hcc'] at h2
    have hq : q (actA c⁻¹ w) = 0 := by
      rw [← hqw]
      exact spinQuad_invariant c⁻¹ w
    have hbw := hb (actA c⁻¹ w) hwa hq
    change actA b (actA c⁻¹ w) = actA c⁻¹ w at hbw
    rw [actA_mul, actA_mul, hbw, hcc]
  rcases SpinFaithful.faithful_core (c * b * c⁻¹) hab' hb' with h | h
  · left
    have h1 : b = c⁻¹ * (c * b * c⁻¹) * c := by group
    rw [h1, h]
    group
  · right
    have h2 : c * b * c⁻¹ = c * a * c⁻¹ := h.trans hc'
    have h3 := mul_right_cancel h2
    exact mul_left_cancel h3

end CFSG.RankThree.GF2n.Parrott
