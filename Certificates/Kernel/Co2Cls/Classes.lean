module

public import Certificates.Kernel.Co2Cls.Checks
public import Certificates.Kernel.Co2Cls.Units
public import Certificates.Kernel.Co2Syl.Facts
public import CFSG.Certificates.Kernel.Co2Cls.Assemble
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.Certificates.Kernel.BSeed.Sound
public import Certificates.Kernel.Co2Cls.Rec5
public import Certificates.Kernel.Co2Cls.Rec6
public import Certificates.Kernel.Co2Cls.RecS

set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.Co2Cls
  CertificateChecks.KernelSpor.Co2Syl CFSG.RankThree.Co2 Subgroup

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem letter_mem {l : ℕ} (hl : l < 42) : MatP 22 (lAt LT l) ∈ genMonN 21 GC := by
  rcases Nat.lt_or_ge l 21 with h | h
  · have e := congrArg (MatP 22) (Nat.eq_of_beq_eq_true (inv l h))
    rw [MatP_mulV, MatP_IDP] at e
    obtain ⟨u, hu, hv, -⟩ := exists_unitsIn isUnit_C (genN_mem GC h)
    have hl' : MatP 22 (lAt LT l) = ((u⁻¹ : M22ˣ) : M22) := calc
      MatP 22 (lAt LT l) = MatP 22 (lAt LT l) * ((u : M22) * ((u⁻¹ : M22ˣ) : M22)) := by
        rw [Units.mul_inv, mul_one]
      _ = ((u⁻¹ : M22ˣ) : M22) := by rw [← mul_assoc, hv, e, one_mul]
    rw [hl']
    exact (unitsIn (genMonN 21 GC)).inv_mem hu
  · have e : GC (l - 21) = lAt LT l := by
      unfold GC
      congr 1
      change l - 21 + 21 = l
      omega
    rw [← e]
    exact genN_mem GC (by omega)

theorem wordK_mem : ∀ w : List ℕ, (∀ l ∈ w, l < 42) → MatP 22 (wordK w) ∈ genMonN 21 GC
  | [], _ => by
    change MatP 22 IDP ∈ _
    rw [MatP_IDP]
    exact (genMonN 21 GC).one_mem
  | l :: w, h => by
    change MatP 22 (mulV (lAt LT l) (wordK w)) ∈ _
    rw [MatP_mulV]
    exact (genMonN 21 GC).mul_mem (letter_mem (h l (by simp)))
      (wordK_mem w fun l' hl' => h l' (by simp [hl']))

theorem repMat_mem {j : ℕ} (hj : j < 10) : MatP 22 (RP j) ∈ genMonN 21 GC := by
  rw [RP_eq hj]
  exact wordK_mem _ (repWords_lt j hj)

theorem matGrp_le {ws : Array (List ℕ)} {n : ℕ} (hs : ws.size = n)
    (hw : ∀ k < n, ∀ l ∈ ws[k]!, l < 42) : matGrp ws ≤ genMonN 21 GC := by
  unfold matGrp
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  have hw' : ∀ l ∈ ws[k], l < 42 := by
    have h := hw k (by omega)
    rwa [getElem!_pos ws k hk] at h
  change wordMat ws[k] ∈ _
  rw [← MatP_wordK hw']
  exact wordK_mem _ hw'

theorem sylWords_lt : ∀ k < 5, ∀ l ∈ sylWords[k]!, l < 42 := by decide +kernel

theorem T_le : genMonN 5 HT ≤ genMonN 21 GC := by
  unfold genMonN
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  change MatP 22 (HT k) ∈ _
  rw [Nat.eq_of_beq_eq_true (gensT k hk)]
  exact wordK_mem _ (sylWords_lt k hk)

theorem two_part {ws : Array (List ℕ)} {n k i : ℕ} {cls : List ℕ} (sg : SylGrp ws (2 ^ k) cls)
    (hs : ws.size = n) (hw : ∀ k < n, ∀ l ∈ ws[k]!, l < 42) (hi : i ∈ cls) (hi10 : i < 10)
    (u : M22ˣ) (hu : (u : M22) = MatP 22 (RP i)) :
    2 ^ k ∣ Nat.card (unitsIn (genMonN 21 GC) ⊓ centralizer {u} : Subgroup M22ˣ) :=
  two_pow_dvd_sub isUnit_C (matGrp_le hs hw) sg.pow sg.card u fun x hx => by
    rw [hu, ← repMat_eq hi10]
    exact sg.comm i hi x hx

theorem conj_at {CF : ℕ → ℕ} {X0 N R k : ℕ} (hok : ∀ k < N, recC CF GC 21 X0 N k = true)
    (hm : memK CF N R k = true) : ∃ g ∈ genMonN 21 GC, g * MatP 22 X0 = MatP 22 R * g := by
  unfold memK at hm
  rw [andK_eq, Bool.and_eq_true] at hm
  rw [← Nat.eq_of_beq_eq_true hm.2]
  exact tree_conj hok k (blt_iff.1 hm.1)

theorem wlt {x : ℕ} (h : Nat.blt x (Nat.shiftLeft 1 484) = true) : x < 2 ^ 484 := by
  rw [Nat.blt_eq] at h
  change x < 1 <<< 484 at h
  rw [Nat.shiftLeft_eq, one_mul] at h
  exact h

theorem wlt' (i j : ℕ) (hi : i < 10) (hj : j < 3) :
    lAt ([[], W1, W2, W3, [], W5, W6, W7, W8, W9].getD i []) j < 2 ^ 484 :=
  wlt (witLt i hi j hj)

theorem odd_part {CF : ℕ → ℕ} {X0 N R k W p : ℕ} (hok : ∀ k < N, recC CF GC 21 X0 N k = true)
    (hm : memK CF N R k = true) (hW : W < 2 ^ 484) (hp : p.Prime) (h : oddW R W p = true)
    (hWS : MatP 22 W ∈ genMonN 21 GC) (u : M22ˣ) (hu : (u : M22) = MatP 22 X0) :
    p ∣ Nat.card (unitsIn (genMonN 21 GC) ⊓ centralizer {u} : Subgroup M22ˣ) := by
  obtain ⟨o, c⟩ := oddW_sound hW hp h
  have hy : ∃ g ∈ genMonN 21 GC, g * (u : M22) = MatP 22 R * g := by
    rw [hu]
    exact conj_at hok hm
  exact dvd_of_orderOf_mem isUnit_C hy hWS c o

theorem nine_part {CF : ℕ → ℕ} {X0 N R k U V : ℕ} (hok : ∀ k < N, recC CF GC 21 X0 N k = true)
    (hm : memK CF N R k = true) (hU : U < 2 ^ 484) (hV : V < 2 ^ 484) (h : pairW R U V = true)
    (hUS : MatP 22 U ∈ genMonN 21 GC) (hVS : MatP 22 V ∈ genMonN 21 GC) (u : M22ˣ)
    (hu : (u : M22) = MatP 22 X0) :
    9 ∣ Nat.card (unitsIn (genMonN 21 GC) ⊓ centralizer {u} : Subgroup M22ˣ) := by
  obtain ⟨o1, o2, c1, c2, c3, n1, n2⟩ := pairW_sound hU hV h
  have hy : ∃ g ∈ genMonN 21 GC, g * (u : M22) = MatP 22 R * g := by
    rw [hu]
    exact conj_at hok hm
  exact nine_dvd_mem isUnit_C hy hUS hVS c1 c2 c3 o1 o2 n1 n2

abbrev Conj (X : ℕ) : Type := {y : M22 // ∃ g ∈ genMonN 21 GC, g * MatP 22 X = y * g}

abbrev Cent (X : ℕ) : Type := {g : M22 // g ∈ genMonN 21 GC ∧ g * MatP 22 X = MatP 22 X * g}

theorem class0 : Nat.card (Conj (RP 0)) = 1 ∧ Nat.card (Cent (RP 0)) = Nat.card (genMonN 21 GC) := by
  refine class_of_central isUnit_C fun g hg => ?_
  unfold genMonN at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨j, hj⟩, rfl⟩ := hx
    exact commK_sound (cent0 j hj)
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]

variable (hC : Nat.card (genMonN 21 GC) = 743178240)
include hC

theorem class1 (hW : ∀ j < 2, MatP 22 (lAt W1 j) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 1)) = 270 ∧ Nat.card (Cent (RP 1)) = 2 ^ 17 * 21 := by
  have w := wit1
  rw [andK_eq, Bool.and_eq_true] at w
  obtain ⟨w1, w2⟩ := w
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec1) (fun u hu => ?_)
    (by norm_num [hC])
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts1.1 pWords1_size pWords1_lt (by simp) (by norm_num) u hu) ?_
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 3) (n := 7) (by norm_num)
    (odd_part rec1 at1 (wlt' 1 0 (by norm_num) (by norm_num)) Nat.prime_three w1 (hW 0 (by norm_num))
      u hu)
    (odd_part rec1 at1 (wlt' 1 1 (by norm_num) (by norm_num)) (by norm_num) w2 (hW 1 (by norm_num))
      u hu)

theorem class2 (hW : ∀ j < 2, MatP 22 (lAt W2 j) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 2)) = 1260 ∧ Nat.card (Cent (RP 2)) = 2 ^ 16 * 9 := by
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec2) (fun u hu => ?_)
    (by norm_num [hC])
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts3.1 pWords3_size pWords3_lt (by simp) (by norm_num) u hu)
    (nine_part rec2 at2 (wlt' 2 0 (by norm_num) (by norm_num)) (wlt' 2 1 (by norm_num) (by norm_num))
      wit2 (hW 0 (by norm_num)) (hW 1 (by norm_num)) u hu)

theorem class3 (hW : ∀ j < 2, MatP 22 (lAt W3 j) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 3)) = 1260 ∧ Nat.card (Cent (RP 3)) = 2 ^ 16 * 9 := by
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec3) (fun u hu => ?_)
    (by norm_num [hC])
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts3.1 pWords3_size pWords3_lt (by simp) (by norm_num) u hu)
    (nine_part rec3 at3 (wlt' 3 0 (by norm_num) (by norm_num)) (wlt' 3 1 (by norm_num) (by norm_num))
      wit3 (hW 0 (by norm_num)) (hW 1 (by norm_num)) u hu)

theorem class4 : Nat.card (Conj (RP 4)) = 22680 ∧ Nat.card (Cent (RP 4)) = 2 ^ 15 :=
  class_of isUnit_C (repMat_mem (by norm_num)) (tree_card recs4)
    (fun u hu => two_part facts4.1 pWords4_size pWords4_lt (by simp) (by norm_num) u hu)
    (by norm_num [hC])

theorem class5 (hW : MatP 22 (lAt W5 0) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 5)) = 15120 ∧ Nat.card (Cent (RP 5)) = 2 ^ 14 * 3 := by
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec5) (fun u hu => ?_)
    (by norm_num [hC])
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts5.1 pWords5_size pWords5_lt (by simp) (by norm_num) u hu)
    (odd_part rec5 at5 (wlt' 5 0 (by norm_num) (by norm_num)) Nat.prime_three wit5 hW u hu)

theorem class6 (hW : MatP 22 (lAt W6 0) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 6)) = 15120 ∧ Nat.card (Cent (RP 6)) = 2 ^ 14 * 3 := by
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec6) (fun u hu => ?_)
    (by norm_num [hC])
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts5.1 pWords5_size pWords5_lt (by simp) (by norm_num) u hu)
    (odd_part rec6 at6 (wlt' 6 0 (by norm_num) (by norm_num)) Nat.prime_three wit6 hW u hu)

theorem class7 (hW : ∀ j < 3, MatP 22 (lAt W7 j) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 7)) = 1008 ∧ Nat.card (Cent (RP 7)) = 2 ^ 14 * 45 := by
  have w := wit7
  rw [andK_eq, Bool.and_eq_true] at w
  obtain ⟨w1, w2⟩ := w
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec7) (fun u hu => ?_)
    (by norm_num [hC])
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts8.1 pWords8_size pWords8_lt (by simp) (by norm_num) u hu) ?_
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 9) (n := 5) (by norm_num)
    (nine_part rec7 at7 (wlt' 7 0 (by norm_num) (by norm_num)) (wlt' 7 1 (by norm_num) (by norm_num))
      w1 (hW 0 (by norm_num)) (hW 1 (by norm_num)) u hu)
    (odd_part rec7 at7 (wlt' 7 2 (by norm_num) (by norm_num)) (by norm_num) w2 (hW 2 (by norm_num))
      u hu)

theorem class8 (hW : ∀ j < 3, MatP 22 (lAt W8 j) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 8)) = 1008 ∧ Nat.card (Cent (RP 8)) = 2 ^ 14 * 45 := by
  have w := wit8
  rw [andK_eq, Bool.and_eq_true] at w
  obtain ⟨w1, w2⟩ := w
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card rec8) (fun u hu => ?_)
    (by norm_num [hC])
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    (two_part facts8.1 pWords8_size pWords8_lt (by simp) (by norm_num) u hu) ?_
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 9) (n := 5) (by norm_num)
    (nine_part rec8 at8 (wlt' 8 0 (by norm_num) (by norm_num)) (wlt' 8 1 (by norm_num) (by norm_num))
      w1 (hW 0 (by norm_num)) (hW 1 (by norm_num)) u hu)
    (odd_part rec8 at8 (wlt' 8 2 (by norm_num) (by norm_num)) (by norm_num) w2 (hW 2 (by norm_num))
      u hu)

theorem class9 (hT : ∀ x ∈ genMonN 5 HT, x ^ 32 = 1) (hTc : 2 ^ 18 ≤ Nat.card (genMonN 5 HT))
    (hW : MatP 22 (lAt W9 0) ∈ genMonN 21 GC) :
    Nat.card (Conj (RP 9)) = 120960 ∧ Nat.card (Cent (RP 9)) = 2 ^ 11 * 3 := by
  refine class_of isUnit_C (repMat_mem (by norm_num)) (tree_card recs9) (fun u hu => ?_)
    (by norm_num [hC])
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_
    (odd_part recs9 at9 (wlt' 9 0 (by norm_num) (by norm_num)) Nat.prime_three wit9 hW u hu)
  have hy : ∃ g ∈ genMonN 21 GC, g * (u : M22) = MatP 22 (lAt O9 0) * g := by
    rw [hu]
    exact conj_at recs9 at9
  exact two_pow_dvd_orb isUnit_C T_le hT hTc hy (fun b => MatP 22 (lAt O9 b)) rfl
    (orb_sound (by norm_num) orb9) (m := 128) (by norm_num)

end CertificateChecks.KernelSpor.Co2Cls

end
