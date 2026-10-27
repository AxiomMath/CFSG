module

public import CFSG.YGroups.Y433.MarkedQuotient
public import CFSG.YGroups.Y322Central

public section

namespace CFSG.YGroups

open CFSG.Certificates.CosetEnumeration (evalWord)

theorem y322_transfer
    {p q r : ℕ} (ι : ℕ → ℕ) (hι : Relabel.PairsPreserved 3 2 2 p q r ι)
    (hspider : evalWord (fun c => yGen p q r (ι c)) (spiderWord 3 2) ^ 10 = 1) :
    evalWord (fun c => yGen p q r (ι c)) y322WordF1 =
        evalWord (fun c => yGen p q r (ι c)) y322WordF2 ∧
      evalWord (fun c => yGen p q r (ι c)) y322WordF1 *
        evalWord (fun c => yGen p q r (ι c)) y322WordF1 = 1 ∧
      ∀ d, d < 8 → yGen p q r (ι d) * evalWord (fun c => yGen p q r (ι c)) y322WordF1 =
        evalWord (fun c => yGen p q r (ι c)) y322WordF1 * yGen p q r (ι d) := by
  have hF1 : Relabel.hom ι hι (fun _ _ _ => hspider) y322F1 =
      evalWord (fun c => yGen p q r (ι c)) y322WordF1 :=
    Relabel.hom_evalWord _ (by decide)
  have hF2 : Relabel.hom ι hι (fun _ _ _ => hspider) y322F2 =
      evalWord (fun c => yGen p q r (ι c)) y322WordF2 :=
    Relabel.hom_evalWord _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hF1, ← hF2, y322F1_eq_F2]
  · rw [← hF1, ← map_mul, y322F1_mul_self, map_one]
  · intro d hd
    rw [← hF1, ← Relabel.hom_yGen (hm := hι) (hspider := fun _ _ _ => hspider) hd,
      ← map_mul, ← map_mul, y322F1_comm_yGen hd]

namespace U433

@[expose] def sub231 (c : ℕ) : ℕ := [0, 5, 6, 7, 8, 9, 1, 2].getD c 0

@[expose] def sub312 (c : ℕ) : ℕ := [0, 8, 9, 10, 1, 2, 5, 6].getD c 0

theorem pairsPreserved_sub231 : Relabel.PairsPreserved 3 2 2 4 3 3 sub231 := by decide

theorem pairsPreserved_sub312 : Relabel.PairsPreserved 3 2 2 4 3 3 sub312 := by decide

theorem spider_sub231 :
    evalWord (fun c => yGen 4 3 3 (sub231 c)) (spiderWord 3 2) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 3 3 (sub231 c)) (spiderWord 3 2) = T 2 * T 3 * T 1 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact Relabel.pow_eq_one_rotate spider

theorem spider_sub312 :
    evalWord (fun c => yGen 4 3 3 (sub312 c)) (spiderWord 3 2) ^ 10 = 1 := by
  have e : evalWord (fun c => yGen 4 3 3 (sub312 c)) (spiderWord 3 2) = T 3 * T 1 * T 2 := by
    rw [Relabel.evalWord_spiderWord]
    rfl
  rw [e]
  exact Relabel.pow_eq_one_rotate (Relabel.pow_eq_one_rotate spider)

theorem evalWord_sub231_F1 :
    evalWord (fun c => yGen 4 3 3 (sub231 c)) y322WordF1 = F433 2 3 1 := by
  rw [y322WordF1, Y443.evalWord_replicate_flatten, F433]
  congr 1

theorem evalWord_sub231_F2 :
    evalWord (fun c => yGen 4 3 3 (sub231 c)) y322WordF2 = F433 2 1 3 := by
  rw [y322WordF2, Y443.evalWord_replicate_flatten, F433]
  congr 1

theorem evalWord_sub312_F1 :
    evalWord (fun c => yGen 4 3 3 (sub312 c)) y322WordF1 = F433 3 1 2 := by
  rw [y322WordF1, Y443.evalWord_replicate_flatten, F433]
  congr 1

theorem evalWord_sub312_F2 :
    evalWord (fun c => yGen 4 3 3 (sub312 c)) y322WordF2 = F433 3 2 1 := by
  rw [y322WordF2, Y443.evalWord_replicate_flatten, F433]
  congr 1

end U433

theorem F433_231_eq_213 :
    F433 2 3 1 = F433 2 1 3 := by
  have h := (y322_transfer U433.sub231 U433.pairsPreserved_sub231 U433.spider_sub231).1
  rwa [U433.evalWord_sub231_F1, U433.evalWord_sub231_F2] at h

theorem F433_321_eq_312 :
    F433 3 2 1 = F433 3 1 2 := by
  have h := (y322_transfer U433.sub312 U433.pairsPreserved_sub312 U433.spider_sub312).1
  rw [U433.evalWord_sub312_F1, U433.evalWord_sub312_F2] at h
  exact h.symm

theorem F433_231_mul_self :
    F433 2 3 1 * F433 2 3 1 = 1 := by
  have h := (y322_transfer U433.sub231 U433.pairsPreserved_sub231 U433.spider_sub231).2.1
  rwa [U433.evalWord_sub231_F1] at h

theorem F433_312_mul_self :
    F433 3 1 2 * F433 3 1 2 = 1 := by
  have h := (y322_transfer U433.sub312 U433.pairsPreserved_sub312 U433.spider_sub312).2.1
  rwa [U433.evalWord_sub312_F1] at h

theorem F433_231_comm_sub231
    {c : ℕ} (hc : c < 8) :
    yGen 4 3 3 (U433.sub231 c) * F433 2 3 1 = F433 2 3 1 * yGen 4 3 3 (U433.sub231 c) := by
  have h := (y322_transfer U433.sub231 U433.pairsPreserved_sub231 U433.spider_sub231).2.2 c hc
  rwa [U433.evalWord_sub231_F1] at h

theorem F433_312_comm_sub312
    {c : ℕ} (hc : c < 8) :
    yGen 4 3 3 (U433.sub312 c) * F433 3 1 2 = F433 3 1 2 * yGen 4 3 3 (U433.sub312 c) := by
  have h := (y322_transfer U433.sub312 U433.pairsPreserved_sub312 U433.spider_sub312).2.2 c hc
  rwa [U433.evalWord_sub312_F1] at h

end CFSG.YGroups
