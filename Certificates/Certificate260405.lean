module

public import Certificates.Data.SmithB45MatM12ClsData
import Certificates.Kernel.OddSylow.M12
import CFSG.Certificates.Kernel.OddSylowClasses
import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

open CFSG.Quasithin.B45Mat.M12 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KD.OddSyl
  CFSG.KS.OddSyl CertificateChecks.KernelOddSyl.M12 CFSG.GroupTheory.SylowOddClasses

namespace CertificateChecks.Batch260405

open CFSG.Quasithin.B45Mat.M12 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KD.OddSyl
  CFSG.KS.OddSyl CertificateChecks.KernelOddSyl.M12 CFSG.GroupTheory.SylowOddClasses

abbrev s12 : List (Equiv.Perm (Fin 12)) := [m12gA, m12gB]

theorem hL : ∀ j, Img 12 (s12.getD j 1) (os12L.getD j (List.range 12))
  | 0 => by unfold Img; decide
  | 1 => by unfold Img; decide
  | j + 2 => by simpa [os12L] using img_one

theorem hLi : ∀ j, Img 12 (s12.getD j 1)⁻¹ (os12Li.getD j (List.range 12))
  | 0 => by unfold Img; decide
  | 1 => by unfold Img; decide
  | j + 2 => by simpa [os12Li] using img_one

theorem hS : ∀ w, evalCodes s12 w ∈ CFSG.Blueprint.NativeSporadic.M12 :=
  evalCodes_mem _ fun g hg => by
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m12a.2
    · exact m12b.2

def wit : ℕ → List (List ℤ × List ℤ × ℕ)
  | 3 => os12W3
  | 5 => os12W5
  | 11 => os12W11
  | _ => []

def fixes : ℕ → List ℕ
  | 3 => [3, 0]
  | 5 => [2]
  | 11 => [1]
  | _ => []

theorem syl : ∀ p ∈ [3, 5, 11],
    sylOK 12 os12L os12Li os12Reps p (if p = 3 then 27 else p) (wit p) = true := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [os12Syl3, os12Syl5, os12Syl11]

theorem card12 : Nat.card CFSG.Blueprint.NativeSporadic.M12 = 95040 := card_M12

theorem hcard : ∀ p ∈ [3, 5, 11], (if p = 3 then 27 else p) =
    p ^ (Nat.card CFSG.Blueprint.NativeSporadic.M12).factorization p := by
  intro p hp
  rw [card12]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · rw [show 95040 = 3 ^ 3 * 3520 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl
  · rw [show 95040 = 5 ^ 1 * 19008 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl
  · rw [show 95040 = 11 ^ 1 * 8640 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl

theorem hodd : ∀ q, q.Prime → q ∣ Nat.card CFSG.Blueprint.NativeSporadic.M12 → q ≠ 2 →
    q ∈ [3, 5, 11] := by
  intro q hq hd h2
  rw [card12, show 95040 = [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 11].prod by norm_num] at hd
  have := mem_of_prime_dvd_prod hq (by decide) hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  omega

theorem reps_eq : os12Reps = [os12Reps.getD 0 [], os12Reps.getD 1 [], os12Reps.getD 2 [],
    os12Reps.getD 3 [], os12Reps.getD 4 []] := rfl

theorem hF : ∀ r ∈ os12Reps.map (evalCodes s12), fixCard r ∈ fixes (orderOf r) := by
  rw [List.forall_mem_map, reps_eq]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os12Rep0
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os12Rep1
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os12Rep2
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os12Rep3
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os12Rep4
    rw [ho, hf]
    decide

theorem reps_map : os12Reps.map (evalCodes s12) = oddReps3 ++ oddReps5 ++ oddReps11 :=
  rfl

theorem classes : ∀ g ∈ CFSG.Blueprint.NativeSporadic.M12, Odd (orderOf g) →
    g = 1 ∨ ∃ r ∈ oddReps3 ++ oddReps5 ++ oddReps11,
      ∃ c ∈ CFSG.Blueprint.NativeSporadic.M12, g = c * r * c⁻¹ := by
  rw [← reps_map]
  have hf := fun p (hp : p ∈ [3, 5, 11]) => syl_facts hL hLi hS (syl p hp)
  refine odd_classes (fun p hp => ?_) hodd (fun p => sylElts s12 (wit p))
    (fun p hp => (hf p hp).1) (fun p hp => (hf p hp).2.1) (fun p hp => (hf p hp).2.2.1)
    (fun p hp => (hf p hp).2.2.2.1) (fun p hp => ((hf p hp).2.2.2.2.1).trans (hcard p hp))
    (fun p hp => (hf p hp).2.2.2.2.2.1) (fun p hp => (hf p hp).2.2.2.2.2.2) fixes hF
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem orders : (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps11, orderOf r = 11) := by
  have h := fun i m f (hm : Nat.Prime m)
      (h : repOK 12 os12L os12Li (os12Reps.getD i []) m f = true) =>
    (repOK_sound (S := s12) hL hLi hm h).1
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [oddReps3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h 0 3 3 (by norm_num) os12Rep0
    · exact h 1 3 0 (by norm_num) os12Rep1
  · intro r hr
    simp only [oddReps5, List.mem_singleton] at hr
    subst hr
    exact h 2 5 2 (by norm_num) os12Rep2
  · intro r hr
    simp only [oddReps11, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h 3 11 1 (by norm_num) os12Rep3
    · exact h 4 11 1 (by norm_num) os12Rep4

end CertificateChecks.Batch260405

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Mat.M12 in
theorem certificate260405 :
    (∀ g ∈ CFSG.Blueprint.NativeSporadic.M12, Odd (orderOf g) →
      g = 1 ∨ ∃ r ∈ oddReps3 ++ oddReps5 ++ oddReps11,
        ∃ c ∈ CFSG.Blueprint.NativeSporadic.M12, g = c * r * c⁻¹) ∧
    (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps11, orderOf r = 11) :=
  ⟨CertificateChecks.Batch260405.classes, CertificateChecks.Batch260405.orders⟩

end Certificates
