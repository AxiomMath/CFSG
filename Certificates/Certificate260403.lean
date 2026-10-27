module

public import Certificates.Data.SmithB45MatM22ClsData
import Certificates.Kernel.OddSylow.M22
import CFSG.Certificates.Kernel.OddSylowClasses
import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

open CFSG.Quasithin.B45Mat.M22 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KD.OddSyl
  CFSG.KS.OddSyl CertificateChecks.KernelOddSyl.M22 CFSG.GroupTheory.SylowOddClasses

namespace CertificateChecks.Batch260403

open CFSG.Quasithin.B45Mat.M22 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KD.OddSyl
  CFSG.KS.OddSyl CertificateChecks.KernelOddSyl.M22 CFSG.GroupTheory.SylowOddClasses

abbrev s22 : List (Equiv.Perm (Fin 22)) := [m22gA, m22gB]

theorem hL : ∀ j, Img 22 (s22.getD j 1) (os22L.getD j (List.range 22))
  | 0 => by unfold Img; decide
  | 1 => by unfold Img; decide
  | j + 2 => by simpa [os22L] using img_one

theorem hLi : ∀ j, Img 22 (s22.getD j 1)⁻¹ (os22Li.getD j (List.range 22))
  | 0 => by unfold Img; decide
  | 1 => by unfold Img; decide
  | j + 2 => by simpa [os22Li] using img_one

theorem hS : ∀ w, evalCodes s22 w ∈ CFSG.Blueprint.NativeSporadic.M22 :=
  evalCodes_mem _ fun g hg => by
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m22a.2
    · exact m22b.2

def wit : ℕ → List (List ℤ × List ℤ × ℕ)
  | 3 => os22W3
  | 5 => os22W5
  | 7 => os22W7
  | 11 => os22W11
  | _ => []

def fixes : ℕ → List ℕ
  | 3 => [4]
  | 5 => [2]
  | 7 => [1]
  | 11 => [0]
  | _ => []

theorem syl : ∀ p ∈ [3, 5, 7, 11],
    sylOK 22 os22L os22Li os22Reps p (if p = 3 then 9 else p) (wit p) = true := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  exacts [os22Syl3, os22Syl5, os22Syl7, os22Syl11]

theorem card22 : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := card_M22

theorem hcard : ∀ p ∈ [3, 5, 7, 11], (if p = 3 then 9 else p) =
    p ^ (Nat.card CFSG.Blueprint.NativeSporadic.M22).factorization p := by
  intro p hp
  rw [card22]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [show 443520 = 3 ^ 2 * 49280 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl
  · rw [show 443520 = 5 ^ 1 * 88704 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl
  · rw [show 443520 = 7 ^ 1 * 63360 by norm_num, factorization_pow_mul (by norm_num) (by norm_num)]
    rfl
  · rw [show 443520 = 11 ^ 1 * 40320 by norm_num,
      factorization_pow_mul (by norm_num) (by norm_num)]
    rfl

theorem hodd : ∀ q, q.Prime → q ∣ Nat.card CFSG.Blueprint.NativeSporadic.M22 → q ≠ 2 →
    q ∈ [3, 5, 7, 11] := by
  intro q hq hd h2
  rw [card22, show 443520 = [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11].prod by norm_num] at hd
  have := mem_of_prime_dvd_prod hq (by decide) hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
  omega

theorem reps_eq : os22Reps = [os22Reps.getD 0 [], os22Reps.getD 1 [], os22Reps.getD 2 [],
    os22Reps.getD 3 [], os22Reps.getD 4 [], os22Reps.getD 5 []] := rfl

theorem hF : ∀ r ∈ os22Reps.map (evalCodes s22), fixCard r ∈ fixes (orderOf r) := by
  rw [List.forall_mem_map, reps_eq]
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep0
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep1
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep2
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep3
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep4
    rw [ho, hf]
    decide
  · obtain ⟨ho, hf⟩ := repOK_sound hL hLi (by norm_num) os22Rep5
    rw [ho, hf]
    decide

theorem reps_map : os22Reps.map (evalCodes s22) = oddReps3 ++ oddReps5 ++ oddReps7 ++ oddReps11 :=
  rfl

theorem classes : ∀ g ∈ CFSG.Blueprint.NativeSporadic.M22, Odd (orderOf g) →
    g = 1 ∨ ∃ r ∈ oddReps3 ++ oddReps5 ++ oddReps7 ++ oddReps11,
      ∃ c ∈ CFSG.Blueprint.NativeSporadic.M22, g = c * r * c⁻¹ := by
  rw [← reps_map]
  have hf := fun p (hp : p ∈ [3, 5, 7, 11]) => syl_facts hL hLi hS (syl p hp)
  refine odd_classes (fun p hp => ?_) hodd (fun p => sylElts s22 (wit p))
    (fun p hp => (hf p hp).1) (fun p hp => (hf p hp).2.1) (fun p hp => (hf p hp).2.2.1)
    (fun p hp => (hf p hp).2.2.2.1) (fun p hp => ((hf p hp).2.2.2.2.1).trans (hcard p hp))
    (fun p hp => (hf p hp).2.2.2.2.2.1) (fun p hp => (hf p hp).2.2.2.2.2.2) fixes hF
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num

theorem orders : (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps7, orderOf r = 7) ∧ (∀ r ∈ oddReps11, orderOf r = 11) := by
  have h := fun i m f (hm : Nat.Prime m) (h : repOK 22 os22L os22Li (os22Reps.getD i []) m f = true) =>
    (repOK_sound (S := s22) hL hLi hm h).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [oddReps3, List.mem_singleton] at hr
    subst hr
    exact h 0 3 4 (by norm_num) os22Rep0
  · intro r hr
    simp only [oddReps5, List.mem_singleton] at hr
    subst hr
    exact h 1 5 2 (by norm_num) os22Rep1
  · intro r hr
    simp only [oddReps7, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h 2 7 1 (by norm_num) os22Rep2
    · exact h 3 7 1 (by norm_num) os22Rep3
  · intro r hr
    simp only [oddReps11, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h 4 11 0 (by norm_num) os22Rep4
    · exact h 5 11 0 (by norm_num) os22Rep5

end CertificateChecks.Batch260403

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.B45Mat.M22 in
theorem certificate260403 :
    (∀ g ∈ CFSG.Blueprint.NativeSporadic.M22, Odd (orderOf g) →
      g = 1 ∨ ∃ r ∈ oddReps3 ++ oddReps5 ++ oddReps7 ++ oddReps11,
        ∃ c ∈ CFSG.Blueprint.NativeSporadic.M22, g = c * r * c⁻¹) ∧
    (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps7, orderOf r = 7) ∧ (∀ r ∈ oddReps11, orderOf r = 11) :=
  ⟨CertificateChecks.Batch260403.classes, CertificateChecks.Batch260403.orders⟩

end Certificates
