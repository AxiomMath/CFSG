module

public import Certificates.Kernel.B45.C260394R0
public import Certificates.Kernel.B45.C260394R1
public import Certificates.Kernel.B45.C260394R2
public import Certificates.Kernel.B45.C260394R3
public import Certificates.Kernel.B45.C260394R4
public import Certificates.Kernel.B45.C260394R5
public import Certificates.Kernel.B45.C260394R6
public import Certificates.Kernel.B45.C260394R7
public import Certificates.Kernel.B45.C260394R8
public import Certificates.Kernel.B45.C260394R9
public import Certificates.Kernel.B45.C260394Tab
public import CFSG.Certificates.Kernel.InvTabFSound
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option Elab.async false

#kon_join CertificateChecks.KernelB45.C260394.rootAll CertificateChecks.KernelB45.C260394.rootS 495

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.InvTabK CFSG.KC.B45P.RuSyl CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.B45Exc.Tab

theorem srch5 : forallGreedyF 495 (cK CM) (pK PR) (predC CM PR WQ (WN 0)) 5 [] = true :=
  forallGreedyF_roots fun r hr => by
    have h := rootAll r hr
    unfold rootS rootC at h
    exact h

theorem rank7 : forallGreedyF 495 (cK CM) (pK PR) (fun _ => false) 7 [] = true := by
  change forallGreedyF 495 (cK CM) (pK PR) (fun _ => false) (5 + 2) [] = true
  rw [forallGreedyF_add]
  refine forallGreedyF_mono (fun l h => ?_) 5 [] srch5
  simp only [predC, Bool.and_eq_true] at h
  exact h.2

theorem wit5 : forallGreedyF 495 (cK CM) (pK PR)
    (fun l => witC WQ (WN 0) (subprodsF 495 (pK PR) l)) 5 [] = true := by
  refine forallGreedyF_mono (fun l h => ?_) 5 [] srch5
  simp only [predC, Bool.and_eq_true] at h
  exact h.1

section Search

variable {X : ℕ → Equiv.Perm (Fin 4060)} (hT : TabSpec 495 (cK CM) (pK PR) X)
  (hcov : ∀ x ∈ ruS, x * x = 1 → (fixFinset x).card = 92 → ∃ i < 495, x = X i)
  {B : Subgroup (Equiv.Perm (Fin 4060))} (hBS : B ≤ ruS)
  (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
  (h2A : ∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92)
include hT hcov hBS hcomm hsq h2A

theorem sub_of {pred : List ℕ → Bool} {k : ℕ}
    (h : forallGreedyF 495 (cK CM) (pK PR) pred k [] = true) (hcard : Nat.card B = 2 ^ k) :
    ∃ l : List ℕ, IsChainF 495 (cK CM) l ∧ pred l = true ∧
      ∀ x, x ∈ B ↔ ∃ s ∈ subprodsF 495 (pK PR) l, x = X s :=
  forallGreedyF_sound hT h B hcomm hsq
    (fun x hx hx1 => hcov x (hBS hx) (hsq x hx) (h2A x hx hx1)) hcard

theorem card_le : Nat.card B ≤ 2 ^ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := by
    intro x
    exact ⟨1, Subtype.ext (by simpa [pow_one, sq] using hsq x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  by_contra hlt
  push Not at hlt
  have hk7 : 7 ≤ k := by
    by_contra h7
    push Not at h7
    have : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 7) (G := ↥B)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 hk7)
  set B' : Subgroup (Equiv.Perm (Fin 4060)) := K.map B.subtype with hB'
  have hcard : Nat.card B' = 2 ^ 7 := by
    rw [hB', Subgroup.card_map_of_injective (Subgroup.subtype_injective B), hK]
  have hB'B : ∀ x ∈ B', x ∈ B := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  obtain ⟨l, -, hl, -⟩ := sub_of hT hcov (B := B') (fun x hx => hBS (hB'B x hx))
    (fun x hx y hy => hcomm x (hB'B x hx) y (hB'B y hy)) (fun x hx => hsq x (hB'B x hx))
    (fun x hx hx1 => h2A x (hB'B x hx) hx1) rank7 hcard
  exact absurd hl (by decide)

theorem wit_mem (hcard : Nat.card B = 2 ^ 5) :
    ∃ k < WN 0, ∀ t < 4, X (quadC WQ k t) ∈ B := by
  obtain ⟨l, -, hl, hmem⟩ := sub_of hT hcov hBS hcomm hsq h2A wit5 hcard
  simp only [witC, List.any_eq_true, List.mem_range, List.all_eq_true, List.contains_iff_mem]
    at hl
  obtain ⟨k, hk, hks⟩ := hl
  exact ⟨k, hk, fun t ht => (hmem _).2 ⟨_, hks t ht, rfl⟩⟩

end Search


theorem tabSpec : ∃ X : ℕ → Equiv.Perm (Fin 4060), (∀ i, X i ∈ ruS) ∧
    (∀ i < 495, X i * X i = 1 ∧ X i ≠ 1) ∧ TabSpec 495 (cK CM) (pK PR) X ∧
    ∀ x ∈ ruS, x * x = 1 → (fixFinset x).card = 92 → ∃ i < 495, x = X i := by
  obtain ⟨X, hmem, hone, hinv, hinj, hcomm, hprod, hcov⟩ := ru2A_table
  exact ⟨X, hmem, hinv, ⟨hone, hinj, hcomm, hprod⟩, hcov⟩

theorem ru2A_search : ∃ X : ℕ → Equiv.Perm (Fin 4060), (∀ i, X i ∈ ruS) ∧
    (∀ i < 495, X i * X i = 1 ∧ X i ≠ 1) ∧ TabSpec 495 (cK CM) (pK PR) X ∧
    ∀ B : Subgroup (Equiv.Perm (Fin 4060)), B ≤ ruS → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → (∀ x ∈ B, x ≠ 1 → (fixFinset x).card = 92) →
      Nat.card B ≤ 2 ^ 6 ∧ (Nat.card B = 2 ^ 5 → ∃ k < WN 0, ∀ t < 4, X (quadC WQ k t) ∈ B) := by
  obtain ⟨X, hmem, hinv, hT, hcov⟩ := tabSpec
  exact ⟨X, hmem, hinv, hT, fun B hBS hcomm hsq h2A =>
    ⟨card_le hT hcov hBS hcomm hsq h2A, wit_mem hT hcov hBS hcomm hsq h2A⟩⟩

end CertificateChecks.KernelB45.C260394

end
