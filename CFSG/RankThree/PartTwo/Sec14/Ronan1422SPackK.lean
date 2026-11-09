module

public import CFSG.Permutation.FinPackDec

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422SPackK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

@[expose] def VL : List ℕ :=
  [5517840, 3490320, 4411920, 5517345, 3489825, 4411425, 5517570, 3490050, 4411650]

@[expose] noncomputable def conjK (c x : ℕ) : ℕ := mulK 6 (mulK 6 c x) (invCK 6 c)

theorem conjK_enc (σ τ : Perm (Fin 6)) : conjK (enc σ) (enc τ) = enc (σ * τ * σ⁻¹) := by
  rw [conjK, invCK_enc (by norm_num), mulK_enc (by norm_num), mulK_enc (by norm_num)]

@[expose] noncomputable def normQ (c : ℕ) : Bool :=
  !allK (fun x => memK (conjK c x) VL) VL ||
    allK (fun x => Nat.beq (conjK (powK 6 5517840 c 4) x) x) VL

theorem normQ_walk : walkK 6 normQ 6 0 0 0 = true := by decide +kernel

theorem enc_one6 : enc (1 : Perm (Fin 6)) = 5517840 := by decide +kernel

theorem pow_four_centralizes {L : List (Perm (Fin 6))} (hL : L.map enc = VL) (σ : Perm (Fin 6))
    (hσ : ∀ x ∈ L, σ * x * σ⁻¹ ∈ L) : ∀ x ∈ L, σ ^ 4 * x * (σ ^ 4)⁻¹ = x := by
  have h := walkK_sound normQ_walk σ
  have h1 : allK (fun x => memK (conjK (enc σ) x) VL) VL = true := by
    rw [allK_iff]
    intro x hx
    rw [← hL, List.mem_map] at hx
    obtain ⟨τ, hτ, rfl⟩ := hx
    rw [conjK_enc, memK_iff, ← hL]
    exact List.mem_map_of_mem (hσ τ hτ)
  rw [normQ, h1, Bool.not_true, Bool.false_or, allK_iff] at h
  intro x hx
  have h2 := h (enc x) (by rw [← hL]; exact List.mem_map_of_mem hx)
  rw [← enc_one6, powK_enc (by norm_num), conjK_enc] at h2
  exact (beq_enc_iff (by norm_num)).1 h2

end CFSG.RankThree.PartTwo.Sec14.Ronan1422SPackK
