module

public import CFSG.Permutation.FinPackEven6
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.Permutation.FinPack

open Equiv

#kc_repo #kc_decls CFSG.Permutation.FinPack "CFSG/Permutation/data/finpack_all6.txt" 9974 2387227443117546899

theorem pc6_mem_all : ∀ g : Perm (Fin 6), memK (pc6 g) allCodes6 = true := by
  decide +kernel

@[expose] noncomputable def pairCheck6 (g g' : ℕ → Bool) (SC T : List ℕ) : Bool :=
  allK (fun c => !g (lo6 c) || allK (fun d => !g' d || memK (mulK 6 (hi6 c) d) T) SC) allCodes6

theorem pair_of_check {P Q R : Perm (Fin 6) → Prop} {g g' : ℕ → Bool} {SC T : List ℕ}
    (hP : ∀ σ, P σ → g (enc σ) = true) (hQ : ∀ τ, Q τ → memK (enc τ) SC = true ∧ g' (enc τ) = true)
    (hR : ∀ ρ, memK (enc ρ) T = true → R ρ) (hc : pairCheck6 g g' SC T = true) :
    ∀ σ τ, P σ → Q τ → R (σ⁻¹ * τ) := by
  intro σ τ hσ hτ
  have h1 := allK_iff.1 hc _ (memK_iff.1 (pc6_mem_all σ))
  rw [lo6_pc6, hi6_pc6, hP σ hσ, Bool.not_true, Bool.false_or] at h1
  obtain ⟨hτS, hτg⟩ := hQ τ hτ
  have h2 := allK_iff.1 h1 _ (memK_iff.1 hτS)
  rw [hτg, Bool.not_true, Bool.false_or, ← enc_mul (by norm_num)] at h2
  exact hR _ h2

end CFSG.Permutation.FinPack
