module

public import Certificates.Data.SmithL6Tr
public import CFSG.GF2Type.SmithTypeE.LMod.Tv
import Certificates.Kernel.SmithL6K.GlueC

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod Matrix

@[expose] def trRep (k : ℕ) : ℕ × ℕ := [(0, 1), (0, 10), (0, 84), (4, 0), (4, 7)].getD k (0, 0)

@[expose] def trRepT (k : ℕ) : Array ℕ := trCandT (trLift (trRep k).1) (trRep k).2

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod Matrix in
theorem certificate38681 :
    (∀ j < 5, ∀ a < 512, (∀ x < 1953, (trCandT (trLift j) a)[(trCandT (trLift j) a)[x]!]! = x) →
      (∃ x < 1953, (trCandT (trLift j) a)[x]! ≠ x) →
      ∃ k < 5, ∃ G H : Matrix (Fin 6) (Fin 6) (ZMod 2), Hᵀ * G = 1 ∧
        ∀ x < 1953, ∀ y < 1953, tvVec y = G *ᵥ tvVec x → tvForm y = H *ᵥ tvForm x →
          tvVec (trRepT k)[y]! = G *ᵥ tvVec (trCandT (trLift j) a)[x]! ∧
            tvForm (trRepT k)[y]! = H *ᵥ tvForm (trCandT (trLift j) a)[x]!) ∧
    (∀ k < 5, ∃ P : List (ℕ × ℕ), P.length = 6 ∧
      (∀ p ∈ P, p.1 < 1395 ∧ p.2 < 1395 ∧
        ∀ x < 1953, inPlane p.1 x = true → inPlane p.2 (trRepT k)[x]! = true) ∧
      (∀ m, 0 < m → m < 64 → trXorSel (P.map fun p => wt p.2 ^^^ wt p.1) m ≠ 0) ∧
      ((∃ i i', i < 1395 ∧ i' < 1395 ∧
          (∀ x < 1953, inPlane i x = true → inPlane i' (trRepT k)[x]! = true) ∧
          fB (wt i') (wt i) = true) ∨
        (∃ i < 1395, ∀ x < 1953, inPlane i x = true → (trRepT k)[x]! = x) ∨ k = 3)) ∧
    (∃ bs : List ℕ, bs.length ≤ 8 ∧ ∃ pl : List (ℕ × ℕ),
      (∀ q ∈ pl, q.1 < 1395 ∧ q.2 < 1395 ∧
        (∀ x < 1953, inPlane q.1 x = true → inPlane q.2 (trRepT 3)[x]! = true) ∧
        ∃ m, trXorSel bs m = wt q.2 ^^^ wt q.1) ∧
      (∀ t < 20, ∃ m, trXorSel (pl.map fun q => wt q.1) m = 2 ^ t) ∧
      (trFixL (trRepT 3)).length % 2 = 1 ∧
      (∃ q₀ ∈ trFixL (trRepT 3), ∀ Q : ℕ → Prop, Q q₀ →
        (∀ q ∈ trFixL (trRepT 3), ∀ u ∈ trFixL (trRepT 3), Q u → Q (tvImg q u)) →
        ∀ v ∈ trFixL (trRepT 3), Q v) ∧
      ∃ b6 : List ℕ, b6.length = 6 ∧ (∀ x ∈ b6, x ∈ trFixL (trRepT 3)) ∧
        ∀ m, 0 < m → m < 64 → trXorSel (b6.map fun x => (tvPair x).1) m ≠ 0) := by
  have hvP : ∀ y < 1953, vP (codeOf (tvPair y)) = tvVec y := fun y hy => by
    rw [vP, codeOf_div (tvP_tvPair hy)]
    rfl
  have hfP : ∀ y < 1953, fP (codeOf (tvPair y)) = tvForm y := fun y hy => by
    rw [fP, codeOf_mod (tvP_tvPair hy)]
    rfl
  have hRT : ∀ k < 5, Certificates.trRepT k =
      trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2 := fun k hk => by
    interval_cases k <;> simp only [Certificates.trRepT, Certificates.trRep, repsC] <;> rfl
  have h3 : Certificates.trRepT 3 = trCandT (trLift 4) 0 := by
    simp only [Certificates.trRepT, Certificates.trRep, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨fun j hj a ha hinv hne => ?_, fun k hk => ?_, ?_⟩
  · rcases KernelSmithL6K.cx_cases hj ha with h | h | ⟨k, hk, G, H, hHG, hconj⟩
    · obtain ⟨x, hx, hne⟩ := hne
      exact absurd (h x hx) hne
    · obtain ⟨x, hx, hne⟩ := h
      exact absurd (hinv x hx) hne
    · refine ⟨k, hk, G, H, hHG, fun x hx y hy hv hf => ?_⟩
      have hr : (repsC.getD k (0, 0)).1 < 5 := by
        have := repsC_fst k hk
        by_cases h3 : k < 3 <;> omega
      obtain ⟨_, hlt1⟩ := KernelSmithL6K.cx_code hj a hx
      obtain ⟨_, hlt2⟩ := KernelSmithL6K.cx_code hr (repsC.getD k (0, 0)).2 hy
      have h' := hconj x hx y hy (by rw [hvP x hx, hvP y hy]; exact hv)
        (by rw [hfP x hx, hfP y hy]; exact hf)
      rw [hvP _ hlt1, hvP _ hlt2, hfP _ hlt1, hfP _ hlt2] at h'
      rw [hRT k hk]
      exact h'
  · rw [hRT k hk]
    exact KernelSmithL6K.cx_rep_facts hk
  · rw [h3]
    exact KernelSmithL6K.cx_outer

end Certificates
