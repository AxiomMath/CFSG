module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.LocalDataOfCheck

open CFSG.AGLEmbedding.MaxD2
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

theorem localData_rsub_of_check {D : Data} {S : List (Equiv.Perm (Fin D.n))} (hp : D.p.Prime)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1)) (hlen : S.length = D.gT.size)
    (hcard : Nat.card (Gsub S) = D.gOrder) (hsolv : ∃ a b : ℕ, D.nOrder = D.p ^ 2 * (2 ^ a * 3 ^ b))
    (h : check D = true) :
    LocalData D.p D.tm D.tlam D.te (Gsub S) (Rsub D S) ∧
      ¬ Gsub S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hInv, hR⟩, hN⟩, hNorm⟩, hMoves⟩, hTorus⟩, hCent⟩, hMax⟩ := h
  have hgi := giT_rep hS hInv
  have hNeq := normalizer_inf_eq hS hgi hlen hcard hR hN hNorm hMoves hMax
  refine ⟨⟨Rsub_le_Gsub, card_R hS hgi hR, ?_, centralizer_le hS hgi hlen hcard hR hN hNorm hMoves
    hMax hCent, ?_, ?_⟩, not_le_normalizer hS hgi hlen hR hMoves⟩
  · intro Y hY hYG
    rw [hNeq] at hY ⊢
    exact maximal_N hS hgi hlen hcard hN (invsOK_of_checkNormal hNorm) hMax Y hY hYG
  · rw [hNeq]
    obtain ⟨a, b, hab⟩ := hsolv
    refine isSolvable_of_normal_sq (a := a) (b := b) hp ?_ (N_le_normalizer hS hgi hR hNorm)
      (card_R hS hgi hR) (by rw [card_N hS hgi hN, hab])
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  · obtain ⟨t, htN, h1, h2, h3⟩ := torus_data hS hgi hp hR hN hTorus
    exact ⟨t, by rw [hNeq]; exact htN, h1, h2, h3⟩

end CFSG.StandardType.LocalDataOfCheck
