module

public import CFSG.Quasithin.AppendixH.H9.H93.S8CentSwap
public import CFSG.Quasithin.AppendixH.H9.H93.S8CentTriple
public import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.CentralizerTransfer
public import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.OuterInvolutions

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem h93_part1 (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) :
    (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 →
        ((psiExt ψ t).cycleType = {2} ∨ (psiExt ψ t).cycleType = {2, 2, 2})) ∧
      (∃ t ∈ Mg 4, t ∉ Lg 4 ∧ orderOf t = 2 ∧ (psiExt ψ t).cycleType = {2}) ∧
      (∃ u ∈ Mg 4, u ∉ Lg 4 ∧ orderOf u = 2 ∧ (psiExt ψ u).cycleType = {2, 2, 2}) ∧
      (∀ t ∈ Mg 4, ∀ u ∈ Mg 4, t ∉ Lg 4 → u ∉ Lg 4 → orderOf t = 2 → orderOf u = 2 →
        (psiExt ψ t).cycleType = (psiExt ψ u).cycleType → IsConjIn (Mg 4) t u) ∧
      (∀ t ∈ Mg 4, t ∉ Lg 4 → orderOf t = 2 → (psiExt ψ t).cycleType = {2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN 4)))) ≃*
          Equiv.Perm (Fin 6))) ∧
      (∀ u ∈ Mg 4, u ∉ Lg 4 → orderOf u = 2 → (psiExt ψ u).cycleType = {2, 2, 2} →
        Nonempty (↥(Lg 4 ⊓ Subgroup.centralizer ({u} : Set (MulAut (PairN 4)))) ≃*
          (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hL h2
    exact cycleType_psiExt_of_outer_involution ψ ht hL h2
  · obtain ⟨t, ht, hL, h2, hψ⟩ :=
      exists_outer_involution ψ orderOf_swap_zero_one sign_swap_zero_one
    exact ⟨t, ht, hL, h2, by rw [hψ]; exact cycleType_swap_zero_one⟩
  · obtain ⟨u, hu, hL, h2, hψ⟩ := exists_outer_involution ψ orderOf_swap_triple sign_swap_triple
    exact ⟨u, hu, hL, h2, by rw [hψ]; exact cycleType_swap_triple⟩
  · intro t ht u hu _ _ _ _ h
    exact isConjIn_Mg_of_cycleType_eq ψ ht hu h
  · intro t ht _ _ hct
    obtain ⟨e⟩ := nonempty_mulEquiv_Lg_centralizer ψ ht
    obtain ⟨f⟩ := altInfCentralizer_swap hct
    exact ⟨e.trans f⟩
  · intro u hu _ _ hcu
    obtain ⟨e⟩ := nonempty_mulEquiv_Lg_centralizer ψ hu
    obtain ⟨f⟩ := altInfCentralizer_triple hcu
    exact ⟨e.trans f⟩

end CFSG.ASVolI.ChH
