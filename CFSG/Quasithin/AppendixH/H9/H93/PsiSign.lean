module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.SignOnLg
public import CFSG.Quasithin.AppendixH.H9.H93.S8Part1.PsiExtBasic

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem mem_Lg_iff_sign (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) {g : MulAut (PairN 4)}
    (hg : g ∈ Mg 4) : g ∈ Lg 4 ↔ Equiv.Perm.sign (psiExt ψ g) = 1 := by
  constructor
  · intro hL
    obtain ⟨A, rfl⟩ := mem_Lg_iff.1 hL
    exact sign_psiExt_pairActN ψ A
  · intro hs
    by_contra hnL
    obtain ⟨A, hA⟩ : ∃ A : GL (Fin 4) (ZMod 2), g = pairActN 4 A * swapN 4 := by
      rcases mem_Mg_iff.1 hg with hL | h
      · exact absurd hL hnL
      · exact h
    have key : ∀ m : MulAut (PairN 4), m ∈ Mg 4 → Equiv.Perm.sign (psiExt ψ m) = 1 := by
      intro m hm
      rcases mem_Mg_iff.1 hm with hmL | ⟨B, hB⟩
      · obtain ⟨C, rfl⟩ := mem_Lg_iff.1 hmL
        exact sign_psiExt_pairActN ψ C
      · have hm' : m = pairActN 4 (B * A⁻¹) * g := by
          rw [hB, hA, map_mul, map_inv]
          group
        rw [hm', psiExt_mul ψ (Lg_le_Mg (pairActN_mem_Lg _)) hg, map_mul,
          sign_psiExt_pairActN ψ, hs, one_mul]
    have h1 := key (ψ.symm (Equiv.swap 0 1) : ↥(Mg 4)).1 (ψ.symm (Equiv.swap 0 1)).2
    rw [psiExt_coe, MulEquiv.apply_symm_apply, Equiv.Perm.sign_swap (by decide)] at h1
    exact absurd h1 (by decide)

end CFSG.ASVolI.ChH
