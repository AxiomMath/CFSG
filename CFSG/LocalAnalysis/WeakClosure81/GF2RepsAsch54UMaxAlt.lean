module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxSec

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Alt
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalEmbed
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup


theorem asch80ThmA54Case_alt (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch80ThmA54Case fun X _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n)) := by
  intro Q _ _ L T M hK hLn hLs hLnab hC hP hL0 hT hMt hM
  obtain ⟨n, hn5, ⟨e⟩⟩ := hP
  by_cases hn6 : n ≤ 6
  · refine asch80ThmA54Case_of_sectionalTwoRankLE hS
      (P := fun X _ => ∃ m : ℕ, 5 ≤ m ∧ m ≤ 6 ∧ Nonempty (X ≃* alternatingGroup (Fin m)))
      ?_ ?_ Q L T M hK hLn hLs hLnab hC ⟨n, hn5, hn6, ⟨e⟩⟩ hL0 hT hMt hM
    · rintro X _ _ ⟨m, -, hm6, ⟨eX⟩⟩
      exact (sectionalTwoRankLE_two_alternatingGroup (by omega)).of_mulEquiv eX.symm
    · rintro X _ _ _ _ ⟨m, hm5, hm6, ⟨eX⟩⟩ -
      obtain rfl | rfl : m = 5 ∨ m = 6 := by omega
      · exact Or.inl (Or.inl (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five
          eX))
      · exact Or.inr (Or.inl (Or.inl ⟨eX⟩))
  have hL0facts : ∀ (X : Type) [Group X], IsCalL0 X →
      ∃ _ : Finite X, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X) ∧
        ∃ a b : X, a * b ≠ b * a :=
    fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
      CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
      ((isCalL0_iff_asc1930ListB X).1 hX)
  by_cases hn9 : n = 9
  · subst n
    exact (hL0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))))).elim
  obtain ⟨φ, hφ, hA⟩ :=
    @CFSG.AGLEmbedding.exists_embedding_alternating_of_ne_six Q _ n hn5 (by omega) L hLn e hC
  let ψ : ↥(⊤ : Subgroup Q) →* Equiv.Perm (Fin n) :=
    φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp (Subgroup.topEquiv (G := Q)).injective
  have hAψ : alternatingGroup (Fin n) ≤ ψ.range := by
    have hrange : ψ.range = φ.range := by
      change (φ.comp (Subgroup.topEquiv (G := Q)).toMonoidHom).range = φ.range
      rw [MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr (Subgroup.topEquiv (G := Q)).surjective, Subgroup.map_top]
    rw [hrange]
    exact hA
  by_cases hn11 : n ≤ 11
  · exact absurd (Asch59.eq_lGen_of_injective_perm hL0facts (by omega) hn11 hn9 ψ hψ hAψ le_top
      hT.isPGroup).symm (lGen_ne_top_of_forall_le hMt hM)
  · obtain ⟨h3, h1⟩ := Asch59.pRank_three_of_injective_perm hL0facts (by omega) ψ hψ hAψ le_top
      hT.isPGroup
    exact Or.inl ⟨3, Nat.prime_three, by norm_num, h3, h1⟩

end CFSG.LocalAnalysis.WeakClosure81

end
