module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Ind
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv Equiv.Perm

private theorem isSwap_of_apply_comp {m n : ℕ} {ι : Fin m ↪ Fin n} {ω : Fin n}
    (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω) {g : Perm (Fin n)} {σ : Perm (Fin m)}
    (hω : g ω = ω) (hg : ∀ i, g (ι i) = ι (σ i)) (hσ : σ.IsSwap) : g.IsSwap := by
  obtain ⟨i, j, hij, rfl⟩ := hσ
  refine ⟨ι i, ι j, ι.injective.ne hij, Equiv.ext fun x => ?_⟩
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨k, rfl⟩ := hx
    rw [hg, ι.injective.swap_apply]
  · have hxω : x = ω := by
      by_contra h
      exact hx ((hι x).2 h)
    rw [hxω, hω, swap_apply_of_ne_of_ne ((hι _).1 ⟨i, rfl⟩).symm ((hι _).1 ⟨j, rfl⟩).symm]

theorem t86_of_ten_le {n : ℕ} (hn : 10 ≤ n) (hT : T86 (n - 1)) (hF : NoFpf n) : T86 n := by
  intro V _ _ hV H ψ hψ hAlt t ht2 ht1 hts hidx
  by_cases hfp : ∃ a, ψ t a = a
  swap
  · push Not at hfp
    exact (hF V hV H ψ hψ hAlt t ht2 hfp hidx).elim
  obtain ⟨a, ha⟩ := hfp
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne (show n - 1 + 1 = n by omega) a
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
    fun h _ hh => coe_mem_preSub.2 hh
  have hinj : Function.Injective
      (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl) :=
    restrictHom_injective (hK := le_rfl) hψ fun k hk =>
      eq_one_of_apply_eq_of_range_ne hι (apply_mem_permSetStab (hK := le_rfl) k) hk
  have htK : (t : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
    coe_mem_preSub.2 (mem_permSetStab_of_apply_eq hι ha)
  have ht2K : (⟨(t : MulAut V), htK⟩ : ↥(preSub ψ (permSetStab (Set.range ι)))) ^ 2 = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val ht2)
  have hκ1 : restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl ⟨t, htK⟩ ≠ 1 :=
    fun h => ht1 (eq_one_of_apply_eq_of_range_ne hι (mem_permSetStab_of_apply_eq hι ha)
      ((restrictHom_eq_one_iff (hK := le_rfl) ⟨(t : MulAut V), htK⟩).1 h))
  have hκs : ¬ (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl
      ⟨t, htK⟩).IsSwap := fun h =>
    hts (isSwap_of_apply_comp hι ha (fun i => (restrictHom_apply_apply (hK := le_rfl)
      ⟨(t : MulAut V), htK⟩ i).symm) h)
  rcases hT V hV _ _ hinj (alternatingGroup_le_range_restrictHom hAlt hKmem) ⟨t, htK⟩ ht2K hκ1
      hκs hidx with hnat | ⟨h7, -⟩
  · exact Or.inl (natVia_commV_of_natShape (by omega) hψ hAlt (natShape_of_stab hV (by omega) ι
      (by omega) _ (natShape_altRho_comp_altLift hψ hAlt _ ι
        (exists_restrictHom_eq_altLift hAlt hKmem) hnat)))
  · omega

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
