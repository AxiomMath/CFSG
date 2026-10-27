module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo
open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChartGen_conj_le {g : G} (hg : g ∈ QTwoH L 𝒦) :
    L.map (MulAut.conj g).toMonoidHom ≤ QTwoH L 𝒦 := by
  rintro _ ⟨l, hl, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg (Subgroup.mem_sup_left hl))
    (Subgroup.inv_mem _ hg)

theorem qTwoChartGen_liftsOne (S : QTwoChartSetting B Bs x L D J 𝒦 m n) :
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (1 : G) 1 := by
  refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun b => ?_⟩
  simp

theorem qTwoChartGen_lift_of_induced (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {K' : Subgroup G} (hKH : K' ≤ QTwoH L 𝒦)
    (hA : ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦) {n' : G} (hn' : n' ∈ K')
    (hN : n' ∈ Subgroup.normalizer (Bs : Set G)) {φ : MulAut ↥Bs}
    (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n' * (b : G) * n'⁻¹) :
    ∃ π : Equiv.Perm (Fin (n + 1)), QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA n' π := by
  have hφA : φ ∈ ggAutomizerJoin L Bs 𝒦 :=
    hA (mem_ggAutomizer_iff.mpr ⟨n', hn', hN, hφ⟩)
  refine ⟨S.ρA.symm ⟨φ, hφA⟩, hKH hn', hN, fun b => ?_⟩
  simpa only [MulEquiv.apply_symm_apply] using hφ b

theorem qTwoChartGen_nbr_le (S : QTwoChartSetting B Bs x L D J 𝒦 m n) {y : G}
    {K' : Subgroup G} (hnbr : GGNbr 3 B x D J y K') (hKH : K' ≤ QTwoH L 𝒦) :
    K' ≤ ⨆ (π : Equiv.Perm (Fin (n + 1))) (g : G)
        (_ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π), L.map (MulAut.conj g).toMonoidHom := by
  have hRM : ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 := S.hRMGen.hRM y K' hnbr
  refine (S.hRMGen.hGen y K' hnbr hRM).trans (iSup_le fun n' => iSup_le fun hn' =>
    iSup_le fun h => ?_)
  obtain ⟨φ, hN, hφ⟩ := h
  obtain ⟨π, hπ⟩ := qTwoChartGen_lift_of_induced S hKH hRM hn' hN hφ
  exact (Subgroup.map_mono (GGConfig.stdSub_le S.hcfg.1.1)).trans
    (le_iSup_of_le π (le_iSup_of_le n' (le_iSup_of_le hπ le_rfl)))

theorem qTwoChart_generation (S : QTwoChartSetting B Bs x L D J 𝒦 m n) :
    QTwoH L 𝒦 =
      ⨆ (π : Equiv.Perm (Fin (n + 1))) (g : G) (_ : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π),
        L.map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · refine sup_le ?_ (iSup₂_le fun k hk => ?_)
    · refine le_iSup_of_le (1 : Equiv.Perm (Fin (n + 1))) ?_
      refine le_iSup_of_le (1 : G) ?_
      exact le_iSup_of_le (qTwoChartGen_liftsOne S) fun l hl => ⟨l, hl, by simp⟩
    · obtain ⟨y, hnbr⟩ := S.hcfg.2.2.2.1.2 k hk
      exact qTwoChartGen_nbr_le S hnbr (le_sup_of_le_right (le_iSup₂_of_le k hk le_rfl))
  · exact iSup_le fun π => iSup_le fun g => iSup_le fun hg => qTwoChartGen_conj_le hg.1

end CFSG.StandardType.QTwo

end
