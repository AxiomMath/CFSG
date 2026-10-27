module

public import CFSG.LocalAnalysis.StandardType.GGFFModelSLN
import CFSG.LocalAnalysis.StandardType.GGFFModel
import CFSG.LocalAnalysis.StandardType.GGFFModelN
import CFSG.LocalAnalysis.StandardType.GGFFModelSL
import CFSG.Adapters.StatedSLTwoField
public import CFSG.Open.StatedDefs

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.Open (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single_one)

private theorem comm_of_mem_tor {L : Type} [Group L] {z : Fin 3 → L} {k : L}
    (hk : ∀ i, k * z i = z i * k) : ∀ x ∈ GGFF.tor z, k * x = x * k := by
  have hsub : GGFF.tor z ≤ Subgroup.centralizer ({k} : Set L) := by
    show Subgroup.closure (Set.range z) ≤ Subgroup.centralizer ({k} : Set L)
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨i, rfl⟩ := hy
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hk i
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hsub hx)) k (Set.mem_singleton k)

private theorem cen_of_model_aux {L : Type} [Group L] {z z' : Fin 3 → L}
    (hz : GGFF.Model L z) (hM' : GGFF.Model L z') (hN' : GGFF.ModelN L z') {k : L}
    (hk : ∀ i, k * z i = z i * k) : ∃ v, k = vecElt z v := by
  have hkt : ∀ x ∈ GGFF.tor z, k * x = x * k := comm_of_mem_tor hk
  obtain ⟨g, hg⟩ := hM'.torus (GGFF.tor z) hz.isElemAbelian_tor' hz.card_tor'
  have hkg : ∀ i, k * (g * z' i * g⁻¹) = (g * z' i * g⁻¹) * k := by
    intro i
    refine hkt (g * z' i * g⁻¹) ((hg _).mpr ⟨Pi.single i 1, ?_⟩)
    rw [vecElt_single_one]
  obtain ⟨w, hw⟩ := (hN'.conj g).cen k hkg
  have hw' : k = g * vecElt z' w * g⁻¹ := by
    rw [hw]
    simpa only [MulAut.conj_apply] using GGFF.vecElt_map (MulAut.conj g) z' w
  obtain ⟨v, hv⟩ := (hz.mem_tor').mp ((hg _).mpr ⟨w, rfl⟩)
  exact ⟨v, hw'.trans hv⟩

theorem cen_of_model {L : Type} [Group L] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (hL : StatedClassicalModel L .PSL (n + 1) 2 1) {z : Fin 3 → L} (hz : GGFF.Model L z) :
    ∀ k : L, (∀ i, k * z i = z i * k) → ∃ v, k = vecElt z v := by
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hL
  rcases hn with rfl | rfl
  · exact fun k hk => cen_of_model_aux hz (GGFF.model_SL6.ofMulEquiv e.symm)
      (GGFF.modelN_SL6.ofMulEquiv e.symm) hk
  · exact fun k hk => cen_of_model_aux hz (GGFF.model_SL7.ofMulEquiv e.symm)
      (GGFF.modelN_SL7.ofMulEquiv e.symm) hk

end CFSG.StandardType.FF81

end
