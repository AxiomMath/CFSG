module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_swap_of_s15 {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs : s15 D.M V₀ V h.isElemAbelian L = 2) :
    ∃ x ∈ D.M, x ∉ nBar D.M V₀ V h.isElemAbelian L ∧
      (∀ m ∈ D.M,
        barSub V₀ V h.isElemAbelian (conjSubgroup L m) = barSub V₀ V h.isElemAbelian L ∨
        barSub V₀ V h.isElemAbelian (conjSubgroup L m) =
          barSub V₀ V h.isElemAbelian (conjSubgroup L x)) ∧
      ∀ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
        (((barSub V₀ V h.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
              barSub V₀ V h.isElemAbelian L ∧
            (barSub V₀ V h.isElemAbelian (conjSubgroup L x)).map
                (MulAut.conj φ).toMonoidHom =
              barSub V₀ V h.isElemAbelian (conjSubgroup L x)) ∨
          ((barSub V₀ V h.isElemAbelian L).map (MulAut.conj φ).toMonoidHom =
              barSub V₀ V h.isElemAbelian (conjSubgroup L x) ∧
            (barSub V₀ V h.isElemAbelian (conjSubgroup L x)).map
                (MulAut.conj φ).toMonoidHom =
              barSub V₀ V h.isElemAbelian L)) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  obtain ⟨⟨ψ₀, hψ₀, hne⟩, hrest⟩ :=
    c23a_two_conj (Mb := Mbar D.M V₀ V hV) (L := barSub V₀ V hV L) hs
  obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV D.M ψ₀).1 hψ₀
  obtain ⟨hall, hperm⟩ := hrest _ hψ₀ hne
  have hx : (g : G)⁻¹ ∈ D.M := D.M.inv_mem hgM
  have hxs : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil V₀ V).inv_mem g.2
  have hconj : barSub V₀ V hV (conjSubgroup L (g : G)⁻¹) =
      (barSub V₀ V hV L).map (MulAut.conj (actTil V₀ V hV g)).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hxs L]
    have : (⟨(g : G)⁻¹, hxs⟩ : stabTil V₀ V) = g⁻¹ := rfl
    rw [this, map_inv (actTil V₀ V hV) g, inv_inv]
  refine ⟨(g : G)⁻¹, hx, ?_, ?_, ?_⟩
  · rw [s15_Infra_mem_nBar_iff h.hyp125 hV hx, hconj]
    exact hne
  · intro m hm
    have hmem : (actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹ ∈ Mbar D.M V₀ V hV :=
      inv_mem (actTil_mem_barSub V₀ V hV hm (hMs hm))
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L, hconj]
    exact hall _ hmem
  · intro φ hφ
    rw [hconj]
    exact hperm φ hφ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
