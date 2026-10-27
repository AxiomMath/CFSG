module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Basic
public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.LIT (autGL autGL_mulVec)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma autGL_symm_comp_toLin_zt (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    (g : U ≃ₗ[ZMod p] U) :
    (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U) ∘ₗ
        Matrix.toLin' ((autGL e g : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)) =
      (g : U →ₗ[ZMod p] U) ∘ₗ
        (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U) := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  rw [autGL_mulVec]
  exact LinearEquiv.symm_apply_apply e (g (e.symm v))

theorem isImprimitiveOnV_of_lines (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {L : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p)}
    (hL : DirectSum.IsInternal L) (h1 : ∀ i, Module.finrank (ZMod p) (L i) = 1)
    (hperm : ∀ g ∈ A.map (autGL e).toMonoidHom, ∀ i, ∃ j,
      CFSG.RankThree.SubgroupLists.translate g (L i) = L j) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  let F := Submodule.orderIsoMapComap (e.symm : (Fin 3 → ZMod p) ≃ₗ[ZMod p] U)
  have hF : ∀ i, F (L i) =
      (L i).map (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U) :=
    fun i => Submodule.orderIsoMapComap_apply _ _
  refine ⟨3, fun i => F (L i), by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i hbot
    change F (L i) = ⊥ at hbot
    have hLi : L i = ⊥ := by
      rw [← F.symm_apply_apply (L i), hbot, OrderIso.map_bot]
    have h1i := h1 i
    rw [hLi, finrank_bot] at h1i
    exact Nat.zero_ne_one h1i
  · simpa only [Function.comp_def, hF] using
      iSupIndep.map_orderIso F hL.submodule_iSupIndep
  · have hmap : (⨆ i, F (L i)) = ⨆ i, (L i).map (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U) := by
      simp only [hF]
    rw [hmap, ← Submodule.map_iSup (e.symm : (Fin 3 → ZMod p) →ₗ[ZMod p] U) L,
      hL.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LinearEquiv.surjective e.symm)
  · intro g hg i
    obtain ⟨j, hj⟩ := hperm (autGL e g) (Subgroup.mem_map_of_mem _ hg) i
    refine ⟨j, ?_⟩
    change (F (L i)).map (g : U →ₗ[ZMod p] U) = F (L j)
    rw [hF i, hF j, ← hj]
    rw [CFSG.RankThree.SubgroupLists.translate]
    simp only [← Submodule.map_comp, autGL_symm_comp_toLin_zt]

end CFSG.StandardType.ZS.DimThree
