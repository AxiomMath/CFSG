module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Clifford

variable {W : Type} [CommGroup W] [Finite W]

theorem s15_semi_isIrrOn_map {N : Subgroup (MulAut W)} {x : MulAut W}
    (hx : ∀ n ∈ N, x⁻¹ * n * x ∈ N) (hx' : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    {J : Subgroup W} (hJ : IsIrrOn N J ⊥) : IsIrrOn N (J.map x.toMonoidHom) ⊥ := by
  have hne : J.map x.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hJ.1.ne' ((Subgroup.map_eq_bot_iff_of_injective (f := x.toMonoidHom) J
      x.injective).1 hbot)
  refine ⟨bot_lt_iff_ne_bot.2 hne, ?_, hJ.2.2.1, ?_⟩
  · rintro n hn y ⟨u, huJ, rfl⟩
    refine ⟨(x⁻¹ * n * x) u, hJ.2.1 _ (hx n hn) u huJ, ?_⟩
    simp [MulAut.mul_apply, MulAut.inv_apply]
  · intro K hK _ hKle
    have hKc : StableUnder N (K.comap x.toMonoidHom) := by
      intro n hn y hy
      have hmem : (x * n * x⁻¹) (x y) ∈ K := hK _ (hx' n hn) _ hy
      have heq : x.toMonoidHom (n y) = (x * n * x⁻¹) (x y) := by
        simp [MulAut.mul_apply, MulAut.inv_apply]
      show x.toMonoidHom (n y) ∈ K
      rw [heq]
      exact hmem
    have hKJ : K.comap x.toMonoidHom ≤ J := by
      intro y hy
      obtain ⟨u, huJ, hu⟩ := Subgroup.mem_map.1 (hKle hy)
      have : u = y := x.injective hu
      rwa [← this]
    rcases hJ.2.2.2 (K.comap x.toMonoidHom) hKc bot_le hKJ with hY | hY
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := x.toMonoidHom) x.surjective K, hY,
        Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := x.toMonoidHom) x.surjective K, hY]

end Clifford

section Conjugates

variable {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semi_isIrrOn_Mbar (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) :
    IsIrrOn (Mbar D.M V₀ V h.isElemAbelian) (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)) ⊥ := by
  have hV := h.isElemAbelian
  obtain ⟨-, -, hle, hTI₀, hnTI, -, -⟩ : InCalV0 D.M V₀ V := by
    rcases h.1 with ⟨-, h0⟩ | ⟨h0, -, -⟩
    · exact absurd h0 hV₀
    · exact h0
  obtain ⟨v, hvV, hv0⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne hle (by rintro rfl; exact hnTI hTI₀))
  have hq : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ≠ 1 := fun h1 =>
    hv0 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h1)
  refine ⟨?_, fun _ _ _ _ => Subgroup.mem_top _, ?_, fun J hJ _ _ =>
    s15_Kbar_irreducible h hV₀ J hJ⟩
  · refine lt_of_le_of_ne bot_le fun hbt => hq ?_
    have hmem : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ (⊥ : Subgroup (Vtil V₀ V hV)) := by
      rw [hbt]
      exact Subgroup.mem_top _
    exact Subgroup.mem_bot.1 hmem
  · intro a _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]

theorem s15_semi_le_iSup_barSub (h : Hyp151 D V₀ V L) :
    barSub V₀ V h.isElemAbelian L ≤
      ⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)) := by
  have h1 := le_iSup
    (fun m : D.M => barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) (1 : D.M)
  simpa [conjSubgroup_one] using h1

theorem s15_semi_iSup_barSub_le_normalizer (h : Hyp151 D V₀ V L) :
    (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) ≤
      normalizer (barSub V₀ V h.isElemAbelian L : Set (MulAut (Vtil V₀ V h.isElemAbelian))) := by
  refine iSup_le fun m => ?_
  by_cases hm : (m : G) ∈ nBar D.M V₀ V h.isElemAbelian L
  · rw [(s15_Infra_mem_nBar_iff h.hyp125 h.isElemAbelian m.2).1 hm]
    exact Subgroup.le_normalizer
  · have hc := (h.commute (m : G) m.2 hm).1
    rw [Subgroup.commutator_comm] at hc
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (Subgroup.centralizer_le_normalizer _)

end Conjugates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
