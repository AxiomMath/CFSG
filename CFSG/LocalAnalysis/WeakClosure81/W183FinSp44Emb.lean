module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Dyn
import CFSG.GroupTheory.ConjNormalFaithful

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSp4)

private theorem w183finSp44Emb_map_conjNormal {G : Type} [Group G] (H : Subgroup G) [H.Normal] :
    H.map (MulAut.conjNormal : G →* MulAut H) = innAutOf H := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, (MulAut.conjNormal_val (h := ⟨g, hg⟩)).symm⟩
  · intro x hx
    rw [innAutOf] at hx
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hx
    exact Subgroup.mem_map.mpr ⟨(h : G), h.2, MulAut.conjNormal_val⟩

private theorem w183finSp44Emb_congr_conj {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (m : M) : MulAut.congr e (MulAut.conj m) = MulAut.conj (e m) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem w183finSp44Emb_map_innAutOf {M M' : Type} [Group M] [Group M'] (e : M ≃* M') :
    (innAutOf M).map (MulAut.congr e).toMonoidHom = innAutOf M' := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hψ
    exact MonoidHom.mem_range.mpr ⟨e m, (w183finSp44Emb_congr_conj e m).symm⟩
  · intro x hx
    rw [innAutOf] at hx
    obtain ⟨m', rfl⟩ := MonoidHom.mem_range.mp hx
    refine ⟨MulAut.conj (e.symm m'), MonoidHom.mem_range.mpr ⟨e.symm m', rfl⟩, ?_⟩
    show MulAut.congr e (MulAut.conj (e.symm m')) = MulAut.conj m'
    rw [w183finSp44Emb_congr_conj e (e.symm m'), MulEquiv.apply_symm_apply]

theorem exists_emb (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (hLn : L.Normal)
    (hSp : IsSp4 ↥L 2) (hC : Subgroup.centralizer (L : Set Y) = ⊥) :
    ∃ f : Y →* MulAut S4, Function.Injective f ∧ L.map f = innAutOf S4 := by
  letI : L.Normal := hLn
  obtain ⟨e⟩ := isSp4_equiv_S4 hSp
  let f : Y →* MulAut S4 := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Y →* MulAut ↥L)
  refine ⟨f, ?_, ?_⟩
  · exact (MulAut.congr e).injective.comp
      (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC)
  · rw [← Subgroup.map_map, w183finSp44Emb_map_conjNormal, w183finSp44Emb_map_innAutOf]

theorem emb_bijective (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) (f : Y →* MulAut S4)
    (hf : Function.Injective f) (hL : L.map f = innAutOf S4)
    (hτ : ∃ τ : Y, ActsOnDynkinMod ⊥ L τ) : Function.Bijective f := by
  obtain ⟨τ, hτ⟩ := hτ
  have hdyn : ActsOnDynkinMod ⊥ (innAutOf S4) (f τ) := by
    have h := W183L34.actsOnDynkinMod_map f hf hτ
    rwa [hL] at h
  refine ⟨hf, MonoidHom.range_eq_top.mp ?_⟩
  rw [eq_top_iff, ← dynkin_generates_S4 hdyn]
  exact sup_le (hL ▸ Subgroup.map_le_range f L)
    (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
