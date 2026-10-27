module

public import CFSG.Milestones.ASVolI.A3Aut.Core

public section

namespace CFSG.ASVolI

open CFSG.Open

section InnDiag

theorem burnsideAut_congr_conj_eq {S M : Type*} [Group S] [Group M] (e' : S ≃* M)
    (χ ψ : MulAut S) : MulAut.congr (χ.symm.trans e') (χ * ψ * χ⁻¹) = MulAut.congr e' ψ := by
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply]

theorem burnsideAut_mul_conj_mul_inv {S : Type*} [Group S] (χ : MulAut S) (y : S) :
    χ * MulAut.conj y * χ⁻¹ = MulAut.conj (χ y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem burnsideAut_isInnDiagAut_conj {S : Type} [Group S] (χ ψ : MulAut S)
    (h : ChA.IsInnDiagAut S ψ) : ChA.IsInnDiagAut S (χ * ψ * χ⁻¹) := by
  rcases h with ⟨y, rfl⟩ | ⟨n, K, hK1, hK2, e', c, hK, hc⟩ | ⟨n, K, hK1, hK2, e', c, hK, hc⟩
  · exact Or.inl ⟨χ y, (burnsideAut_mul_conj_mul_inv χ y).symm⟩
  · refine Or.inr (Or.inl ⟨n, K, hK1, hK2, χ.symm.trans e', c, hK, ?_⟩)
    rw [burnsideAut_congr_conj_eq]
    exact hc
  · refine Or.inr (Or.inr ⟨n, K, hK1, hK2, χ.symm.trans e', c, hK, ?_⟩)
    rw [burnsideAut_congr_conj_eq]
    exact hc

theorem burnsideAut_innDiag_normal (S : Type) [Group S] : (ChA.innDiagSubgroup S).Normal := by
  refine ⟨fun x hx χ => ?_⟩
  have key : (ChA.innDiagSubgroup S).map (MulAut.conj χ).toMonoidHom ≤ ChA.innDiagSubgroup S := by
    rw [ChA.innDiagSubgroup, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨ψ, hψ, rfl⟩
    exact burnsideAut_isInnDiagAut_conj χ ψ hψ
  exact key ⟨x, hx, rfl⟩

theorem burnsideAut_inn_le_innDiag (S : Type) [Group S] :
    (MulAut.conj : S →* MulAut S).range ≤ ChA.innDiagSubgroup S := fun ψ hψ =>
  Subgroup.subset_closure (Or.inl hψ)

end InnDiag

section Transport

variable {G : Type} [Group G]

theorem burnsideAut_conjNormal_of_mem {L : Subgroup G} [L.Normal] {l : G} (hl : l ∈ L) :
    MulAut.conjNormal l = MulAut.conj (⟨l, hl⟩ : ↥L) := by
  ext x
  simp [MulAut.conjNormal_apply, MulAut.conj_apply]

theorem burnsideAut_autImage_of_le {L X : Subgroup G} [L.Normal] (hX : X ≤ L) :
    CFSG.Quasithin.A315.autImage L X = (X.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) := by
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hX hx⟩, Subgroup.mem_subgroupOf.2 hx, (burnsideAut_conjNormal_of_mem (hX hx)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.1 hy, burnsideAut_conjNormal_of_mem y.2⟩

theorem burnsideAut_congr_conj {S M : Type*} [Group S] [Group M] (e : S ≃* M) (y : S) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext m
  simp [MulAut.congr_apply, map_mul, map_inv]

theorem burnsideAut_map_congr_conj {S M : Type*} [Group S] [Group M] (e : S ≃* M) (U : Subgroup S) :
    (U.map (MulAut.conj : S →* MulAut S)).map (MulAut.congr e).toMonoidHom =
      (U.map e.toMonoidHom).map (MulAut.conj : M →* MulAut M) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y : 1
  exact burnsideAut_congr_conj e y

theorem burnsideAut_conj_congr_symm {S M : Type*} [Group S] [Group M] (e : S ≃* M) (l : S)
    (x : MulAut M) :
    MulAut.conj (MulAut.conj l) (MulAut.congr e.symm x) =
      MulAut.congr ((MulAut.conj l⁻¹).trans e).symm x := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply, MulAut.mul_apply]

theorem burnsideAut_solvBorel_of_mulEquiv {S M : Type} [Group S] [Group M] (e : S ≃* M)
    {U : Subgroup S} (h : burnsideAut_SolvBorel M (U.map e.toMonoidHom)) :
    burnsideAut_SolvBorel S U := by
  intro Y hUY hY
  have hY' : Group.IsSolvable ↥(Y.map e.toMonoidHom) :=
    solvable_of_surjective (f := (Y.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (Y.equivMapOfInjective e.toMonoidHom e.injective).surjective
  have h1 := h (Y.map e.toMonoidHom) (Subgroup.map_mono hUY) hY'
  intro y hy
  have h2 : e y ∈ Subgroup.normalizer ((U.map e.toMonoidHom : Subgroup M) : Set M) :=
    h1 ⟨y, hy, rfl⟩
  rw [← Subgroup.map_equiv_normalizer_eq] at h2
  obtain ⟨y', hy', hyy'⟩ := h2
  rwa [e.injective hyy'] at hy'

end Transport

end CFSG.ASVolI
