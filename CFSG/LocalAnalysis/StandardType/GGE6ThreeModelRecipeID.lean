module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeIndex
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6Core

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc TableBExc.E6Three

variable {K : Type} [Field K] [Finite K]

private theorem map_congr_eq_of_normal {R C : Type} [Group R] [Group C]
    (J : Subgroup (MulAut R)) (hJ : J.Normal) (e e' : R ≃* C) :
    J.map (MulAut.congr e).toMonoidHom = J.map (MulAut.congr e').toMonoidHom := by
  have hg : e' = e.trans (e.symm.trans e') := by
    ext x
    simp [MulEquiv.trans_apply]
  rw [hg]
  have hcomp : MulAut.congr (e.trans (e.symm.trans e')) =
      (MulAut.congr e).trans (MulAut.congr (e.symm.trans e')) := by
    ext φ x
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hcomp2 : ((MulAut.congr e).trans (MulAut.congr (e.symm.trans e'))).toMonoidHom =
      (MulAut.congr (e.symm.trans e')).toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
    ext φ
    rfl
  rw [hcomp, hcomp2, ← Subgroup.map_map]
  haveI : (J.map (MulAut.congr e).toMonoidHom).Normal :=
    hJ.map _ (MulAut.congr e).surjective
  have hconj : (MulAut.congr (e.symm.trans e')).toMonoidHom =
      MulAut.conj (e.symm.trans e') := by
    ext φ x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [hconj, Subgroup.Normal.map_conj_eq]

theorem recipeID_iff_hatAut (φ : MulAut (RecipeGroup .E6 K)) :
    φ ∈ RecipeID .E6 K ↔ MulAut.congr (recipeEquiv .E6 K) φ ∈ (hatAut .E6 K).range := by
  let J : Subgroup (MulAut (RecipeGroup .E6 K)) :=
    Subgroup.closure (LargeEvenInnSet (RecipeGroup .E6 K) ∪
      LargeEvenChevDiagImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
  have hJ : (J : Set (MulAut (RecipeGroup .E6 K))) = RecipeID .E6 K := rfl
  obtain ⟨Ψ, hΨ⟩ := TableBExc.E6Three.exists_quot_E6 K
  have hJker : J = Ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, hΨ x]
    exact Iff.rfl
  have hJnormal : J.Normal := hJker.symm ▸ inferInstance
  obtain ⟨T, hTx, hTy⟩ := InnerDiagE6.exists_largeEvenChevEquiv (τ := .E6) (K := K)
  have hZ : Subgroup.center ↥(LargeEvenChevGroup (Tag.cartan .E6) K) = ⊥ :=
    InnerDiagE6.center_eq_bot_of_mulEquiv T
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := K))
  let e₀ : RecipeGroup .E6 K ≃* adjointGroup .E6 K :=
    (centerQuotEquivOfBot hZ).trans T.symm
  have congr_diag : ∀ {ψ : MulAut (RecipeGroup .E6 K)} {a : Fin (Tag.rank .E6) → Kˣ},
      TableB.IsDiagOf (LargeEvenChevH Tag.E6.cartan K false) ψ a →
      MulAut.congr e₀ ψ = rootDiagAutHom .E6 K a := by
    intro ψ a hψa
    rw [MulAut.congr_apply]
    refine MulEquiv.ext fun x => ?_
    change e₀ (ψ (e₀.symm x)) = rootDiagAutHom Tag.E6 K a x
    have hsymm : e₀.symm x = LargeEvenCenterMk (LargeEvenChevH Tag.E6.cartan K false) (T x) := rfl
    rw [hsymm, hψa.2 (T x) (hψa.1 (T x) (T x).2)]
    have hcoe : e₀ (LargeEvenCenterMk (LargeEvenChevH Tag.E6.cartan K false)
        ⟨TableB.diagHom Tag.E6.cartan K a * (T x) * (TableB.diagHom Tag.E6.cartan K a)⁻¹,
          hψa.1 (T x) (T x).2⟩) =
        T.symm ⟨TableB.diagHom Tag.E6.cartan K a * (T x) *
          (TableB.diagHom Tag.E6.cartan K a)⁻¹, hψa.1 (T x) (T x).2⟩ := rfl
    rw [hcoe, MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    exact (MpStdE6.transfer_conj_rootDiag .E6 T hTx hTy a x).symm
  have hInn : (MulAut.congr e₀).toMonoidHom '' LargeEvenInnSet (RecipeGroup .E6 K) =
      ↑(MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
    ext x
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨e₀ r, (mulAut_congr_conj e₀ r).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨MulAut.conj (e₀.symm c), ⟨e₀.symm c, rfl⟩, by
        change MulAut.congr e₀ (MulAut.conj (e₀.symm c)) = MulAut.conj c
        rw [mulAut_congr_conj, MulEquiv.apply_symm_apply]⟩
  have hDiag : (MulAut.congr e₀).toMonoidHom '' LargeEvenChevDiagImage Tag.E6.cartan K
      (LargeEvenChevH Tag.E6.cartan K false) = ↑(rootDiagAutHom .E6 K).range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hy
      exact ⟨a, (congr_diag ha).symm⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨y, hyD, hy⟩ := InnerDiagE6.exists_diagAut (A := (Tag.cartan .E6)) (K := K) hZ a
        (fun h hh => InnerDiagE6.diagHom_conj_mem .E6 a hh)
        (fun h hh => InnerDiagE6.diagHom_inv_conj_mem .E6 a hh)
      exact ⟨y, hyD, congr_diag ⟨fun h hh => InnerDiagE6.diagHom_conj_mem .E6 a hh,
        fun h _ => hy h⟩⟩
  have hmap₀ : J.map (MulAut.congr e₀).toMonoidHom = (hatAut .E6 K).range := by
    dsimp only [J]
    rw [MonoidHom.map_closure, Set.image_union, hInn, hDiag, Subgroup.closure_union,
      Subgroup.closure_eq, Subgroup.closure_eq, NoOffE6Three.hatAut_range_eq_sup]
  have hmap : J.map (MulAut.congr (recipeEquiv .E6 K)).toMonoidHom = (hatAut .E6 K).range := by
    rw [← map_congr_eq_of_normal J hJnormal e₀ (recipeEquiv .E6 K), hmap₀]
  show φ ∈ J ↔ MulAut.congr (recipeEquiv .E6 K) φ ∈ (hatAut .E6 K).range
  constructor
  · intro hx
    exact hmap ▸ ⟨φ, hx, rfl⟩
  · rintro hx
    rw [← hmap] at hx
    rcases hx with ⟨y, hy, hyφ⟩
    rwa [← (MulAut.congr (recipeEquiv .E6 K)).injective hyφ]

end CFSG.StandardType.E6ThreeModel
