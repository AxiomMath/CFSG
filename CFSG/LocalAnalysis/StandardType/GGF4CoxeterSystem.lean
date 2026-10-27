module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import Mathlib.GroupTheory.Coxeter.Inversion
import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] {Bs : Subgroup G}

noncomputable def ggF4CoxeterSystem {A : Subgroup (MulAut ↥Bs)} {ι : Type} (e' : Fin 4 ≃ ι)
    (e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A) : CoxeterSystem CoxeterMatrix.F₄ ↥A :=
  CoxeterMatrix.F₄.toCoxeterSystem.map (((CoxeterMatrix.F₄.reindexGroupEquiv e').symm).trans e)

@[simp] theorem ggF4CoxeterSystem_simple {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    (e' : Fin 4 ≃ ι) (e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A) (i : Fin 4) :
    (ggF4CoxeterSystem e' e).simple i =
      e ((CoxeterMatrix.F₄.reindex e').simple (e' i)) := by
  simp [ggF4CoxeterSystem, CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]

theorem ggF4CoxeterSystem_isReflection_iff {A : Subgroup (MulAut ↥Bs)} {ι : Type} [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hNT : GGNoTransvection p Bs) (hAind : A ≤ ggInduced ⊤ Bs) (e' : Fin 4 ≃ ι)
    {e : (CoxeterMatrix.F₄.reindex e').Group ≃* ↥A}
    (hP : GGCoxeterPres p A (CoxeterMatrix.F₄.reindex e') e) :
    ∀ a : ↥A, (ggF4CoxeterSystem e' e).IsReflection a ↔ GGIsReflection p (a : MulAut ↥Bs) := by
  have : Fintype ι := Fintype.ofEquiv (Fin 4) e'
  have hG2 : ¬ ∃ e'' : Fin 2 ≃ ι,
      CoxeterMatrix.F₄.reindex e' = CoxeterMatrix.G₂.reindex e'' := by
    rintro ⟨e'', -⟩
    have h := Fintype.card_congr (e''.trans e'.symm)
    simp at h
  intro a
  constructor
  · rintro ⟨w, i, hw⟩
    have hsimple : (ggF4CoxeterSystem e' e).simple i =
        e ((CoxeterMatrix.F₄.reindex e').simple (e' i)) :=
      ggF4CoxeterSystem_simple e' e i
    have hcoe : ((w * (ggF4CoxeterSystem e' e).simple i * w⁻¹ : ↥A) : MulAut ↥Bs) =
        (w : MulAut ↥Bs) * (((ggF4CoxeterSystem e' e).simple i : ↥A) : MulAut ↥Bs) *
          (w : MulAut ↥Bs)⁻¹ := by
      simp
    rw [hw, hcoe, hsimple]
    exact (hP.2 (e' i)).conj (w : MulAut ↥Bs)
  · intro hr
    obtain ⟨i, g, hg⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hBs hNT A
      hAind ι (CoxeterMatrix.F₄.reindex e') hP.1 hG2 e hP.2 a hr
    refine ⟨e g, e'.symm i, ?_⟩
    have hsimple : (ggF4CoxeterSystem e' e).simple (e'.symm i) =
        e ((CoxeterMatrix.F₄.reindex e').simple i) := by
      simp
    rw [hsimple, hg, map_mul, map_mul, map_inv]

theorem ggF4_exists_coxeterSystem {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAind : A ≤ ggInduced ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥A} (hP : GGCoxeterPres p A M e) (hF : GGIsWeylMatrixF4 M) :
    ∃ cs : CoxeterSystem CoxeterMatrix.F₄ ↥A,
      ∀ a : ↥A, cs.IsReflection a ↔ GGIsReflection p (a : MulAut ↥Bs) := by
  obtain ⟨e', rfl⟩ := hF
  exact ⟨ggF4CoxeterSystem e' e,
    ggF4CoxeterSystem_isReflection_iff hp hp2 hBs hNT hAind e' hP⟩

end CFSG.StandardType

end
