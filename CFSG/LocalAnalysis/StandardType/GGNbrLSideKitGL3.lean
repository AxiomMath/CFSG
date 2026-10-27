module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

private theorem range_eq_commutator_of_perfect {X B Ab : Type} [Group X] [Group B]
    [CommGroup Ab] (θ : X →* B) (hX : commutator X = ⊤) (D : B →* Ab) (hD : D.ker ≤ θ.range) :
    θ.range = commutator B := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map, ← hX, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · refine le_trans ?_ hD
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)

private theorem map_commutator_mulEquiv {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem range_comp_eq_commutator {G : Type} [Group G] {A : Subgroup G} {B X : Type}
    [Group B] [Group X] (φ : A ≃* B) (θ : X →* B) (hθ : θ.range = commutator B) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp θ)).range = ⁅A, A⁆ := by
  have h1 : (φ.symm.toMonoidHom.comp θ).range = commutator ↥A := by
    rw [MonoidHom.range_comp, hθ]
    exact map_commutator_mulEquiv φ.symm
  rw [MonoidHom.range_comp, h1]
  exact Subgroup.map_subtype_commutator A

private theorem range_toGL_eq_commutator {K : Type} [Field K] :
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range =
      commutator (GL (Fin 3) K) := by
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (m := 3) (by norm_num)
      (Or.inl (by norm_num))
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin 3) K) = ⊤ :=
    Group.isPerfect_def.mp hqSL.1
  let θ : Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K :=
    Matrix.SpecialLinearGroup.toGL
  have hθ : θ.range = commutator (GL (Fin 3) K) := by
    refine range_eq_commutator_of_perfect θ hperf
      (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ) fun g hg => ?_
    rw [MonoidHom.mem_ker] at hg
    have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have := congrArg Units.val hg
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    exact ⟨⟨g, hdet⟩, Units.ext rfl⟩
  exact hθ

theorem ggNbrLSideGL3Witness {G T : Type} [Group G] [Group T] (π : G →* T)
    (hπ : Function.Injective π) {K : Type} [Field K] [Finite K] (A : Subgroup G)
    (φ : ↥A ≃* GL (Fin 3) K) (c : ↥A)
    (α : MulAut (↥(⁅A, A⁆.map π) ⧸ Subgroup.center ↥(⁅A, A⁆.map π)))
    (hα : GGNbrLSideInduces (MulAut.conj (π (c : G))) (⁅A, A⁆.map π) α) :
    GGInnDiagPSL3 (Nat.card K) (↥(⁅A, A⁆.map π) ⧸ Subgroup.center ↥(⁅A, A⁆.map π)) α := by
  let θ : Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K :=
    Matrix.SpecialLinearGroup.toGL
  let ψ : Matrix.SpecialLinearGroup (Fin 3) K →* T :=
    π.comp (A.subtype.comp (φ.symm.toMonoidHom.comp θ))
  have hθ : θ.range = commutator (GL (Fin 3) K) := range_toGL_eq_commutator
  have hψi : Function.Injective ψ :=
    hπ.comp (Subtype.val_injective.comp
      (φ.symm.injective.comp Matrix.SpecialLinearGroup.toGL_injective))
  have hψr : ψ.range = ⁅A, A⁆.map π := by
    rw [MonoidHom.range_comp, range_comp_eq_commutator φ θ hθ]
  let eJ' : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(⁅A, A⁆.map π) :=
    (MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψr)
  have heJ'_apply : ∀ g, (eJ' g : T) = ψ g := fun _ => rfl
  let e : (↥(⁅A, A⁆.map π) ⧸ Subgroup.center ↥(⁅A, A⁆.map π)) ≃* projectiveSL 3 K :=
    QuotientGroup.congr (Subgroup.center ↥(⁅A, A⁆.map π)) (scalars 3 K) eJ'.symm
      ((Subgroup.map_center_eq eJ'.symm).trans (scalars_eq_center 3 K).symm)
  have he_mk : ∀ j : ↥(⁅A, A⁆.map π), e (QuotientGroup.mk j) = QuotientGroup.mk (eJ'.symm j) := by
    intro j
    change e (QuotientGroup.mk' (Subgroup.center ↥(⁅A, A⁆.map π)) j) =
      QuotientGroup.mk' (scalars 3 K) (eJ'.symm j)
    rw [QuotientGroup.congr_mk']
  refine ggInnDiagPSL3_of_conjAut_apply (F := K) (Q := Nat.card K) rfl e (φ c) ?_
  intro x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨j', hj'val, hj'α⟩ := hα j
  set g : Matrix.SpecialLinearGroup (Fin 3) K := eJ'.symm j with hg
  have hj : (j : T) = ψ g := by
    have h1 := heJ'_apply g
    rwa [show eJ' g = j from eJ'.apply_symm_apply j] at h1
  have hθg : θ (CatalogueBHigherLinearAction.slConjugation 3 K (φ c) g) =
      (φ c) * θ g * (φ c)⁻¹ := by
    apply Units.ext
    exact coe_slConjugation (φ c) g
  have hφsymm : φ.symm ((φ c) * θ g * (φ c)⁻¹) = c * φ.symm (θ g) * c⁻¹ := by
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hA : A.subtype (c * φ.symm (θ g) * c⁻¹) =
      (c : G) * A.subtype (φ.symm (θ g)) * (c : G)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have hψ_conj : ψ (CatalogueBHigherLinearAction.slConjugation 3 K (φ c) g) =
      (π c) * ψ g * (π c)⁻¹ := by
    show π (A.subtype (φ.symm (θ
      (CatalogueBHigherLinearAction.slConjugation 3 K (φ c) g)))) = _
    rw [hθg, hφsymm, hA]
    simp only [map_mul, map_inv]
    rfl
  have hj'_eq : j' = eJ' (CatalogueBHigherLinearAction.slConjugation 3 K (φ c) g) := by
    apply Subtype.ext
    rw [hj'val]
    simp only [heJ'_apply, hψ_conj, MulAut.conj_apply, hj]
  have hs : eJ'.symm j' = CatalogueBHigherLinearAction.slConjugation 3 K (φ c) g := by
    rw [hj'_eq, MulEquiv.symm_apply_apply]
  rw [hj'α, he_mk j', he_mk j, hs]
  exact (conjAut_proj (φ c) g).symm

end CFSG.StandardType
