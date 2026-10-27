module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

private theorem ggNbrLSideSL3Witness_aux {G T : Type} [Group G] [Group T] (π : G →* T)
    (hπ : Function.Injective π) {K : Type} [Field K] [Finite K] (S : Subgroup G)
    (φ : ↥S ≃* Matrix.SpecialLinearGroup (Fin 3) K) (c : G) (hc : ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (M : Matrix.GeneralLinearGroup (Fin 3) K)
    (hconj : ∀ s : ↥S, φ ⟨c * s * c⁻¹, hc s s.2⟩ =
      CatalogueBHigherLinearAction.slConjugation 3 K M (φ s))
    (α : MulAut (↥(S.map π) ⧸ Subgroup.center ↥(S.map π)))
    (hα : GGNbrLSideInduces (MulAut.conj (π c)) (S.map π) α) :
    GGInnDiagPSL3 (Nat.card K) (↥(S.map π) ⧸ Subgroup.center ↥(S.map π)) α := by
  let ψ : Matrix.SpecialLinearGroup (Fin 3) K →* T :=
    π.comp (S.subtype.comp φ.symm.toMonoidHom)
  have hψi : Function.Injective ψ :=
    hπ.comp (Subtype.val_injective.comp φ.symm.injective)
  have hψr : ψ.range = S.map π := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 φ.symm.surjective]
    simp [Subgroup.map_top]
  let eJ' : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(S.map π) :=
    (MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψr)
  have heJ'_apply : ∀ g, (eJ' g : T) = ψ g := fun _ => rfl
  let e : (↥(S.map π) ⧸ Subgroup.center ↥(S.map π)) ≃* projectiveSL 3 K :=
    QuotientGroup.congr (Subgroup.center ↥(S.map π)) (scalars 3 K) eJ'.symm
      ((Subgroup.map_center_eq eJ'.symm).trans (scalars_eq_center 3 K).symm)
  have he_mk : ∀ j : ↥(S.map π), e (QuotientGroup.mk j) = QuotientGroup.mk (eJ'.symm j) := by
    intro j
    change e (QuotientGroup.mk' (Subgroup.center ↥(S.map π)) j) =
      QuotientGroup.mk' (scalars 3 K) (eJ'.symm j)
    rw [QuotientGroup.congr_mk']
  refine ggInnDiagPSL3_of_conjAut_apply (F := K) (Q := Nat.card K) rfl e M ?_
  intro x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨j', hj'val, hj'α⟩ := hα j
  set g : Matrix.SpecialLinearGroup (Fin 3) K := eJ'.symm j with hg
  have hj : (j : T) = ψ g := by
    have h1 := heJ'_apply g
    rwa [show eJ' g = j from eJ'.apply_symm_apply j] at h1
  have hs : φ.symm (CatalogueBHigherLinearAction.slConjugation 3 K M g) =
      ⟨c * (φ.symm g : G) * c⁻¹, hc _ (φ.symm g).2⟩ := by
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hconj, MulEquiv.apply_symm_apply]
  have hψ_conj : ψ (CatalogueBHigherLinearAction.slConjugation 3 K M g) =
      (π c) * ψ g * (π c)⁻¹ := by
    show π (S.subtype (φ.symm (CatalogueBHigherLinearAction.slConjugation 3 K M g))) = _
    rw [hs]
    show π (c * (φ.symm g : G) * c⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rfl
  have hj'_eq : j' = eJ' (CatalogueBHigherLinearAction.slConjugation 3 K M g) := by
    apply Subtype.ext
    rw [hj'val]
    simp only [heJ'_apply, hψ_conj, MulAut.conj_apply, hj]
  have hs' : eJ'.symm j' = CatalogueBHigherLinearAction.slConjugation 3 K M g := by
    rw [hj'_eq, MulEquiv.symm_apply_apply]
  rw [hj'α, he_mk j', he_mk j, hs']
  exact (conjAut_proj M g).symm

theorem ggNbrLSideSL3Witness {G T : Type} [Group G] [Group T] (π : G →* T)
    (hπ : Function.Injective π) {K : Type} [Field K] [Finite K] {a : ℕ} (ha : a = 3)
    (S : Subgroup G) (φ : ↥S ≃* ↥(StatedSL a K)) (c : G) (hc : ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (M : Matrix.GeneralLinearGroup (Fin a) K)
    (hconj : ∀ s : ↥S, ((φ ⟨c * s * c⁻¹, hc s s.2⟩ : ↥(StatedSL a K)) :
      Matrix.GeneralLinearGroup (Fin a) K) =
        M * ((φ s : ↥(StatedSL a K)) : Matrix.GeneralLinearGroup (Fin a) K) * M⁻¹)
    (α : MulAut (↥(S.map π) ⧸ Subgroup.center ↥(S.map π)))
    (hα : GGNbrLSideInduces (MulAut.conj (π c)) (S.map π) α) :
    GGInnDiagPSL3 (Nat.card K) (↥(S.map π) ⧸ Subgroup.center ↥(S.map π)) α := by
  subst ha
  have hcoe : ∀ x : ↥(StatedSL 3 K),
      ((LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm x : Matrix (Fin 3) (Fin 3) K) =
        ((x : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun x => by
    rw [← LowTwoRank.specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
  have hcoe' : ∀ s : ↥S,
      (((φ.trans (LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm) s :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((φ s : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    fun s => hcoe (φ s)
  refine ggNbrLSideSL3Witness_aux π hπ S
    (φ.trans (LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm) c hc M (fun s => ?_) α hα
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, hcoe', hcoe', hconj]
  simp only [Units.val_mul]

end CFSG.StandardType

end
