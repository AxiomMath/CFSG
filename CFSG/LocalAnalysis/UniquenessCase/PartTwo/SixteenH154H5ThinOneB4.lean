module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B5FinTransport
import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.GF2n.Stroth80 (reindexGL sumFinTwo map_reindexGL_statedSp_one coe_reindexGL)
open scoped Matrix

variable {W : Type} [CommGroup W]

private noncomputable def s16h_spEquivSL (K : Type) [Field K] :
    ↥(StatedSp 1 K) ≃* ↥(StatedSL 2 K) :=
  (MulEquiv.subgroupMap (reindexGL (K := K) sumFinTwo) (StatedSp 1 K)).trans
    (MulEquiv.subgroupCongr (map_reindexGL_statedSp_one (K := K)))

private noncomputable def s16h_slEquivSp (K : Type) [Field K] :
    ↥(StatedSL 2 K) ≃* ↥(StatedSp 1 K) :=
  (s16h_spEquivSL K).symm

private theorem s16h_spEquivSL_apply {K : Type} [Field K] (γ : ↥(StatedSp 1 K)) :
    ((s16h_spEquivSL K γ : ↥(StatedSL 2 K)) : GL (Fin 2) K) =
      reindexGL sumFinTwo (γ : GL (Fin 1 ⊕ Fin 1) K) := by
  rfl

private theorem s16h_slEquivSp_apply {K : Type} [Field K] (γ : ↥(StatedSL 2 K)) :
    ((s16h_slEquivSp K γ : ↥(StatedSp 1 K)) : GL (Fin 1 ⊕ Fin 1) K) =
      (reindexGL (K := K) sumFinTwo).symm (γ : GL (Fin 2) K) := by
  have h2 : s16h_spEquivSL K (s16h_slEquivSp K γ) = γ := by
    simp [s16h_slEquivSp]
  have h := s16h_spEquivSL_apply (K := K) (s16h_slEquivSp K γ)
  rw [h2] at h
  have h' : (reindexGL (K := K) sumFinTwo).symm (γ : GL (Fin 2) K) =
      ((s16h_slEquivSp K γ : ↥(StatedSp 1 K)) : GL (Fin 1 ⊕ Fin 1) K) := by
    rw [h, MulEquiv.symm_apply_apply]
  exact h'.symm

private theorem s16h_reindexGL_symm_coe {ι ι' : Type} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] {K : Type} [Field K] (e : ι ≃ ι') (A : GL ι' K) :
    (((reindexGL e).symm A : GL ι K) : Matrix ι ι K) =
      (A : Matrix ι' ι' K).submatrix e e := by
  have h := coe_reindexGL e ((reindexGL e).symm A)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  simp

private noncomputable def s16h_ambSLtoSpAdd (K : Type) [Field K] :
    (Fin 2 → K) ≃+ (Fin 1 ⊕ Fin 1 → K) :=
  (LinearEquiv.funCongrLeft K K sumFinTwo).toAddEquiv

private noncomputable def s16h_ambSLtoSp (K : Type) [Field K] :
    Multiplicative (Fin 2 → K) ≃* Multiplicative (Fin 1 ⊕ Fin 1 → K) :=
  (s16h_ambSLtoSpAdd K).toMultiplicative

private theorem s16h_ambSLtoSp_apply {K : Type} [Field K]
    (x : Multiplicative (Fin 2 → K)) :
    s16h_ambSLtoSp K x =
      Multiplicative.ofAdd (s16h_ambSLtoSpAdd K (Multiplicative.toAdd x)) := rfl

private theorem s16h_ambSLtoSpAdd_mulVec {K : Type} [Field K] (γ : ↥(StatedSL 2 K))
    (v : Fin 2 → K) :
    s16h_ambSLtoSpAdd K (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
      (((s16h_slEquivSp K γ : ↥(StatedSp 1 K)) : GL (Fin 1 ⊕ Fin 1) K) :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) *ᵥ s16h_ambSLtoSpAdd K v := by
  rw [s16h_slEquivSp_apply, s16h_reindexGL_symm_coe, s16h_ambSLtoSpAdd,
    LinearEquiv.coe_toAddEquiv]
  have hcomp : ∀ w : Fin 2 → K,
      LinearEquiv.funCongrLeft K K sumFinTwo w = w ∘ sumFinTwo := by
    intro w
    funext i
    simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  change LinearEquiv.funCongrLeft K K sumFinTwo
      (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) =
    (((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).submatrix sumFinTwo sumFinTwo) *ᵥ
      LinearEquiv.funCongrLeft K K sumFinTwo v
  rw [hcomp, hcomp, Matrix.submatrix_mulVec_equiv]
  funext i
  simp

private theorem s16h_ambSLtoSp_natAct {K : Type} [Field K] (γ : ↥(StatedSL 2 K))
    (x : Multiplicative (Fin 2 → K)) :
    s16h_ambSLtoSp K (natAct (StatedSL 2 K) γ x) =
      natAct (StatedSp 1 K) (s16h_slEquivSp K γ) (s16h_ambSLtoSp K x) := by
  simp only [natAct, s16h_ambSLtoSp_apply, toAdd_ofAdd]
  rw [s16h_ambSLtoSpAdd_mulVec]

theorem s16h_H5_rowSL2_of_isSpn_two [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {a : ℕ} (h : IsSpn ↥L 2 a)
    (hN : NatSpn L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 a) :
    s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) a := by
  obtain ⟨-, K, hF, hFin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  refine ⟨?_, ?_⟩
  · exact ⟨K, hF, hFin, hKcard, ⟨e.trans (s16h_slEquivSp K).symm⟩⟩
  · obtain ⟨-, K', hF', hFin', hKcard', hReal⟩ := hN
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    have hReal' : (FFModel.nat (StatedSp 1 K')).Realizes L (commSub ⊤ L)
        (commSub ⊤ L ⊓ fixV L) := by simpa using hReal
    obtain ⟨π, hπ⟩ := hReal'
    let θ : ↥(StatedSL 2 K') →* ↥(StatedSp 1 K') := (s16h_slEquivSp K').toMonoidHom
    let Ê : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K'))) ≃*
        ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K'))) :=
      (Subgroup.topEquiv.trans (s16h_ambSLtoSp K')).trans Subgroup.topEquiv.symm
    refine ⟨K', hF', hFin', hKcard', ⟨π.comp θ, ?_⟩⟩
    refine FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel (StatedSL 2 K')) hπ θ
      (s16h_slEquivSp K').surjective Ê.toMonoidHom Ê.surjective ?_ ?_
    · intro γ m _hm
      simp only [FFModel.nat] at m
      have h1 : ∀ y : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K'))),
          ((Ê.toMonoidHom y : ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K')))) :
            Multiplicative (Fin 1 ⊕ Fin 1 → K')) =
            s16h_ambSLtoSp K' (y : Multiplicative (Fin 2 → K')) := by
        intro y
        simp [Ê]
      change ((Ê.toMonoidHom ⟨natAct (StatedSL 2 K') γ (m : Multiplicative (Fin 2 → K')),
          Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K')))) :
          Multiplicative (Fin 1 ⊕ Fin 1 → K')) =
        natAct (StatedSp 1 K') (θ γ)
          ((Ê.toMonoidHom m : ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K')))) :
            Multiplicative (Fin 1 ⊕ Fin 1 → K'))
      rw [h1, h1]
      exact s16h_ambSLtoSp_natAct (K := K') γ (m : Multiplicative (Fin 2 → K'))
    · intro m
      simp only [FFModel.nat] at m
      have h1 : ∀ y : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K'))),
          ((Ê.toMonoidHom y : ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K')))) :
            Multiplicative (Fin 1 ⊕ Fin 1 → K')) =
            s16h_ambSLtoSp K' (y : Multiplicative (Fin 2 → K')) := by
        intro y
        simp [Ê]
      change ((Ê.toMonoidHom m : ↥(⊤ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K')))) :
          Multiplicative (Fin 1 ⊕ Fin 1 → K')) ∈
          (⊥ : Subgroup (Multiplicative (Fin 1 ⊕ Fin 1 → K'))) ↔
        (m : Multiplicative (Fin 2 → K')) ∈ (⊥ : Subgroup (Multiplicative (Fin 2 → K')))
      rw [Subgroup.mem_bot, Subgroup.mem_bot, h1]
      exact MulEquiv.map_eq_one_iff (s16h_ambSLtoSp K')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
