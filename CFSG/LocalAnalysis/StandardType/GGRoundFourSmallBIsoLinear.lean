module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBIso
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open scoped commutatorElement

section PSL

variable {n : ℕ} {K : Type} [Field K]

theorem fieldAut_mul_dualAut_comm (σ : K ≃+* K) :
    fieldAut n K σ * dualAut n K = dualAut n K * fieldAut n K σ := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have h1 := htrans.2.2.2.2.2.1 σ
  have h2 := htrans.2.2.2.1
  calc fieldAut n K σ * dualAut n K
      = dualAut n K * fieldAut n K σ * dualAut n K * dualAut n K := by rw [h1]
    _ = dualAut n K * fieldAut n K σ * (dualAut n K * dualAut n K) := by group
    _ = dualAut n K * fieldAut n K σ := by rw [h2, mul_one]

variable [Finite K]

theorem commutator_top_le_linearAutGroup (hn : 3 ≤ n) :
    ⁅(⊤ : Subgroup (MulAut (projectiveSL n K))), ⊤⁆ ≤ linearAutGroup n K := by
  rw [Subgroup.commutator_le]
  rintro α - β -
  rw [commutatorElement_def]
  exact OuterDerived.commutator_mem_linearAutGroup hn α β

variable [CharP K 2]

theorem conjAut_mem_ggInndiagComm (A : GL (Fin n) K) :
    conjAut n K A ∈ ggInndiagComm (projectiveSL n K) := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  set φ : K ≃+* K := frobeniusEquiv K 2 with hφ
  set M : GL (Fin n) K := GeneralLinearGroup.map (φ : K →+* K) A with hM
  have h1 : ⁅fieldAut n K φ, conjAut n K A⁆ = conjAut n K (M * A⁻¹) := by
    rw [commutatorElement_def, htrans.2.2.1 φ A, map_mul, map_inv]
  set S : GL (Fin n) K := A⁻¹ * (M * A⁻¹) with hS
  have hdM : GeneralLinearGroup.det M = GeneralLinearGroup.det A ^ 2 := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.val_det_apply]
    change ((φ : K →+* K).mapMatrix (A : Matrix (Fin n) (Fin n) K)).det = _
    rw [← RingHom.map_det]
    exact frobeniusEquiv_apply K 2 _
  have hdetS : GeneralLinearGroup.det S = 1 := by
    rw [hS, map_mul, map_mul, map_inv, hdM]
    group
  have hdetS' : (S : Matrix (Fin n) (Fin n) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hdetS, Units.val_one]
  obtain ⟨s, hs⟩ : ∃ s : SpecialLinearGroup (Fin n) K, SpecialLinearGroup.toGL s = S :=
    ⟨⟨S, hdetS'⟩, by ext; rfl⟩
  have h2 : conjAut n K A = ⁅fieldAut n K φ, conjAut n K A⁆ * (conjAut n K S)⁻¹ := by
    rw [h1, ← map_inv, ← map_mul]
    congr 1
    rw [hS]
    group
  rw [h2]
  refine Subgroup.mul_mem _ (commutator_mem_ggInndiagComm _ _)
    (Subgroup.inv_mem _ (range_conj_le_ggInndiagComm ?_))
  rw [← hs, conjAut_toGL]
  exact ⟨_, rfl⟩

theorem linearAutGroup_eq_ggInndiagComm (hn : 3 ≤ n) :
    linearAutGroup n K = ggInndiagComm (projectiveSL n K) := by
  refine le_antisymm ?_ (sup_le (standard_outer_quotients (n := n) (K := K)).1
    (commutator_top_le_linearAutGroup hn))
  rw [linearAutGroup_eq_range]
  rintro _ ⟨A, rfl⟩
  exact conjAut_mem_ggInndiagComm A

end PSL

section Recipe

variable {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggInndiagCommEq_linear (hd : 3 ≤ d) :
    GGInndiagCommEq (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  set c := MulAut.congr (TypeA.recipeEquiv d K) with hc
  have hmap : (ggInndiag (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)).map
        c.toMonoidHom = linearAutGroup d K := by
    apply le_antisymm
    · rw [ggInndiag, Subgroup.map_sup, map_congr_range_conj, MonoidHom.map_closure]
      refine sup_le (standard_outer_quotients (n := d) (K := K)).1 ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hφ
      change c φ ∈ linearAutGroup d K
      rw [← hA]
      exact conjAut_mem_linearAutGroup A
    · rw [linearAutGroup_eq_range]
      rintro _ ⟨A, rfl⟩
      exact ⟨c.symm (conjAut d K A), subset_ggInndiag (congr_symm_conjAut_mem A),
        c.apply_symm_apply _⟩
  show ggInndiag _ _ = ggInndiagComm _
  apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
  rw [hmap, linearAutGroup_eq_ggInndiagComm hd, map_congr_ggInndiagComm]

end Recipe

theorem recipeLinear_inndiagComm {d m : ℕ} (hd : 3 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ m) Q) :
    LargeEvenRecipeLinear d (2 ^ m) fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard GGInndiagCommEq R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => ggInndiagCommEq_linear hd⟩

@[expose] def GGInndiagCommLinearLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 2 ≤ lab.rank) ∨ (lab.tag = .D ∧ lab.rank = 3)

theorem largeEvenLabelAll_inndiagComm_linear {lab : LargeEvenLabel}
    (h : GGInndiagCommLinearLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  rcases h with ⟨h, hl⟩ | ⟨h, hl⟩
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h hl
    subst h
    intro Q hQ
    exact recipeLinear_inndiagComm (by dsimp only; omega) hQ
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h hl
    subst h hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    exact recipeLinear_inndiagComm (by omega) hQ

end CFSG.StandardType

end
