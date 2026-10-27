module

import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Matrix

private abbrev Q4 : (SmallOmegaFour.ι4 → ZMod 2) → ZMod 2 :=
  StatedQuadMinus 2 (ZMod 2) 1 1

private theorem isometryCore_Q4_eq_O4 :
    CFSG.MatrixModel.isometryCore Q4 = SmallOmegaFour.O4 :=
  Subgroup.closure_eq SmallOmegaFour.O4

private noncomputable def eps : Equiv.Perm (Fin 5) ≃* ↥(CFSG.MatrixModel.isometryCore Q4) :=
  SmallOmegaFour.o4MulEquivPerm.symm.trans
    (MulEquiv.subgroupCongr isometryCore_Q4_eq_O4.symm)

private theorem eps_coe (σ : Equiv.Perm (Fin 5)) :
    ((eps σ : ↥(CFSG.MatrixModel.isometryCore Q4)) : GL SmallOmegaFour.ι4 (ZMod 2)) =
      ((SmallOmegaFour.o4MulEquivPerm.symm σ : SmallOmegaFour.O4) :
        GL SmallOmegaFour.ι4 (ZMod 2)) :=
  rfl

private theorem eps_mulVec_sing (σ : Equiv.Perm (Fin 5)) (i : Fin 5) :
    (((eps σ : ↥(CFSG.MatrixModel.isometryCore Q4)) :
        GL SmallOmegaFour.ι4 (ZMod 2)).1) *ᵥ SmallOmegaFour.sing i =
      SmallOmegaFour.sing (σ i) := by
  rw [eps_coe]
  have h := SmallOmegaFour.toPerm_spec (SmallOmegaFour.o4MulEquivPerm.symm σ) i
  have hσ : SmallOmegaFour.toPerm (SmallOmegaFour.o4MulEquivPerm.symm σ) = σ :=
    SmallOmegaFour.o4MulEquivPerm.apply_symm_apply σ
  rwa [hσ] at h

private noncomputable def phi :
    G6.PermMod 5 →* Multiplicative (SmallOmegaFour.ι4 → ZMod 2) where
  toFun x := Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i • SmallOmegaFour.sing i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => add_smul _ _ _

private theorem phi_inj_on_core :
    ∀ x : Fin 5 → ZMod 2, (∑ i, x i = 0) →
      (∑ i, x i • SmallOmegaFour.sing i = 0) → x = 0 := by
  decide +kernel

private theorem phi_surj_aux :
    ∀ v : SmallOmegaFour.ι4 → ZMod 2, ∃ x : Fin 5 → ZMod 2,
      (∑ i, x i = 0) ∧ (∑ i, x i • SmallOmegaFour.sing i = v) := by
  decide +kernel

private noncomputable def phi0 :
    ↥(G6.coreMod 5) →* ↥(⊤ : Subgroup (Multiplicative (SmallOmegaFour.ι4 → ZMod 2))) :=
  (phi.comp (G6.coreMod 5).subtype).codRestrict ⊤ fun _ => Subgroup.mem_top _

private theorem phi0_surjective : Function.Surjective phi0 := by
  intro y
  obtain ⟨x, hx, hv⟩ := phi_surj_aux (Multiplicative.toAdd y.1)
  refine ⟨⟨Multiplicative.ofAdd x, G6.mem_coreMod.mpr hx⟩, ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  change (∑ i, x i • SmallOmegaFour.sing i) = Multiplicative.toAdd y.1
  exact hv

private theorem phi_eq_one_iff (x : ↥(G6.coreMod 5)) :
    phi (x : G6.PermMod 5) = 1 ↔ (x : G6.PermMod 5) = 1 := by
  constructor
  · intro hx
    have h0 : ∑ i, Multiplicative.toAdd (x : G6.PermMod 5) i • SmallOmegaFour.sing i = 0 := by
      have h := congrArg Multiplicative.toAdd hx
      simpa [phi] using h
    have hz := phi_inj_on_core (Multiplicative.toAdd (x : G6.PermMod 5))
      (G6.mem_coreMod.mp x.2) h0
    apply Multiplicative.toAdd.injective
    simpa using hz
  · intro hx
    rw [hx, map_one]

private theorem allOnes_five_not_mem_coreMod : G6.allOnes 5 ∉ G6.coreMod 5 := by
  rw [G6.mem_coreMod]
  decide +kernel

private theorem symDn_five_ker : (FFModel.symDn 5).ker = ⊥ := by
  show Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥
  rw [eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  rw [Subgroup.mem_bot]
  rcases B5FinPerm.mem_zpowers_allOnes_iff.mp hz1 with h | h
  · exact h
  · exact absurd (h ▸ hz2) allOnes_five_not_mem_coreMod

private theorem permAct_apply_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : G6.PermMod n)
    (i : Fin n) :
    Multiplicative.toAdd (G6.permAct n σ x) i = Multiplicative.toAdd x (σ.symm i) :=
  G6.permAct_apply n σ x i

private theorem natAct_eps_phi (σ : Equiv.Perm (Fin 5)) (x : G6.PermMod 5) :
    natAct (CFSG.MatrixModel.isometryCore Q4) (eps σ) (phi x) =
      phi (G6.permAct 5 σ x) := by
  apply Multiplicative.toAdd.injective
  show ((eps σ : ↥(CFSG.MatrixModel.isometryCore Q4)) :
      GL SmallOmegaFour.ι4 (ZMod 2)).1 *ᵥ
        (∑ i, Multiplicative.toAdd x i • SmallOmegaFour.sing i) =
    ∑ i, Multiplicative.toAdd (G6.permAct 5 σ x) i • SmallOmegaFour.sing i
  rw [Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, eps_mulVec_sing]
  have hR : (∑ i, Multiplicative.toAdd (G6.permAct 5 σ x) i • SmallOmegaFour.sing i) =
      ∑ i, (fun j => Multiplicative.toAdd x j • SmallOmegaFour.sing (σ j)) (σ.symm i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [permAct_apply_symm, Equiv.apply_symm_apply]
  rw [hR]
  exact (Equiv.sum_comp σ.symm
    (fun j => Multiplicative.toAdd x j • SmallOmegaFour.sing (σ j))).symm

theorem s15k_jp_o4minus_zmod {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (h : (FFModel.nat (CFSG.MatrixModel.isometryCore
      (StatedQuadMinus 2 (ZMod 2) 1 1))).Realizes J R ⊥) : SymmetricNatural J R ⊥ 5 := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨π.comp eps.toMonoidHom, ?_⟩
  refine FFModel.RealizesVia.of_surjHom (FFModel.symDn_isActionModel 5) hπ
    eps.toMonoidHom eps.surjective phi0 phi0_surjective ?_ ?_
  · intro σ m hm
    exact (natAct_eps_phi σ m.1).symm
  · intro m
    rw [symDn_five_ker]
    exact phi_eq_one_iff m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
