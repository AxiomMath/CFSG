module

public import CFSG.Quasithin.Background.P4GLAut
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.Quasithin.SteinbergCD

open CFSG Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
open CFSG.RankThree.GroupTheory.SteinbergBY (map_conj_eq_of_mem_normalizer
  mem_normalizer_of_map_conj_eq)

section General

variable {G : Type*} [Group G]

theorem mulAut_mul_conj_mul_inv (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  ext x
  simp [MulAut.conj_apply]

end General

section Binary

variable {n : ℕ}

theorem injective_conj_binarySL (n : ℕ) :
    Function.Injective (MulAut.conj : SpecialLinearGroup (Fin n) (ZMod 2) →*
      MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : g ∈ center (SpecialLinearGroup (Fin n) (ZMod 2)) := by
    rw [mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin n) (ZMod 2)) => φ h)
      (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rwa [← scalars_eq_center, QuasithinUnique.Setup.Family.scalars_zmod_two] at hc

theorem graphAut_eq_conj_mul_slGraphAut (n : ℕ) :
    ∃ w : SpecialLinearGroup (Fin n) (ZMod 2),
      graphAut n = MulAut.conj w * ComponentClassification.CatalogueBGraphForm.slGraphAut n
        (ZMod 2) := by
  have hdet : (permMatrix n (ZMod 2) Fin.revPerm).det = 1 := by
    rw [det_permMatrix]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;>
      rw [h] <;> decide
  obtain ⟨w, hw⟩ : ∃ w : SpecialLinearGroup (Fin n) (ZMod 2),
      (w : Matrix (Fin n) (Fin n) (ZMod 2)) = permMatrix n (ZMod 2) Fin.revPerm :=
    ⟨⟨_, hdet⟩, rfl⟩
  have hww : w⁻¹ = w := by
    have h : ((w * w : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((1 : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hw,
        permMatrix_mul_permMatrix, show (Fin.revPerm : Equiv.Perm (Fin n)) * Fin.revPerm = 1 from
          Equiv.ext fun x => Fin.rev_rev x, permMatrix_one']
    exact inv_eq_of_mul_eq_one_right (Subtype.ext h)
  refine ⟨w, MulEquiv.ext fun g => Subtype.ext ?_⟩
  change ((graphAut n g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
    (((MulAut.conj w * ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)) g :
      SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
  rw [MulAut.mul_apply, MulAut.conj_apply, hww, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_graphAut, revMatrix_inv,
    ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, hw]

theorem aut_eq_conj_or_conj_mul_graphAut (hn : 3 ≤ n)
    (α : MulAut (SpecialLinearGroup (Fin n) (ZMod 2))) :
    (∃ g, α = MulAut.conj g) ∨ ∃ g, α = MulAut.conj g * graphAut n := by
  obtain ⟨w, hw⟩ := graphAut_eq_conj_mul_slGraphAut n
  have hconj : ∀ A : GL (Fin n) (ZMod 2), ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      ComponentClassification.CatalogueBHigherLinearAction.slConjugation n (ZMod 2) A =
        MulAut.conj g := by
    intro A
    refine ⟨(G11.P4GL.slEquiv n).symm A, MulEquiv.ext fun h => ?_⟩
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hA : Matrix.SpecialLinearGroup.toGL ((G11.P4GL.slEquiv n).symm A) = A :=
      (G11.P4GL.slEquiv n).apply_symm_apply A
    rw [ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      MulAut.conj_apply, map_mul, map_mul, map_inv, hA]
  rcases G11.P4GL.aut_SL_cases hn α with ⟨A, hA⟩ | ⟨A, hA⟩
  · obtain ⟨g, hg⟩ := hconj A
    exact Or.inl ⟨g, hA.trans hg⟩
  · obtain ⟨g, hg⟩ := hconj A
    refine Or.inr ⟨g * w⁻¹, ?_⟩
    rw [hA, hg, hw, map_mul, map_inv, mul_assoc, ← mul_assoc (MulAut.conj w)⁻¹, inv_mul_cancel,
      one_mul]

theorem graphAut_ne_conj (hn : 3 ≤ n) (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    graphAut n ≠ MulAut.conj g := by
  intro h
  have hU : (unitriangular n (ZMod 2)).map (MulAut.conj g).toMonoidHom =
      unitriangular n (ZMod 2) := by
    rw [← h]
    exact map_graphAut_unitriangular
  have hgU : g ∈ unitriangular n (ZMod 2) := by
    have hg := mem_normalizer_of_map_conj_eq hU
    rwa [normalizer_unitriangular, upperTriangular_eq_unitriangular] at hg
  have hM := map_graphAut_parabolic (n := n) (j := 1) le_rfl (by omega)
  rw [h, map_conj_eq_of_mem_normalizer
    (le_normalizer (unitriangular_le_flagStabilizer _ hgU))] at hM
  have hr := reflection_mem_parabolic (n := n) (j := n - 1) (by omega) (by omega)
  rw [← hM] at hr
  have := eq_of_reflection_mem_parabolic (j := 1) (by omega) (by omega) hr
  omega

end Binary

end SteinbergCD

open Subgroup Matrix SteinbergCD
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic
open CFSG.RankThree.GroupTheory.SteinbergBY (map_conj_eq_of_mem_normalizer)

end CFSG.Quasithin
