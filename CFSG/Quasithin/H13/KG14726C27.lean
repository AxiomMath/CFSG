module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.H13.KG14726Core

public noncomputable section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Subgroup KG14726

namespace KG14726

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def quotientPCoreEquiv {K M : Type*} [Group K] [Group M] (α : K →* M)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 K) : K ⧸ CFSG.pCore 2 K ≃* M :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

@[expose] def quotientCenterEquivSelf (hc : center X = ⊥) : X ⧸ center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

theorem center_eq_bot_of_mulEquiv_simple (hqs : CFSG.IsQuasisimple X) [IsSimpleGroup Y]
    (e : X ≃* Y) : center X = ⊥ := by
  have : Nontrivial X := e.symm.injective.nontrivial
  have : IsSimpleGroup X :=
    IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
  rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hqs.2.2
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have hb : b ∈ center X := h ▸ mem_top b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.mp hb a)]

theorem nontrivial_specialLinearGroup {n : ℕ} (hn : 2 ≤ n) (F : Type*) [Field F] :
    Nontrivial (Matrix.SpecialLinearGroup (Fin n) F) := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨⟨⟨Matrix.transvection ⟨0, by omega⟩ ⟨1, by omega⟩ 1,
    Matrix.det_transvection_of_ne _ _ h01 1⟩, 1, fun h => ?_⟩⟩
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) F =>
    (A : Matrix (Fin n) (Fin n) F) ⟨0, by omega⟩ ⟨1, by omega⟩) h
  simp [Matrix.transvection, h01] at this

end KG14726

open KG14726

end CFSG.Quasithin.H13

end
