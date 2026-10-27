module

public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.Background.G11Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SLCover CFSG.Assembly.LowTwoRank
open Matrix
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {B Q : Type} [Group B] [AddCommGroup Q] [Module (ZMod 2) Q]

theorem naturalThree_exists_dual_cocycle_not_coboundary
    (ρQ : Representation (ZMod 2) B Q) {ε : Explicit.NatDual}
    (hnat : Explicit.BinaryNaturalSL ρQ 3 (ZMod 2) ε) :
    ∃ d : B → Module.Dual (ZMod 2) Q,
      d ∈ Z1 (Representation.dual ρQ) ∧
      d ∉ B1 (Representation.dual ρQ) := by
  obtain ⟨θ, β, hβ⟩ := JonesParshall.BinaryNaturalSL.intertwiner hnat
  letI : Algebra (ZMod 2) (ZMod 2) := ZMod.algebra (ZMod 2) 2
  letI : Module (ZMod 2) ((Fin 3) → ZMod 2) :=
    @Pi.Function.module (Fin 3) (ZMod 2) (ZMod 2) _ _ (Algebra.toModule)
  let eQ : Q ≃ₗ[ZMod 2] ((Fin 3) → ZMod 2) := G11.addEquivToLinear β
  let psi := SLCover.psiEquiv 3 (ZMod 2)
  let dEquiv : Module.Dual (ZMod 2) Q ≃+ Module.Dual (ZMod 2) ((Fin 3) → ZMod 2) :=
  { toFun := fun f => f.comp eQ.symm.toLinearMap
    invFun := fun g => g.comp eQ.toLinearMap
    left_inv := fun f => by
      ext q
      simp
    right_inv := fun g => by
      ext v
      simp
    map_add' := fun f g => by
      ext v
      simp }
  let βd : Module.Dual (ZMod 2) Q ≃+ ((Fin 3) → ZMod 2) := dEquiv.trans psi.symm
  let eSL := specialLinearGroupEquivStatedSL 3 (ZMod 2)
  let θd : B ≃* SpecialLinearGroup (Fin 3) (ZMod 2) := θ.trans (invTransposeSL 3 (ZMod 2))
  have hβd_psi : ∀ f : Module.Dual (ZMod 2) Q, psi (βd f) = f.comp eQ.symm.toLinearMap := by
    intro f
    change psi (psi.symm (f.comp eQ.symm.toLinearMap)) = f.comp eQ.symm.toLinearMap
    exact psi.apply_symm_apply _
  have he : ∀ (b : B) (q : Q),
      eQ (ρQ b q) = SLCover.natRepQ 3 (ZMod 2) (eSL (θ b)) (eQ q) := by
    intro b q
    rw [SLCover.natRepQ_apply]
    change β (ρQ b q) =
      (((eSL (θ b) : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ β q
    rw [hβ b q]
    rw [specialLinearGroupEquivStatedSL_coe]
    simp [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
  have he_inv : ∀ (b : B) (x : Q),
      eQ (ρQ b⁻¹ x) = SLCover.natRepQ 3 (ZMod 2) ((eSL (θ b))⁻¹) (eQ x) := by
    intro b x
    have h := he b (ρQ b⁻¹ x)
    have hx : ρQ b (ρQ b⁻¹ x) = x := by simp
    rw [hx] at h
    have hmul : SLCover.natRepQ 3 (ZMod 2) ((eSL (θ b))⁻¹) *
        SLCover.natRepQ 3 (ZMod 2) (eSL (θ b)) = 1 := by
      rw [← map_mul]
      simp
    have h2 := congrArg (fun y => SLCover.natRepQ 3 (ZMod 2) ((eSL (θ b))⁻¹) y) h
    rw [← Module.End.mul_apply, hmul, Module.End.one_apply] at h2
    exact h2.symm
  have hcomp : ∀ (b : B) (f : Module.Dual (ZMod 2) Q),
      ((Representation.dual ρQ) b f).comp eQ.symm.toLinearMap =
        Representation.dual (SLCover.natRepQ 3 (ZMod 2)) (eSL (θ b))
          (f.comp eQ.symm.toLinearMap) := by
    intro b f
    ext v
    rw [Representation.dual_apply]
    change f (ρQ b⁻¹ (eQ.symm v)) =
      f (eQ.symm (SLCover.natRepQ 3 (ZMod 2) (eSL (θ b)⁻¹) v))
    congr 1
    apply eQ.injective
    rw [he_inv b (eQ.symm v), eQ.apply_symm_apply, ← (map_inv eSL (θ b)).symm]
    exact (eQ.apply_symm_apply (SLCover.natRepQ 3 (ZMod 2) ((eSL (θ b))⁻¹) v)).symm
  have hmat : ∀ b : B,
      ((θd b : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        (((eSL (θ b))⁻¹ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2))ᵀ := by
    intro b
    rw [show θd b = invTransposeSL 3 (ZMod 2) (θ b) from rfl, invTransposeSL_coe]
    congr 1
  have hright : ∀ (b : B) (w : Module.Dual (ZMod 2) Q),
      psi (θd b • βd w) =
        Representation.dual (SLCover.natRepQ 3 (ZMod 2)) (eSL (θ b)) (psi (βd w)) := by
    intro b w
    have hsm : θd b • βd w =
        ((θd b : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ βd w := by
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    rw [hsm, hmat b]
    exact (SLCover.dual_psi 3 (ZMod 2) (eSL (θ b)) (βd w)).symm
  have hβd_group : ∀ (b : B) (w : Module.Dual (ZMod 2) Q),
      βd ((Representation.dual ρQ) b w) = θd b • βd w := by
    intro b w
    apply psi.injective
    rw [hβd_psi, hcomp b w, hright b w, hβd_psi]
  have hβd : ∀ (b : B) (w : Module.Dual (ZMod 2) Q),
      βd ((Representation.dual ρQ) b w) = muF2 3 (θd b) (βd w) := by
    intro b w
    exact hβd_group b w
  let d : B → Module.Dual (ZMod 2) Q := (transportFun θd βd).symm cocycle3
  have hd_transport : transportFun θd βd d = cocycle3 :=
    (transportFun θd βd).apply_symm_apply cocycle3
  refine ⟨d, ?_, ?_⟩
  · exact (transport_mem_Z1A (ρ := Representation.dual ρQ) (μ := muF2 3)
      (θ := θd) (β := βd) hβd).mp (by rw [hd_transport]; exact cocycle3_mem)
  · intro hd
    have hb : transportFun θd βd d ∈ B1A (muF2 3) :=
      (transport_mem_B1A (ρ := Representation.dual ρQ) (μ := muF2 3)
        (θ := θd) (β := βd) hβd).mpr hd
    rw [hd_transport] at hb
    exact cocycle3_not_mem hb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
