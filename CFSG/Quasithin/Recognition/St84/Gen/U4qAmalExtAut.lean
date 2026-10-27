module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDC
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtAutRigid
import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

private def resU4ExtAut {G : Type*} [Group G] (Ψ : MulAut G) (S : Subgroup G)
    (hS : ∀ g, g ∈ S ↔ Ψ g ∈ S) : MulAut ↥S where
  toFun x := ⟨Ψ (x : G), (hS x).mp x.2⟩
  invFun x := ⟨Ψ.symm (x : G), (hS _).mpr (by rw [MulEquiv.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (Ψ.symm_apply_apply (x : G))
  right_inv x := Subtype.ext (Ψ.apply_symm_apply (x : G))
  map_mul' x y := Subtype.ext (map_mul Ψ (x : G) (y : G))

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem mem_radQ_iff_of_mulAut_u4ExtAut (hm : 2 ≤ m) (θ : MulAut ↥(parP h))
    (x : ↥(parP h)) :
    (x : hypSU h 2 0) ∈ radQ h ↔ ((θ x : ↥(parP h)) : hypSU h 2 0) ∈ radQ h := by
  have key : θ x ∈ CFSG.pCore 2 ↥(parP h) ↔ x ∈ CFSG.pCore 2 ↥(parP h) := by
    have e := Subgroup.mem_map_equiv (f := θ) (K := CFSG.pCore 2 ↥(parP h)) (x := θ x)
    rw [CFSG.pCore_map_iso, MulEquiv.symm_apply_apply] at e
    exact e
  rw [← U4qModel.pCoreOf_parP_eq h hm, CFSG.mem_openPCoreOf_iff, CFSG.mem_openPCoreOf_iff]
  exact key.symm

theorem exists_stdAut_eq_of_agree_inf_u4 (hm : 2 ≤ m) (θ₁ : MulAut ↥(parP h))
    (θ₂ : MulAut ↥(parP2 h))
    (hθ : ∀ (x : ↥(parP h)) (y : ↥(parP2 h)), (x : hypSU h 2 0) = y →
      ((θ₁ x : ↥(parP h)) : hypSU h 2 0) = θ₂ y) :
    ∃ (e : ↥(parP h ⊓ parP2 h)) (d : hypSU h 2 0) (ρ : K ≃+* K), d ∈ hypTorus h 2 0 ∧
      (∀ x : ↥(parP h), ((θ₁ x : ↥(parP h)) : hypSU h 2 0) =
        (MulAut.conj (e : hypSU h 2 0)⁻¹ * u4StdAut h d ρ) x) ∧
      ∀ x : ↥(parP2 h), ((θ₂ x : ↥(parP2 h)) : hypSU h 2 0) =
        (MulAut.conj (e : hypSU h 2 0)⁻¹ * u4StdAut h d ρ) x := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hB : ∀ b : ↥(parP h ⊓ parP2 h),
      ((θ₁ ⟨b, b.2.1⟩ : ↥(parP h)) : hypSU h 2 0) ∈ parP h ⊓ parP2 h := fun b =>
    ⟨(θ₁ _).2, by rw [hθ ⟨b, b.2.1⟩ ⟨b, b.2.2⟩ rfl]; exact (θ₂ _).2⟩
  let f : ↥(parP h ⊓ parP2 h) →* ↥(parP h ⊓ parP2 h) :=
    { toFun := fun b => ⟨θ₁ ⟨b, b.2.1⟩, hB b⟩
      map_one' := by
        apply Subtype.ext
        change ((θ₁ 1 : ↥(parP h)) : hypSU h 2 0) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((θ₁ (⟨a, a.2.1⟩ * ⟨b, b.2.1⟩) : ↥(parP h)) : hypSU h 2 0) =
          ((θ₁ ⟨a, a.2.1⟩ * θ₁ ⟨b, b.2.1⟩ : ↥(parP h)) : hypSU h 2 0)
        rw [map_mul] }
  have hfi : Function.Injective f := by
    intro a b hab
    have h0 := congrArg Subtype.val hab
    have h1 : (⟨a, a.2.1⟩ : ↥(parP h)) = ⟨b, b.2.1⟩ := θ₁.injective (Subtype.ext h0)
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  let σ : MulAut ↥(parP h ⊓ parP2 h) :=
    MulEquiv.ofBijective f ⟨hfi, Finite.injective_iff_surjective.mp hfi⟩
  have hσ : ∀ b : ↥(parP h ⊓ parP2 h),
      ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = θ₁ ⟨b, b.2.1⟩ := fun _ => rfl
  obtain ⟨e, d, ρ, hdT, hagree⟩ := exists_stdAut_eq_of_preserves_radQ_u4 h hm σ fun b => by
    rw [hσ]
    exact mem_radQ_iff_of_mulAut_u4ExtAut h hm θ₁ ⟨b, b.2.1⟩
  set Ψ : MulAut (hypSU h 2 0) := MulAut.conj (e : hypSU h 2 0)⁻¹ * u4StdAut h d ρ with hΨ
  have heB : (e : hypSU h 2 0) ∈ parP h ⊓ parP2 h := e.2
  have hdB : d ∈ parP h ⊓ parP2 h := hypTorus_le_inf_u4 h hdT
  have hP : ∀ g, g ∈ parP h ↔ Ψ g ∈ parP h := by
    intro g
    rw [hΨ, MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ heB.1,
      Subgroup.mul_mem_cancel_left _ ((parP h).inv_mem heB.1)]
    exact (stdAut_mem_parP_iff_u4 h hdB.1 ρ g).symm
  have hP2 : ∀ g, g ∈ parP2 h ↔ Ψ g ∈ parP2 h := by
    intro g
    rw [hΨ, MulAut.mul_apply, MulAut.conj_apply, inv_inv, Subgroup.mul_mem_cancel_right _ heB.2,
      Subgroup.mul_mem_cancel_left _ ((parP2 h).inv_mem heB.2)]
    exact (stdAut_mem_parP2_iff_u4 h hdB.2 ρ g).symm
  have h1B : ∀ x : ↥(parP h), (x : hypSU h 2 0) ∈ parP h ⊓ parP2 h →
      ((θ₁ x : ↥(parP h)) : hypSU h 2 0) = Ψ x := fun x hx => (hagree ⟨x, hx⟩).symm
  have h2B : ∀ y : ↥(parP2 h), (y : hypSU h 2 0) ∈ parP h ⊓ parP2 h →
      ((θ₂ y : ↥(parP2 h)) : hypSU h 2 0) = Ψ y := fun y hy =>
    (hθ ⟨y, hy.1⟩ y rfl).symm.trans (h1B ⟨y, hy.1⟩ hy)
  refine ⟨e, d, ρ, hdT, fun x => ?_, fun x => ?_⟩
  · have h1 : (resU4ExtAut Ψ (parP h) hP)⁻¹ * θ₁ = 1 :=
      eq_one_of_forall_fix_inf_parP_u4 h hm _ fun y hy => by
        rw [MulAut.mul_apply, show θ₁ y = resU4ExtAut Ψ (parP h) hP y from
          Subtype.ext (h1B y hy), MulAut.inv_apply_self]
    rw [← inv_mul_eq_one.mp h1]
    rfl
  · have h2 : (resU4ExtAut Ψ (parP2 h) hP2)⁻¹ * θ₂ = 1 :=
      eq_one_of_forall_fix_inf_parP2_u4 h hm _ fun y hy => by
        rw [MulAut.mul_apply, show θ₂ y = resU4ExtAut Ψ (parP2 h) hP2 y from
          Subtype.ext (h2B y hy), MulAut.inv_apply_self]
    rw [← inv_mul_eq_one.mp h2]
    rfl

end CFSG.Quasithin.F112R.St84

end
