module

public import CFSG.Quasithin.Background.P4GLSylow
public import CFSG.Quasithin.Background.G10FifteenInputs

public section

namespace CFSG.Quasithin.G11.P4GL

open Pointwise Matrix CFSG.ComponentClassification

@[expose] def Concl {G : Type*} [Group G] (α : G ≃* G) (P : Set G) : Prop :=
  ∃ s ∈ P, ∃ t ∈ P,
    ¬ ((s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
      (s⁻¹ * α s) * (s⁻¹ * α s) = 1)

theorem concl_transport {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (α : G ≃* G) (P : Set G)
    (U : Set H) (hP : ∀ x, x ∈ P ↔ θ x ∈ U) :
    Concl (θ.symm.trans (α.trans θ)) U → Concl α P := by
  rintro ⟨s, hs, t, ht, hneg⟩
  refine ⟨θ.symm s, (hP _).2 (by simpa using hs), θ.symm t, (hP _).2 (by simpa using ht), ?_⟩
  rintro ⟨h1, h2⟩
  apply hneg
  constructor
  · have := congrArg θ h1
    simpa [map_mul, map_inv] using this
  · have := congrArg θ h2
    simpa [map_mul, map_inv] using this

theorem exists_iso_sylow {G : Type*} [Group G] [Finite G] {m : ℕ} (θ : G ≃* Gm m)
    (P : Sylow 2 G) : ∃ θ' : G ≃* Gm m, ∀ x : G, x ∈ P ↔ θ' x ∈ UTm m := by
  obtain ⟨Q0, hQ0⟩ := exists_sylow_UTm m
  have hle : Q0 ≤ θ.toMonoidHom.range := fun y _ => ⟨θ.symm y, θ.apply_symm_apply y⟩
  set Q1 : Sylow 2 G := Q0.comapOfInjective θ.toMonoidHom θ.injective hle with hQ1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q1 P
  refine ⟨(MulAut.conj g⁻¹ : G ≃* G).trans θ, fun x => ?_⟩
  have hx : x ∈ P ↔ g⁻¹ * x * g ∈ (Q1 : Subgroup G) := by
    rw [← hg]
    show x ∈ ((g • Q1 : Sylow 2 G) : Subgroup G) ↔ _
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  have e : ((MulAut.conj g⁻¹ : G ≃* G).trans θ) x = θ (g⁻¹ * x * g) := by
    simp
  rw [e, hx, ← hQ0]
  rfl

theorem transport_props {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (α : G ≃* G) (P : Set G)
    (U : Set H) (hP : ∀ x, x ∈ P ↔ θ x ∈ U) (hαP : ∀ s ∈ P, α s ∈ P)
    (hαα : ∀ s, α (α s) = s) :
    (∀ y ∈ U, (θ.symm.trans (α.trans θ)) y ∈ U) ∧
      ∀ y, (θ.symm.trans (α.trans θ)) ((θ.symm.trans (α.trans θ)) y) = y := by
  refine ⟨fun y hy => ?_, fun y => ?_⟩
  · have hx : θ.symm y ∈ P := (hP _).2 (by simpa using hy)
    have := (hP _).1 (hαP _ hx)
    simpa using this
  · simp [hαα]

theorem inner_of_conj {G H : Type*} [Group G] [Group H] (θ : G ≃* H) (α : G ≃* G) (A : H)
    (h : θ.symm.trans (α.trans θ) = MulAut.conj A) : ∃ c : G, ∀ x : G, α x = c * x * c⁻¹ := by
  refine ⟨θ.symm A, fun x => ?_⟩
  apply θ.injective
  have := congrArg (fun φ : H ≃* H => φ (θ x)) h
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
  rw [this]
  simp

theorem val_of_eq_conj_mul_graph {n : ℕ} (A : GL (Fin n) (ZMod 2))
    (α : MulAut (GL (Fin n) (ZMod 2)))
    (hA : α = MulAut.conj A * CatalogueBGraphForm.glGraphAut n (ZMod 2)) (x : GL (Fin n) (ZMod 2)) :
    ((α x : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((x⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
        ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  rw [hA, MulAut.mul_apply, MulAut.conj_apply, Units.val_mul, Units.val_mul,
    CatalogueBGraphForm.glGraphAut_matrix]

theorem concl_gl {m : ℕ} (hm : m ≠ 1) (α : MulAut (Gm m)) (hUα : ∀ x ∈ UTm m, α x ∈ UTm m)
    (hinv : ∀ x, α (α x) = x) (hnot : ¬ ∃ A : Gm m, α = MulAut.conj A) :
    Concl α (UTm m : Set (Gm m)) := by
  rcases aut_GL_cases (show 3 ≤ m + 3 by omega) α with ⟨A, hA⟩ | ⟨A, hA⟩
  · exact absurd ⟨A, hA⟩ hnot
  · exact core_group hm (isUT_UTm m) α A (val_of_eq_conj_mul_graph A α hA) hUα hinv

noncomputable def glvEquiv {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {m : ℕ}
    (b : Module.Basis (Fin (m + 3)) (ZMod 2) U) : (U ≃ₗ[ZMod 2] U) ≃* Gm m :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

end CFSG.Quasithin.G11.P4GL

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.G11.P4GL

theorem outerGLInput : OuterGLInput := by
  intro U _ _ _ K hK h3 h4 α P hαP hαα hnot
  classical
  have : Finite (U ≃ₗ[ZMod 2] U) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank (ZMod 2) U = m + 3 :=
    ⟨Module.finrank (ZMod 2) U - 3, by omega⟩
  have hm1 : m ≠ 1 := by omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) U hm
  have hKtop : K = ⊤ := eq_top_iff.2 fun g _ => hK g
  let kE : ↥K ≃* (U ≃ₗ[ZMod 2] U) := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
  let θ : ↥K ≃* Gm m := kE.trans (glvEquiv b)
  obtain ⟨θ', hθ'⟩ := exists_iso_sylow θ P
  have hprops := transport_props θ' α (P : Set ↥K) (UTm m : Set (Gm m)) hθ' hαP hαα
  refine concl_transport θ' α (P : Set ↥K) (UTm m : Set (Gm m)) hθ' ?_
  refine concl_gl hm1 _ hprops.1 hprops.2 ?_
  rintro ⟨A, hA⟩
  obtain ⟨c', hc'⟩ := inner_of_conj θ' α A hA
  exact hnot ⟨(c' : U ≃ₗ[ZMod 2] U), fun k => by rw [hc' k]; simp⟩

end CFSG.Quasithin.G11
