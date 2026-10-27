module

public import CFSG.Quasithin.SteinbergCBI16Alt5

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Trace

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [Fintype G] {W : Type*}
  [AddCommGroup W] [Module k W]

@[expose] noncomputable def traceFun (ρ : Representation k G W) (l : W →ₗ[k] k) (v : W) :
    MonoidAlgebra k G :=
  ∑ g : G, l (ρ g⁻¹ v) • MonoidAlgebra.of k G g

theorem traceFun_add (ρ : Representation k G W) (l : W →ₗ[k] k) (v w : W) :
    traceFun ρ l (v + w) = traceFun ρ l v + traceFun ρ l w := by
  simp only [traceFun, map_add, add_smul, Finset.sum_add_distrib]

theorem traceFun_smul (ρ : Representation k G W) (l : W →ₗ[k] k) (r : k) (v : W) :
    traceFun ρ l (r • v) = r • traceFun ρ l v := by
  simp only [traceFun, map_smul, smul_eq_mul, Finset.smul_sum, mul_smul]

theorem traceFun_asAlgebraHom (ρ : Representation k G W) (l : W →ₗ[k] k)
    (a : MonoidAlgebra k G) (v : W) :
    traceFun ρ l (ρ.asAlgebraHom a v) = a * traceFun ρ l v := by
  induction a using MonoidAlgebra.induction_on generalizing v with
  | of g' =>
    rw [Representation.asAlgebraHom_of]
    simp only [traceFun, Finset.mul_sum, mul_smul_comm, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g'⁻¹) _ _ fun g => by
      simp only [Equiv.coe_mulLeft, mul_inv_cancel_left, mul_inv_rev, inv_inv,
        ← Module.End.mul_apply, ← map_mul]
  | add x y hx hy =>
    rw [map_add, LinearMap.add_apply, traceFun_add, hx, hy, add_mul]
  | smul r x hx =>
    rw [map_smul, LinearMap.smul_apply, traceFun_smul, hx, smul_mul_assoc]

@[expose] noncomputable def traceMap (ρ : Representation k G W) (l : W →ₗ[k] k) :
    ρ.asModule →ₗ[MonoidAlgebra k G] MonoidAlgebra k G where
  toFun w := traceFun ρ l (ρ.asModuleEquiv w)
  map_add' v w := by
    rw [map_add, traceFun_add]
  map_smul' a w := by
    rw [Representation.asModuleEquiv_map_smul, traceFun_asAlgebraHom, RingHom.id_apply,
      smul_eq_mul]

theorem projective_of_trace (ρ : Representation k G W) (l : W →ₗ[k] k) (w₀ : W)
    (h : ∀ w, ∑ g : G, l (ρ g⁻¹ w) • ρ g w₀ = w) :
    Module.Projective (MonoidAlgebra k G) ρ.asModule := by
  refine Module.Projective.of_split (traceMap ρ l)
    (LinearMap.toSpanSingleton _ _ (ρ.asModuleEquiv.symm w₀)) (LinearMap.ext fun w => ?_)
  apply ρ.asModuleEquiv.injective
  rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, Representation.asModuleEquiv_map_smul,
    LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  change ρ.asAlgebraHom (traceFun ρ l (ρ.asModuleEquiv w)) w₀ = ρ.asModuleEquiv w
  simp only [traceFun, map_sum, map_smul, Representation.asAlgebraHom_of, LinearMap.sum_apply,
    LinearMap.smul_apply]
  exact h _

end Trace

theorem trace5 : ∀ c < 2 ^ 4, ∑ σ : ↥(alternatingGroup (Fin 5)),
    coords5.actA σ⁻¹ (toV 4 c) 0 • coords5.actA σ (Pi.single 0 1) = toV 4 c := by
  decide +kernel

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem projective_alternatingNatural_five {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ 5 .alternating) :
    Module.Projective (MonoidAlgebra (ZMod 2) Γ) ρ.asModule := by
  obtain ⟨θ, e, he⟩ := coords5.exists_intertwiner h
  let _ : Fintype Γ := Fintype.ofEquiv _ θ.symm.toEquiv
  let eL : W →ₗ[ZMod 2] (Fin 4 → ZMod 2) := e.toAddMonoidHom.toZModLinearMap 2
  have heL : ∀ w, eL w = e w := fun _ => rfl
  refine projective_of_trace ρ ((LinearMap.proj 0).comp eL) (e.symm (Pi.single 0 1)) fun w => ?_
  apply e.injective
  have key : ∀ γ : Γ, e (((LinearMap.proj 0).comp eL) (ρ γ⁻¹ w) • ρ γ (e.symm (Pi.single 0 1))) =
      coords5.actA (θ γ)⁻¹ (e w) 0 • coords5.actA (θ γ) (Pi.single 0 1) := by
    intro γ
    rw [← heL, map_smul, heL, he, AddEquiv.apply_symm_apply]
    congr 1
    change e (ρ γ⁻¹ w) 0 = _
    rw [he, map_inv]
  rw [map_sum, Finset.sum_congr rfl fun γ _ => key γ]
  obtain ⟨c, hc, hcw⟩ := toV_surj (e w)
  rw [← hcw]
  conv_rhs => rw [← trace5 c hc]
  exact Fintype.sum_equiv θ.toEquiv _ _ fun γ => rfl

end CFSG.Quasithin.SteinbergCB.I16
