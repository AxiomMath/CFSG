module

public import CFSG.LieType.ReflectionGroups.F4ModThree
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open CFSG.LieType.ReflectionGroups.F4ModThree

private theorem exists_mulEquiv_of_weylOfType_F4 {G : Type} [Group G] {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card ↥Bs = 3 ^ 4)
    {A : Subgroup (MulAut ↥Bs)} (e : CoxeterMatrix.F₄.Group ≃* ↥A)
    (he : ∀ i, GGIsReflection 3
      ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs)) :
    ∃ θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3), ∀ (i : Fin 4) (b : ↥Bs),
      θ (((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs) b) =
        Multiplicative.ofAdd (f4Refl3 i (Multiplicative.toAdd (θ b))) := by
  refine exists_mulEquiv_f4Refl3_of_comm (fun a b => isMulCommutative_iff.mp hBs.1 a b)
    (fun x => ?_) hcard (fun i => ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs))
    (fun i => (he i).1) (fun i => (he i).2) (fun i j => ?_)
  · ext
    simpa using hBs.2 x x.2
  · calc orderOf (((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs) *
          ((e (CoxeterMatrix.F₄.simple j) : ↥A) : MulAut ↥Bs))
        = orderOf ((e (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j) : ↥A) :
            MulAut ↥Bs) := by rw [map_mul, Subgroup.coe_mul]
      _ = orderOf (e (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j)) :=
        Subgroup.orderOf_coe _
      _ = orderOf (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j) :=
        MulEquiv.orderOf_eq e _
      _ = CoxeterMatrix.F₄ i j := CoxeterMatrix.F₄.toCoxeterSystem.orderOf_simple_mul_simple i j

theorem exists_mulEquiv_of_ggWeylOfType_F4 {G : Type} [Group G] {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card ↥Bs = 3 ^ 4)
    {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType 3 CoxeterMatrix.F₄ A) :
    ∃ (e : CoxeterMatrix.F₄.Group ≃* ↥A) (θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3)),
      (∀ i, GGIsReflection 3
        ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs)) ∧
      ∀ (i : Fin 4) (b : ↥Bs), θ (((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs) b) =
        Multiplicative.ofAdd (f4Refl3 i (Multiplicative.toAdd (θ b))) := by
  obtain ⟨e, he⟩ := hW
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_of_weylOfType_F4 hBs hcard e he
  exact ⟨e, θ, he, hθ⟩

theorem exists_f4Coords_of_ggWeylOfType_F4 {G : Type} [Group G] {Bs : Subgroup G}
    (hBs : CFSG.Open.IsElemAbelian 3 Bs) (hcard : Nat.card ↥Bs = 3 ^ 4)
    {A : Subgroup (MulAut ↥Bs)} (hW : GGWeylOfType 3 CoxeterMatrix.F₄ A) :
    ∃ θ : ↥Bs ≃* Multiplicative (Fin 4 → ZMod 3),
      (∀ a ∈ A, ∀ b c : ↥Bs,
        f4Bil3 (Multiplicative.toAdd (θ (a b))) (Multiplicative.toAdd (θ (a c))) =
          f4Bil3 (Multiplicative.toAdd (θ b)) (Multiplicative.toAdd (θ c))) ∧
      ∀ x : Fin 4 → ZMod 3, f4Q3 x ≠ 0 → ∃ a ∈ A, ∃ w ∈ f4Cross3 x,
        Multiplicative.toAdd (θ (a (θ.symm (Multiplicative.ofAdd w)))) ∉ f4Cross3 x := by
  obtain ⟨e, θ, -, hθ⟩ := exists_mulEquiv_of_ggWeylOfType_F4 hBs hcard hW
  have hQ : ∀ g : CoxeterMatrix.F₄.Group, ∀ b : ↥Bs,
      f4Q3 (Multiplicative.toAdd (θ (((e g : ↥A) : MulAut ↥Bs) b))) =
        f4Q3 (Multiplicative.toAdd (θ b)) := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range CoxeterMatrix.F₄.simple) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple,
        CoxeterMatrix.F₄.toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b
      rw [hθ, toAdd_ofAdd, f4Q3_refl]
    | one => intro b; rw [map_one, Subgroup.coe_one, MulAut.one_apply]
    | mul x y _ _ hx hy =>
      intro b
      rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, hx, hy]
    | inv x _ hx =>
      intro b
      rw [← hx (((e x⁻¹ : ↥A) : MulAut ↥Bs) b), ← MulAut.mul_apply, ← Subgroup.coe_mul,
        ← map_mul, mul_inv_cancel, map_one, Subgroup.coe_one, MulAut.one_apply]
  have hA : ∀ a ∈ A, ∀ b : ↥Bs,
      f4Q3 (Multiplicative.toAdd (θ (a b))) = f4Q3 (Multiplicative.toAdd (θ b)) := by
    intro a ha b
    simpa using hQ (e.symm ⟨a, ha⟩) b
  have hpol : ∀ u v : Fin 4 → ZMod 3, f4Bil3 u v = f4Q3 (u + v) - f4Q3 u - f4Q3 v :=
    fun u v => by rw [f4Q3_add]; ring
  refine ⟨θ, fun a ha b c => ?_, fun x hx => ?_⟩
  · rw [hpol, hpol, ← toAdd_mul, ← map_mul θ, ← map_mul a, hA a ha (b * c),
      hA a ha b, hA a ha c, map_mul θ, toAdd_mul]
  · obtain ⟨i, w, hw, hwi⟩ := not_stable_f4Cross3 x hx
    refine ⟨_, (e (CoxeterMatrix.F₄.simple i)).2, w, hw, ?_⟩
    rwa [hθ, MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_ofAdd]

end CFSG.StandardType
