module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBTwist

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem exists_gl_std_of_finrank {n m : ℕ} (A : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hA : Module.finrank (ZMod 2) A = m) :
    ∃ P : GL (Fin n) (ZMod 2), ∀ x : Fin n → ZMod 2,
      x ∈ A ↔ ∀ b : Fin n, m ≤ b.val → ((P : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec x) b = 0 := by
  have hq : Module.finrank (ZMod 2) ((Fin n → ZMod 2) ⧸ A) + m = n := by
    have h1 := A.finrank_quotient_add_finrank
    rw [hA, Module.finrank_fin_fun] at h1
    exact h1
  have hmn : m ≤ n := by omega
  obtain ⟨A', hA'⟩ := A.exists_isCompl
  let b : Module.Basis (Fin m) (ZMod 2) A := Module.finBasisOfFinrankEq (ZMod 2) A hA
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ x, M x = b.equivFun (A.projectionOnto A' hA' x) :=
    ⟨b.equivFun.toLinearMap ∘ₗ A.projectionOnto A' hA', fun x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (n - m) → ZMod 2),
      ∀ x, L x = 0 ↔ x ∈ A := by
    refine ⟨(LinearEquiv.ofFinrankEq ((Fin n → ZMod 2) ⧸ A) (Fin (n - m) → ZMod 2)
      (by rw [Module.finrank_fin_fun]; omega)).toLinearMap ∘ₗ A.mkQ, fun x => ?_⟩
    simp
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2),
      ∀ (x : Fin n → ZMod 2) (c : Fin n), E x c = if h : c.val < m then M x ⟨c.val, h⟩
        else L x ⟨c.val - m, by have := c.isLt; omega⟩ := by
    refine ⟨LinearMap.pi fun c => if h : c.val < m then
        (LinearMap.proj (⟨c.val, h⟩ : Fin m) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp M
      else (LinearMap.proj (⟨c.val - m, by have := c.isLt; omega⟩ : Fin (n - m)) :
        (Fin (n - m) → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp L, fun x c => ?_⟩
    simp only [LinearMap.pi_apply]
    split_ifs <;> rfl
  have hE_lo : ∀ (x : Fin n → ZMod 2) (c : Fin n) (h : c.val < m),
      E x c = M x ⟨c.val, h⟩ := by
    intro x c h
    rw [hE x c, dif_pos h]
  have hE_hi : ∀ (x : Fin n → ZMod 2) (c : Fin n) (h : m ≤ c.val),
      E x c = L x ⟨c.val - m, by have := c.isLt; omega⟩ := by
    intro x c h
    have hnc : ¬ c.val < m := by omega
    rw [hE x c, dif_neg hnc]
  have key : ∀ x, x ∈ A ↔ ∀ c : Fin n, m ≤ c.val → E x c = 0 := by
    intro x
    constructor
    · intro hx c hc
      rw [hE_hi x c hc]
      exact congrFun ((hL x).mpr hx) _
    · intro hc
      refine (hL x).mp (funext fun j => ?_)
      have hj : j.val + m < n := by have := j.isLt; omega
      have h1 := hc ⟨j.val + m, hj⟩ (Nat.le_add_left m j.val)
      rw [hE_hi x ⟨j.val + m, hj⟩ (Nat.le_add_left m j.val)] at h1
      have h2 : (⟨j.val + m - m, by have := j.isLt; omega⟩ : Fin (n - m)) = j :=
        Fin.ext (Nat.add_sub_cancel j.val m)
      exact (congrArg (L x) h2).symm.trans h1
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).mpr fun x hx0 => ?_
    have hxA : x ∈ A := (key x).mpr fun c _ => congrFun hx0 c
    have hM0 : M x = 0 := by
      funext i
      have hi' : i.val < n := lt_of_lt_of_le i.isLt hmn
      have h1 : E x ⟨i.val, hi'⟩ = 0 := congrFun hx0 _
      rw [hE_lo x ⟨i.val, hi'⟩ i.isLt] at h1
      exact h1
    have h2 : b.equivFun (A.projectionOnto A' hA' x) = 0 := by
      rw [← hM x, hM0]
    rw [Submodule.projectionOnto_apply_of_mem_left hA' hxA] at h2
    exact congrArg Subtype.val ((b.equivFun.map_eq_zero_iff).mp h2)
  have hbij : Function.Bijective E := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hEu : IsUnit E := (Module.End.isUnit_iff E).mpr hbij
  have hdet : IsUnit (LinearMap.toMatrix' E).det := by
    rw [LinearMap.det_toMatrix', ← LinearMap.isUnit_iff_isUnit_det]
    exact hEu
  have hMu : IsUnit (LinearMap.toMatrix' E) := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  refine ⟨hMu.unit, fun x => ?_⟩
  rw [hMu.unit_spec, LinearMap.toMatrix'_mulVec]
  exact key x

end CFSG.Quasithin.H13.Ch4.NSB
