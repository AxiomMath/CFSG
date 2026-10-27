module

public import CFSG.LocalAnalysis.WeakClosure81.W19EightLinear
public import CFSG.LocalAnalysis.WeakClosure81.LemmaD
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem apply_conj_inv {a x : LGL 2 W} (hax : a * x * a⁻¹ = x⁻¹) (v : W) :
    a (x v) = x⁻¹ (a v) := by
  have hax' : a * x = x⁻¹ * a := by
    calc a * x = (a * x * a⁻¹) * a := by group
      _ = x⁻¹ * a := by rw [hax]
  have := congrArg (fun f : LGL 2 W => f v) hax'
  simpa [LinearEquiv.mul_apply] using this

private theorem apply_conj_inv' {a x : LGL 2 W} (hax : a * x * a⁻¹ = x⁻¹) (v : W) :
    a (x⁻¹ v) = x (a v) := by
  have h := apply_conj_inv hax (x⁻¹ v)
  rw [show x (x⁻¹ v) = v from LinearEquiv.apply_symm_apply x v] at h
  rw [h]
  exact (LinearEquiv.apply_symm_apply x _).symm

private theorem apply_apply_of_mul_self {a : LGL 2 W} (ha : a * a = 1) (v : W) : a (a v) = v := by
  have := congrArg (fun f : LGL 2 W => f v) ha
  simpa [LinearEquiv.mul_apply] using this

theorem fix_comm_of_quadratic {a x b : LGL 2 W} (hodd : Odd (orderOf x))
    (hax : a * x * a⁻¹ = x⁻¹) (ha : a * a = 1) (hbx : b * x = x * b)
    (hq : ∀ w : W, b (a w - w) = a w - w) (u : W) : b (x u - u) = x u - u := by
  have hbxv : ∀ v : W, b (x v) = x (b v) := fun v => by
    have := congrArg (fun f : LGL 2 W => f v) hbx
    simpa [LinearEquiv.mul_apply] using this
  have hbxn : ∀ (n : ℕ) (v : W), b ((x ^ n) v) = (x ^ n) (b v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbxv, ih]
  have h1 : ∀ w : W, b (x (x w) - w) = x (x w) - w := by
    intro w
    have hs1 : x (x⁻¹ (a w)) = a w := LinearEquiv.apply_symm_apply x _
    have hs2 : a (x⁻¹ (a w)) = x w := by rw [apply_conj_inv' hax, apply_apply_of_mul_self ha]
    have e : x (x w) - w = x (a (x⁻¹ (a w)) - x⁻¹ (a w)) + (a w - w) := by
      rw [map_sub, hs2, hs1]
      abel
    rw [e, map_add, hbxv, hq, hq]
  have h2 : ∀ k : ℕ, b ((x ^ (2 * k)) u - u) = (x ^ (2 * k)) u - u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : x ^ (2 * (k + 1)) = x ^ (2 * k) * (x * x) := by
        rw [mul_add, mul_one, pow_add, pow_two]
      have e2 : (x ^ (2 * (k + 1))) u - u =
          (x ^ (2 * k)) (x (x u) - u) + ((x ^ (2 * k)) u - u) := by
        rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub]
        abel
      rw [e2, map_add, hbxn, h1 u, ih]
  obtain ⟨m, hm⟩ := hodd
  have e : x ^ (2 * (m + 1)) = x := by
    have : 2 * (m + 1) = orderOf x + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  have := h2 (m + 1)
  rwa [e] at this

theorem fix_of_conj_fix {a x y : LGL 2 W} (hax : a * x * a⁻¹ = x⁻¹)
    (hxy : x * y = y * x) (hodd : Odd (orderOf x))
    (hfix : ∀ u : W, a (y u - u) = y u - u) (u : W) : x (y u - u) = y u - u := by
  have hxyv : ∀ v : W, x⁻¹ (y v) = y (x⁻¹ v) := fun v => by
    have := congrArg (fun f : LGL 2 W => f v)
      (show x⁻¹ * y = y * x⁻¹ from (Commute.inv_left (show Commute x y from hxy)).eq)
    simpa [LinearEquiv.mul_apply] using this
  have h1 := hfix (x⁻¹ u)
  have h2 : y (x⁻¹ u) - x⁻¹ u = x⁻¹ (y u - u) := by rw [map_sub, hxyv]
  rw [h2, apply_conj_inv' hax, hfix u] at h1
  refine fix_of_sq_fix hodd ?_
  rw [h1]
  exact LinearEquiv.apply_symm_apply x _

theorem exists_dihedral_conf [Finite W] {A X : Subgroup (LGL 2 W)} (hA : IsElemAbelian 2 A)
    (hodd : Odd (Nat.card X)) (hAX : A ≤ normalizer (X : Set (LGL 2 W)))
    (hC : A ⊓ centralizer (X : Set (LGL 2 W)) = ⊥) (h4 : 4 ≤ Nat.card A)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w : W, a (b w - w) = b w - w) :
    ∃ (B : Subgroup (LGL 2 W)) (a₁ x₂ : LGL 2 W) (w : W),
      B ≤ A ∧ (B.subgroupOf A).index = 2 ∧ a₁ ∈ A ∧ x₂ ∈ X ∧ x₂ ≠ 1 ∧
      (∀ b ∈ B, b w = w) ∧ a₁ w ≠ w ∧ x₂ (a₁ w - w) = a₁ w - w := by
  have hindex : 4 ≤ ((A ⊓ centralizer (X : Set (LGL 2 W))).subgroupOf A).index := by
    rw [hC, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact h4
  obtain ⟨dd⟩ := lemmaD hA hAX hodd hindex
  have hodd' : ∀ y ∈ X, Odd (orderOf y) := fun y hy => by
    have h1 : orderOf (⟨y, hy⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hx₁ : dd.x₁ ∈ X := dd.X₀_le dd.x₁_mem
  have hx₂ : dd.x₂ ∈ X := dd.X₀_le dd.x₂_mem
  have hx₁1 : dd.x₁ ≠ 1 := fun h => by
    have := dd.x₁_order
    rw [h, orderOf_one] at this
    exact dd.p₁_prime.one_lt.ne this
  have hx₂1 : dd.x₂ ≠ 1 := fun h => by
    have := dd.x₂_order
    rw [h, orderOf_one] at this
    exact dd.p₂_prime.one_lt.ne this
  have ha₁ : dd.a₁ * dd.a₁ = 1 := hA.mul_self_eq_one dd.a₁_mem
  have ha₂ : dd.a₂ * dd.a₂ = 1 := hA.mul_self_eq_one dd.a₂_mem
  obtain ⟨u, hu⟩ : ∃ u : W, dd.a₁ (dd.x₁ u - u) ≠ dd.x₁ u - u := by
    by_contra hcon
    apply hx₁1
    refine eq_one_of_dihedral_fix ha₁ dd.a₁_inverts (hodd' _ hx₁) fun u => ?_
    by_contra hne
    exact hcon ⟨u, hne⟩
  let S : Subgroup (LGL 2 W) :=
    { carrier := {g | g (dd.x₁ u - u) = dd.x₁ u - u}
      one_mem' := rfl
      mul_mem' := fun {g h} hg hh => by
        change g (h (dd.x₁ u - u)) = dd.x₁ u - u
        rw [show h (dd.x₁ u - u) = dd.x₁ u - u from hh,
          show g (dd.x₁ u - u) = dd.x₁ u - u from hg]
      inv_mem' := fun {g} hg => by
        change g⁻¹ (dd.x₁ u - u) = dd.x₁ u - u
        have h1 : g (dd.x₁ u - u) = dd.x₁ u - u := hg
        calc g⁻¹ (dd.x₁ u - u) = g⁻¹ (g (dd.x₁ u - u)) := by rw [h1]
          _ = dd.x₁ u - u := LinearEquiv.symm_apply_apply g _ }
  have hDA : dd.D ≤ A := by
    rw [dd.D_eq]
    exact inf_le_left
  have hDS : dd.D ≤ S := fun d hd => by
    have hd' := hd
    rw [dd.D_eq] at hd'
    have hbx : d * dd.x₁ = dd.x₁ * d :=
      (Subgroup.mem_centralizer_iff.1 hd'.2 dd.x₁ dd.x₁_mem).symm
    exact fix_comm_of_quadratic (hodd' _ hx₁) dd.a₁_inverts ha₁ hbx
      (fun w => hquad d hd'.1 dd.a₁ dd.a₁_mem w) u
  have ha₂S : dd.a₂ ∈ S := by
    have hbx : dd.a₂ * dd.x₁ = dd.x₁ * dd.a₂ := mul_inv_eq_iff_eq_mul.1 dd.a₂_centralizes
    exact fix_comm_of_quadratic (hodd' _ hx₁) dd.a₁_inverts ha₁ hbx
      (fun w => hquad dd.a₂ dd.a₂_mem dd.a₁ dd.a₁_mem w) u
  have hx₂₁ : dd.x₂ * dd.a₁ = dd.a₁ * dd.x₂ :=
    (mul_inv_eq_iff_eq_mul.1 dd.a₁_centralizes).symm
  refine ⟨dd.D ⊔ Subgroup.zpowers dd.a₂, dd.a₁, dd.x₂, dd.x₁ u - u,
    sup_le hDA (Subgroup.zpowers_le.2 dd.a₂_mem), dd.hyperplane, dd.a₁_mem, hx₂, hx₂1,
    fun b hb => sup_le hDS (Subgroup.zpowers_le.2 ha₂S) hb, hu, ?_⟩
  exact fix_of_conj_fix dd.a₂_inverts hx₂₁ (hodd' _ hx₂)
    (fun u' => hquad dd.a₂ dd.a₂_mem dd.a₁ dd.a₁_mem u') _

end CFSG.LocalAnalysis.WeakClosure81

end
