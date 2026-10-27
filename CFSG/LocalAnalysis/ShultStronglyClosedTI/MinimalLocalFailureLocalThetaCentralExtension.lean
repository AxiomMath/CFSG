module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open scoped commutatorElement IsMulCommutative

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem odd_central_square_kernel_commutative
    (C : Subgroup G) (hCodd : Odd (Nat.card C)) (hcentral : C ≤ Subgroup.center G)
    (hsquare : ∀ x : G, x ^ 2 ∈ C)
    (hcommutator : ∀ x y : G, ⁅x, y⁆ ∈ C) : IsMulCommutative G := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hxyC : ⁅x, y⁆ ∈ C := hcommutator x y
  have hxycentral : Commute x ⁅x, y⁆ :=
    (Subgroup.mem_center_iff.mp (hcentral hxyC)) x
  have hx2central : Commute (x ^ 2) y :=
    ((Subgroup.mem_center_iff.mp (hcentral (hsquare x))) y).symm
  have hxy2 : ⁅x, y⁆ ^ 2 = 1 := by
    rw [hxycentral.commutatorElement_pow_left, hx2central.commutator_eq]
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (square_one_eq_one_of_mem_odd_subgroup C hCodd hxyC hxy2)

omit [Finite G] in
theorem square_one_commuting_closure_elementary
    (s : Set G) (hcomm : s.Pairwise Commute) (hsquare : ∀ x ∈ s, x ^ 2 = 1) :
    IsElementaryAbelian 2 (Subgroup.closure s) := by
  let : IsMulCommutative (Subgroup.closure s) := Subgroup.isMulCommutative_closure hcomm
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.closure_induction (k := s)
    (p := fun x _ => x ^ 2 = 1) (x := x.val)
    hsquare (by simp) (by
      intro a b ha hb ha2 hb2
      have hab : Commute a b := congrArg Subtype.val
        (mul_comm (⟨a, ha⟩ : Subgroup.closure s) (⟨b, hb⟩ : Subgroup.closure s))
      rw [hab.mul_pow, ha2, hb2, one_mul]) (by
      intro a _ ha2
      simpa only [inv_pow, inv_one] using congrArg Inv.inv ha2) x.property

theorem involution_generated_odd_central_extension
    (C : Subgroup G) (hCodd : Odd (Nat.card C)) (hcentral : C ≤ Subgroup.center G)
    (hsquare : ∀ x : G, x ^ 2 ∈ C)
    (hcommutator : ∀ x y : G, ⁅x, y⁆ ∈ C)
    (s : Set G) (hgen : Subgroup.closure s = ⊤)
    (hs : ∀ x ∈ s, x ^ 2 = 1) :
    IsElementaryAbelian 2 G ∧ C = ⊥ := by
  let : IsMulCommutative G :=
    odd_central_square_kernel_commutative C hCodd hcentral hsquare hcommutator
  have helem := square_one_commuting_closure_elementary s
    (fun a _ b _ _ => (show a * b = b * a from mul_comm a b)) hs
  have hall : ∀ x : G, x ^ 2 = 1 := by
    intro x
    let : IsElementaryAbelian 2 (Subgroup.closure s) := helem
    exact elemPow_eq_one_of_isElementaryAbelian x (hgen.symm ▸ Subgroup.mem_top x)
  have helementary : IsElementaryAbelian 2 G :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall }
  refine ⟨helementary, ?_⟩
  apply le_antisymm _ bot_le
  intro x hx
  exact Subgroup.mem_bot.mpr (square_one_eq_one_of_mem_odd_subgroup C hCodd hx (hall x))

theorem involution_generated_odd_central_hom
    {F : Type v} [Group F] [IsElementaryAbelian 2 F]
    (f : G →* F) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G)
    (s : Set G) (hgen : Subgroup.closure s = ⊤)
    (hs : ∀ x ∈ s, x ^ 2 = 1) :
    IsElementaryAbelian 2 G ∧ Function.Injective f := by
  have hsquare : ∀ x : G, x ^ 2 ∈ f.ker := by
    intro x
    change f (x ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 F) (f x)
  have hcommutator : ∀ x y : G, ⁅x, y⁆ ∈ f.ker := by
    intro x y
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  obtain ⟨helem, hker⟩ := involution_generated_odd_central_extension
    f.ker hodd hcentral hsquare hcommutator s hgen hs
  exact ⟨helem, (MonoidHom.ker_eq_bot_iff f).mp hker⟩

end CFSG.ShultStronglyClosedTI.LocalTheta
