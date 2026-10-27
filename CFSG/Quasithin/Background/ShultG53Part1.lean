module

public import CFSG.Quasithin.Background.ShultG53Cyc

public section

namespace CFSG.Quasithin.ShultG53

open Classical

variable {X : Type} [Group X] (V : Md X)

@[expose] noncomputable def eqvMd (g : X) : V.carrier ≃ V.carrier where
  toFun := V.ρ g
  invFun := V.ρ g⁻¹
  left_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem weightHom_apply' [Fintype V.carrier] (u : V.carrier → ZMod 2) :
    weightHom V u = ∑ w : V.carrier, u w :=
  finsum_eq_sum_of_fintype u

theorem weightHom_permAct (g : X) (u : V.carrier → ZMod 2) :
    weightHom V (permAct V g u) = weightHom V u := by
  show ∑ᶠ w, u (V.ρ g⁻¹ w) = ∑ᶠ w, u w
  exact finsum_comp_equiv (eqvMd V g⁻¹) (f := u)

@[expose] noncomputable def onesFn : V.carrier → ZMod 2 := fun w => if w = 0 then 0 else 1

theorem permAct_onesFn (g : X) : permAct V g (onesFn V) = onesFn V := by
  funext w
  show (if V.ρ g⁻¹ w = 0 then (0 : ZMod 2) else 1) = if w = 0 then 0 else 1
  have : V.ρ g⁻¹ w = 0 ↔ w = 0 := by
    constructor
    · intro h
      have := congrArg (V.ρ g) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        map_zero] at this
    · intro h
      rw [h, map_zero]
  simp only [this]

theorem weight_onesFn (hV : Nat.card V.carrier = 2 ^ 4) : weightHom V (onesFn V) = 1 := by
  haveI : Fintype V.carrier := Fintype.ofFinite _
  rw [weightHom_apply']
  have h1 : ∑ w : V.carrier, onesFn V w = ((Finset.univ.filter (fun w : V.carrier => w ≠ 0)).card :
      ZMod 2) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w = 0 <;> simp [onesFn, hw]
  rw [h1, Finset.filter_ne' Finset.univ (0 : V.carrier), Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card, hV]
  decide

theorem permCore_inv_md : InvSub (permAct V) (permCore V) := by
  intro g u hu
  obtain ⟨h0, h1⟩ := AddSubgroup.mem_inf.mp hu
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [AddMonoidHom.mem_ker] at h0 ⊢
    show u (V.ρ g⁻¹ 0) = 0
    rw [map_zero]
    exact h0
  · rw [AddMonoidHom.mem_ker] at h1 ⊢
    rw [weightHom_permAct]
    exact h1

theorem mem_permOnes {u : V.carrier → ZMod 2} :
    u ∈ permOnes V ↔ ∃ n : ℤ, n • onesFn V = u := by
  unfold permOnes
  exact AddSubgroup.mem_closure_singleton

theorem zsmul_onesFn (n : ℤ) : n • onesFn V = 0 ∨ n • onesFn V = onesFn V := by
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    funext w
    show (m + m) • onesFn V w = 0
    rw [zsmul_eq_mul]
    push_cast
    rw [CharTwo.add_self_eq_zero, zero_mul]
  · right
    funext w
    show (2 * m + 1) • onesFn V w = onesFn V w
    rw [zsmul_eq_mul]
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_mul, zero_add, one_mul]

theorem permOnes_inv : InvSub (permAct V) (permOnes V) := by
  intro g u hu
  obtain ⟨n, rfl⟩ := (mem_permOnes V).mp hu
  refine (mem_permOnes V).mpr ⟨n, ?_⟩
  have h1 : permAct V g (n • onesFn V) = n • permAct V g (onesFn V) :=
    map_zsmul (permRep V g) n (onesFn V)
  rw [h1, permAct_onesFn]

theorem mem_permCore_md (u : V.carrier → ZMod 2) :
    u ∈ permCore V ↔ u 0 = 0 ∧ weightHom V u = 0 := by
  unfold permCore
  rw [AddSubgroup.mem_inf, AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  rfl

theorem mem_permSpace_md (u : V.carrier → ZMod 2) : u ∈ permSpace V ↔ u 0 = 0 := by
  unfold permSpace
  rw [AddMonoidHom.mem_ker]
  rfl

theorem onesFn_zero : onesFn V 0 = 0 := by simp [onesFn]

theorem inf_ones_eq_bot (hV : Nat.card V.carrier = 2 ^ 4) : permCore V ⊓ permOnes V = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
  obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.mp hu
  obtain ⟨n, rfl⟩ := (mem_permOnes V).mp h2
  rcases zsmul_onesFn V n with h | h
  · exact h
  · exfalso
    rw [h, mem_permCore_md, weight_onesFn V hV] at h1
    exact one_ne_zero h1.2

theorem sup_ones_eq (hV : Nat.card V.carrier = 2 ^ 4) :
    permCore V ⊔ permOnes V = permSpace V := by
  apply le_antisymm
  · refine sup_le (fun u hu => ?_) ?_
    · exact (mem_permSpace_md V u).mpr ((mem_permCore_md V u).mp hu).1
    · rw [permOnes, AddSubgroup.closure_le]
      intro u hu
      rw [Set.mem_singleton_iff.mp hu]
      exact (mem_permSpace_md V _).mpr (onesFn_zero V)
  · intro u hu
    have hu0 : u 0 = 0 := (mem_permSpace_md V u).mp hu
    have hones : onesFn V ∈ permOnes V := AddSubgroup.subset_closure rfl
    have hw : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hw (weightHom V u) with h | h
    · exact AddSubgroup.mem_sup_left ((mem_permCore_md V u).mpr ⟨hu0, h⟩)
    · have hc : u + onesFn V ∈ permCore V := by
        rw [mem_permCore_md]
        refine ⟨by simp [hu0, onesFn_zero], ?_⟩
        rw [map_add, h, weight_onesFn V hV]
        decide
      have : u = (u + onesFn V) + onesFn V := by
        funext w
        show u w = (u w + onesFn V w) + onesFn V w
        generalize onesFn V w = a
        generalize u w = b
        revert a b
        decide
      rw [this]
      exact AddSubgroup.add_mem_sup hc hones

end CFSG.Quasithin.ShultG53

namespace CFSG.Quasithin.ShultG53

theorem part1_of_card (V₁ : Md ↥(alternatingGroup (Fin 6))) (h : Nat.card V₁.carrier = 2 ^ 4) :
    Part1 V₁ :=
  ⟨permCore_inv_md V₁, permOnes_inv V₁, inf_ones_eq_bot V₁ h, sup_ones_eq V₁ h⟩

end CFSG.Quasithin.ShultG53
