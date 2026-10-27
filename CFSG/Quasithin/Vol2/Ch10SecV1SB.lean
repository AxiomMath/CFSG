module

public import CFSG.Quasithin.Vol2.Ch10SecV1SA

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C.A319

open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem transvection_mulVec_sub {i j : Fin 3} (t : K) (x : Fin 3 → K) :
    Matrix.transvection i j t *ᵥ x - x = Pi.single i (t * x j) := by
  ext k
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single, Matrix.mulVec, dotProduct,
    Pi.single_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Ne.symm hk, hk]

@[expose] noncomputable def transvSL {i j : Fin 3} (hij : i ≠ j) (t : K) : ↥(StatedSL 3 K) :=
  specialLinearGroupEquivStatedSL 3 K ⟨Matrix.transvection i j t,
    Matrix.det_transvection_of_ne i j hij t⟩

theorem coe_transvSL {i j : Fin 3} (hij : i ≠ j) (t : K) :
    (((transvSL hij t : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection i j t := rfl

theorem single_mem_of_invariant {U : AddSubgroup (Fin 3 → K)}
    (hU : ∀ γ : ↥(StatedSL 3 K), ∀ x ∈ U, ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ U)
    {x : Fin 3 → K} (hx : x ∈ U) {i j : Fin 3} (hij : i ≠ j) (hxj : x j ≠ 0) (c : K) :
    Pi.single i c ∈ U := by
  have h := U.sub_mem (hU (transvSL hij (c / x j)) x hx) hx
  rwa [coe_transvSL, transvection_mulVec_sub, div_mul_cancel₀ c hxj] at h

theorem eq_bot_or_top_of_invariant (U : AddSubgroup (Fin 3 → K))
    (hU : ∀ γ : ↥(StatedSL 3 K), ∀ x ∈ U,
      ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases h : ∀ x ∈ U, x = 0
  · exact Or.inl ((AddSubgroup.eq_bot_iff_forall U).mpr h)
  · right
    push Not at h
    obtain ⟨x, hx, hx0⟩ := h
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx0 (funext hc)
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := ⟨j + 1, by omega⟩
    have hei : Pi.single i (1 : K) ∈ U := single_mem_of_invariant hU hx hij hj 1
    have hall : ∀ (k : Fin 3) (c : K), Pi.single k c ∈ U := by
      intro k c
      by_cases hkj : k = j
      · subst hkj
        exact single_mem_of_invariant hU hei (Ne.symm hij) (by simp) c
      · exact single_mem_of_invariant hU hx hkj hj c
    rw [eq_top_iff]
    intro y _
    rw [← Finset.univ_sum_single y]
    exact AddSubgroup.sum_mem U fun k _ => hall k (y k)

variable {H : Type} [Group H] {L : Subgroup H}
  {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} {W : Subgroup H}

namespace NatCoord

@[expose] def coordSub (c : NatCoord φ W) (U : Subgroup H) : AddSubgroup (Fin 3 → K) where
  carrier := {x | ((c.θ.symm (Multiplicative.ofAdd x) : ↥W) : H) ∈ U}
  add_mem' := fun {x y} hx hy => by
    show ((c.θ.symm (Multiplicative.ofAdd (x + y)) : ↥W) : H) ∈ U
    rw [ofAdd_add, map_mul, Subgroup.coe_mul]
    exact U.mul_mem hx hy
  zero_mem' := by
    show ((c.θ.symm (Multiplicative.ofAdd 0) : ↥W) : H) ∈ U
    rw [ofAdd_zero, map_one, Subgroup.coe_one]
    exact U.one_mem
  neg_mem' := fun {x} hx => by
    show ((c.θ.symm (Multiplicative.ofAdd (-x)) : ↥W) : H) ∈ U
    rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
    exact U.inv_mem hx

theorem symm_mat (c : NatCoord φ W) (l : ↥L) (x : Fin 3 → K) :
    ((c.θ.symm (Multiplicative.ofAdd (mat φ l *ᵥ x)) : ↥W) : H) =
      l * (c.θ.symm (Multiplicative.ofAdd x) : H) * (l : H)⁻¹ := by
  obtain ⟨v', hv', hθ⟩ := c.act l (c.θ.symm (Multiplicative.ofAdd x))
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd] at hθ
  rw [← hθ, MulEquiv.symm_apply_apply, hv']

theorem eq_bot_or_eq (c : NatCoord φ W) {U : Subgroup H} (hUW : U ≤ W)
    (hLU : L ≤ Subgroup.normalizer (U : Set H)) : U = ⊥ ∨ U = W := by
  rcases eq_bot_or_top_of_invariant (c.coordSub U) (fun γ x hx => by
    obtain ⟨l, hl⟩ := exists_mat φ γ
    show ((c.θ.symm (Multiplicative.ofAdd (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      x)) : ↥W) : H) ∈ U
    rw [← hl, symm_mat]
    exact (Subgroup.mem_normalizer_iff.mp (hLU l.2) _).mp hx) with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have hx : Multiplicative.toAdd (c.θ ⟨u, hUW hu⟩) ∈ c.coordSub U := by
      show ((c.θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (c.θ ⟨u, hUW hu⟩))) : ↥W) :
        H) ∈ U
      rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
      exact hu
    rw [h, AddSubgroup.mem_bot] at hx
    have h1 : c.θ ⟨u, hUW hu⟩ = 1 := by
      rw [← ofAdd_toAdd (c.θ ⟨u, hUW hu⟩), hx, ofAdd_zero]
    have h2 : (⟨u, hUW hu⟩ : ↥W) = 1 := c.θ.injective (by rw [h1, map_one])
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  · right
    refine le_antisymm hUW fun w hw => ?_
    have hx : Multiplicative.toAdd (c.θ ⟨w, hw⟩) ∈ c.coordSub U := h ▸ AddSubgroup.mem_top _
    have : ((c.θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (c.θ ⟨w, hw⟩))) : ↥W) : H) ∈
      U := hx
    rwa [ofAdd_toAdd, MulEquiv.symm_apply_apply] at this

end NatCoord

end CFSG.Quasithin.Vol2.Ch10.V1C.A319
