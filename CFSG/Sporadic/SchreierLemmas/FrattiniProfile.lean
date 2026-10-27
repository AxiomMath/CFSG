module

public import CFSG.GroupTheory.FrattiniQuotient

public section

namespace CFSG.Sporadic.SchreierLemmas

open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped IsMulCommutative

variable {S : Type*} [Group S]

theorem card_fiber_congr (N : Subgroup S) [N.Characteristic] (α : MulAut S) (w : S ⧸ N)
    (P : S → Prop) (hP : ∀ x, P (α x) ↔ P x) :
    Nat.card {x : S // (x : S ⧸ N) = quotientAutomorphism N α w ∧ P x} =
      Nat.card {x : S // (x : S ⧸ N) = w ∧ P x} := by
  refine Nat.card_congr (α.symm.toEquiv.subtypeEquiv fun x => ?_)
  have h1 : quotientAutomorphism N α ((α.symm x : S) : S ⧸ N) = (x : S ⧸ N) :=
    (quotientAutomorphism_apply N α (α.symm x)).trans (congrArg _ (α.apply_symm_apply x))
  have h2 := hP (α.symm x)
  rw [α.apply_symm_apply] at h2
  change ((x : S ⧸ N) = quotientAutomorphism N α w ∧ P x) ↔
    ((α.symm x : S ⧸ N) = w ∧ P (α.symm x))
  rw [← h1, (quotientAutomorphism N α).injective.eq_iff, h2]

theorem Frattini_profile_automorphisms [Finite S] (hS : IsPGroup 2 S)
    (hprof : letI : CFSG.IsElementaryAbelian 2 (S ⧸ frattini S) :=
        (CFSG.GroupTheory.frattini_elementary_quotient hS).2.2.2.1
      ∀ T : Additive (S ⧸ frattini S) ≃ₗ[ZMod 2] Additive (S ⧸ frattini S),
        (∀ (v : Additive (S ⧸ frattini S)) (k : ℕ), 0 < k →
          Nat.card {x : S // (x : S ⧸ frattini S) = (T v).toMul ∧ orderOf x = k} =
              Nat.card {x : S // (x : S ⧸ frattini S) = v.toMul ∧ orderOf x = k} ∧
            Nat.card {x : S // (x : S ⧸ frattini S) = (T v).toMul ∧
                orderOf (x : S ⧸ Subgroup.center S) = k} =
              Nat.card {x : S // (x : S ⧸ frattini S) = v.toMul ∧
                orderOf (x : S ⧸ Subgroup.center S) = k}) →
        T = LinearEquiv.refl (ZMod 2) (Additive (S ⧸ frattini S))) :
    IsPGroup 2 (MulAut S) := by
  let _ : CFSG.IsElementaryAbelian 2 (S ⧸ frattini S) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hS).2.2.2.1
  intro α
  set αbar := quotientAutomorphism (frattini S) α
  let e : Additive (S ⧸ frattini S) ≃+ Additive (S ⧸ frattini S) := MulEquiv.toAdditive αbar
  let T : Additive (S ⧸ frattini S) ≃ₗ[ZMod 2] Additive (S ⧸ frattini S) :=
    e.toLinearEquiv fun c x => ZMod.map_smul e c x
  have hord : ∀ x : S, orderOf (α x : S ⧸ Subgroup.center S) =
      orderOf (x : S ⧸ Subgroup.center S) := fun x => by
    rw [show ((α x : S) : S ⧸ Subgroup.center S) =
      quotientAutomorphism (Subgroup.center S) α (x : S ⧸ Subgroup.center S) from
      (quotientAutomorphism_apply (Subgroup.center S) α x).symm]
    exact MulEquiv.orderOf_eq _ _
  have hT := hprof T fun v k _ =>
    ⟨card_fiber_congr (frattini S) α v.toMul (fun x => orderOf x = k)
        (fun x => by rw [MulEquiv.orderOf_eq]),
      card_fiber_congr (frattini S) α v.toMul
        (fun x => orderOf (x : S ⧸ Subgroup.center S) = k) (fun x => by rw [hord])⟩
  have hα : α ∈ (quotientAutomorphism (frattini S)).ker := by
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun v => ?_
    exact congrArg Additive.toMul (DFunLike.congr_fun hT (Additive.ofMul v))
  obtain ⟨n, hn⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hS).2 ⟨α, hα⟩
  exact ⟨n, congrArg Subtype.val hn⟩

end CFSG.Sporadic.SchreierLemmas
