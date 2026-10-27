module

public import CFSG.Quasithin.EmptyFaithful.A38c16Tensor
public import CFSG.Quasithin.EmptyFaithful.A38c16Blocks

public section

namespace CFSG.Quasithin.A38c16

open CFSG.Quasithin
open scoped MatrixGroups

section Core

variable {W : Type} [CommGroup W]

theorem isKSub_commSub_ofNorm {K : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : ∀ v ∈ commSub ⊤ K, g v ∈ commSub ⊤ K := by
  intro v hv
  unfold commSub at hv ⊢
  have key : ∀ c ∈ {c | ∃ x ∈ K, ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = c},
      g c ∈ Subgroup.closure {c | ∃ x ∈ K, ∃ w ∈ (⊤ : Subgroup W), x w * w⁻¹ = c} := by
    rintro c ⟨x, hx, w, -, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨g * x * g⁻¹, hg x hx, g w, Subgroup.mem_top _, ?_⟩
    simp
  induction hv using Subgroup.closure_induction with
  | mem c hc => exact key c hc
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha


theorem isKSub_commSub {X K : Subgroup (MulAut W)} (hX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    IsKSub X (commSub ⊤ K) := fun x hx v hv => isKSub_commSub_ofNorm (hX x hx) v hv

theorem case3_core [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hAut : SL3OutFacts) (hcheck : Case3Check)
    {Γ K Kp : Subgroup (MulAut W)} (hΓ : Case3Setting Γ K Kp)
    (θ : ↥K ≃* SL(3, ZMod 2)) (θp : ↥Kp ≃* SL(3, ZMod 2))
    {s : MulAut W} (hs : s ∈ Γ) (hso : IsOuterOn K s)
    (hA : commSub ⊤ K ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 K M), M)
    (hAp : commSub ⊤ Kp ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 Kp M), M)
    {A : Subgroup (MulAut W)} (hAΓ : A ≤ Γ) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A)
    (hAq : Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A)) :
    commSub ⊤ K ⊓ commSub ⊤ Kp = ⊥ := by
  by_contra hne
  have hKK : ∀ x ∈ K, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk =>
    K.mul_mem (K.mul_mem hx hk) (K.inv_mem hx)
  have hKpKp : ∀ x ∈ Kp, ∀ k ∈ Kp, x * k * x⁻¹ ∈ Kp := fun x hx k hk =>
    Kp.mul_mem (Kp.mul_mem hx hk) (Kp.inv_mem hx)
  have hKKp : ∀ x ∈ K, ∀ k ∈ Kp, x * k * x⁻¹ ∈ Kp := fun x hx k hk => by
    rw [hΓ.comm x hx k hk]; simpa using hk
  have hKpK : ∀ x ∈ Kp, ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun x hx k hk => by
    rw [← hΓ.comm k hk x hx]; simpa using hk
  set Y := commSub ⊤ K ⊓ commSub ⊤ Kp with hY
  have hYK : IsKSub K Y := fun x hx v hv =>
    ⟨isKSub_commSub hKK x hx v hv.1, isKSub_commSub hKKp x hx v hv.2⟩
  have hYKp : IsKSub Kp Y := fun x hx v hv =>
    ⟨isKSub_commSub hKpK x hx v hv.1, isKSub_commSub hKpKp x hx v hv.2⟩
  obtain ⟨S, hSY, hS1, hSK, hSKp, hSmin⟩ : ∃ S : Subgroup W, S ≤ Y ∧ S ≠ ⊥ ∧ IsKSub K S ∧
      IsKSub Kp S ∧ ∀ N : Subgroup W, N ≤ S → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = S := by
    let 𝒮 : Set (Subgroup W) := {N | N ≤ Y ∧ N ≠ ⊥ ∧ IsKSub K N ∧ IsKSub Kp N}
    obtain ⟨S, hS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup W)) 𝒮
      ⟨Y, le_rfl, hne, hYK, hYKp⟩
    refine ⟨S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, fun N hNS hNK hNKp => ?_⟩
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      by_contra hNS'
      exact hmin N ⟨hNS.trans hS.1, hN, hNK, hNKp⟩ (lt_of_le_of_ne hNS hNS')
  obtain ⟨t, hcount⟩ := tensor_counting hW θ θp hΓ.comm hA hAp hSY hS1 hSK hSKp hSmin
  have := no_offender_of_counting hW hAut hcheck hΓ θ θp hs hso hS1 hSK hSKp hSmin hcount hAΓ hA1
    hAe
  omega

end Core

end CFSG.Quasithin.A38c16
