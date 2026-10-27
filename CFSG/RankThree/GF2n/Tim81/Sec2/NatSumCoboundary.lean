module

public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumCocycle

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups
open Matrix
open CFSG.Quasithin.JonesParshall
open CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

theorem IsNatSumModule.exists_eq_sub_of_cocycle_of_le
    {σ : Representation (ZMod 2) SL(2, F) N}
    (hσ : IsNatSumModule σ) {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {f : SL(2, F) → N} (hf : ∀ g h, f (g * h) = f g + σ g (f h)) {A A₁ : Subgroup SL(2, F)}
    (hA2 : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = Fintype.card F) (hA₁A : A₁ ≤ A)
    (hA₁ : 2 < Nat.card A₁) (hf₁ : ∀ x ∈ A₁, f x = 0) :
    ∃ v : N, (∀ x ∈ A, σ x v = v) ∧ ∀ g, f g = σ g v - v := by
  classical
  have hvan := IsNatSumModule.cocycle_eq_zero_of_le hσ hF ha hf hA2 hA hA₁A hA₁ hf₁
  haveI : Finite F := Finite.of_fintype F
  haveI : Finite (Matrix (Fin 2) (Fin 2) F) := Finite.of_fintype _
  haveI : Finite SL(2, F) := Finite.of_injective
    (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F)) Subtype.coe_injective
  let μ : SL(2, F) →* AddMonoid.End N :=
    { toFun := fun g => (σ g).toAddMonoidHom
      map_one' := AddMonoidHom.ext fun v => by
        change σ 1 v = v
        rw [map_one, Module.End.one_apply]
      map_mul' := fun g h => AddMonoidHom.ext fun v => by
        change σ (g * h) v = σ g (σ h v)
        rw [map_mul]
        rfl }
  have hodd : Odd A.index := by
    obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
    rw [hAx, show (conjSubgroup x (utri F)).index = (utri F).index from
      Subgroup.index_map_equiv (H := utri F) (MulAut.conj x)]
    exact CFSG.CGT.Timmesfeld75.odd_index_utri
  have h2 : ∀ m : N, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2) m, show (2 : ZMod 2) = 0 from by decide, zero_smul]
  obtain ⟨v, hv⟩ := mem_B1A_of_vanish h2 hodd
    (mem_Z1A.mpr fun g h => hf g h : f ∈ Z1A μ) hvan
  have hfv : ∀ g, f g = σ g v - v := fun g => (congrFun hv g).symm
  exact ⟨v, fun x hx => sub_eq_zero.mp ((hfv x).symm.trans (hvan x hx)), hfv⟩

theorem IsNatSumModule.exists_eq_sub_of_cocycle_comp
    {σ : Representation (ZMod 2) SL(2, F) N}
    (hσ : IsNatSumModule σ) {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {Γ : Type} [Group Γ] (π : Γ →* SL(2, F)) (hπ : Function.Surjective π)
    {c : Γ → N} (hc : ∀ x y, c (x * y) = c x + σ (π x) (c y))
    (hker : ∀ x, π x = 1 → c x = 0) {A A₁ : Subgroup SL(2, F)}
    (hA2 : ∀ s ∈ A, s * s = 1) (hA : Nat.card A = Fintype.card F) (hA₁A : A₁ ≤ A)
    (hA₁ : 2 < Nat.card A₁) (hc₁ : ∀ s ∈ A₁, ∃ x, π x = s ∧ c x = 0) :
    ∃ v : N, (∀ s ∈ A, σ s v = v) ∧ ∀ x, c x = σ (π x) v - v := by
  classical
  let τ := Function.surjInv hπ
  have hτ : ∀ s, π (τ s) = s := Function.surjInv_eq hπ
  have hdep : ∀ x y, π x = π y → c x = c y := by
    intro x y hxy
    have h1 : π (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := hc x (x⁻¹ * y)
    rw [mul_inv_cancel_left, hker _ h1, map_zero, add_zero] at h2
    exact h2.symm
  have hf : ∀ g h, c (τ (g * h)) = c (τ g) + σ g (c (τ h)) := by
    intro g h
    have := hc (τ g) (τ h)
    rw [hτ g] at this
    rw [← this]
    exact hdep _ _ (by rw [map_mul, hτ, hτ, hτ])
  have hf₁ : ∀ s ∈ A₁, c (τ s) = 0 := fun s hs => by
    obtain ⟨x, hxs, hx0⟩ := hc₁ s hs
    exact (hdep x (τ s) (by rw [hτ, hxs])).symm.trans hx0
  obtain ⟨v, hvA, hv⟩ := IsNatSumModule.exists_eq_sub_of_cocycle_of_le hσ (f := fun s => c (τ s))
    hF ha hf hA2 hA hA₁A hA₁ hf₁
  exact ⟨v, hvA, fun x => (hdep x (τ (π x)) (by rw [hτ])).trans (hv (π x))⟩

end CFSG.RankThree.GF2n.Tim81.Sec2
