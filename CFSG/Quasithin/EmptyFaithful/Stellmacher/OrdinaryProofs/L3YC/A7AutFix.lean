module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Inner
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFixPack

public section

open Equiv

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFix

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem orbit_full : ∀ σ : Perm (Fin 7), σ ^ 7 = 1 → σ ≠ 1 →
    ∀ i : Fin 7, ∃ k : Fin 7, (σ ^ (k : ℕ)) 0 = i :=
  A7AutFixPack.orbit_full_K

theorem centralizer_pow (σ : Perm (Fin 7)) (h7 : σ ^ 7 = 1) (h1 : σ ≠ 1)
    (π : Perm (Fin 7)) (hπ : Commute π σ) : ∃ k : ℕ, π = σ ^ k := by
  obtain ⟨j, hj⟩ := orbit_full σ h7 h1 (π 0)
  have hcomm : Commute ((σ ^ (j : ℕ))⁻¹ * π) σ :=
    (((Commute.refl σ).pow_left (j : ℕ)).inv_left).mul_left hπ
  have h0 : ((σ ^ (j : ℕ))⁻¹ * π) 0 = 0 := by
    rw [Equiv.Perm.mul_apply, ← hj, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hfix : ∀ i, ((σ ^ (j : ℕ))⁻¹ * π) i = i := by
    intro i
    obtain ⟨k, hk⟩ := orbit_full σ h7 h1 i
    have e1 := congrArg (fun f : Perm (Fin 7) => f 0) (hcomm.pow_right (k : ℕ)).eq
    simp only [Equiv.Perm.mul_apply, h0] at e1
    rw [← hk, Equiv.Perm.mul_apply]
    exact e1
  have hone : (σ ^ (j : ℕ))⁻¹ * π = 1 := Equiv.ext (fun i => by simpa using hfix i)
  exact ⟨j, (eq_of_inv_mul_eq_one hone).symm⟩

theorem perm_eq_one_of_commute (L : Subgroup (Perm (Fin 7))) (hL : Nat.card L = 168)
    (σ : Perm (Fin 7)) (hσ : ∀ l ∈ L, Commute σ l) : σ = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 7 (by rw [hL]; norm_num)
  have hord : orderOf (c : Perm (Fin 7)) = 7 := (Subgroup.orderOf_coe c).trans hc
  have hd7 : (c : Perm (Fin 7)) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one (c : Perm (Fin 7))
    rwa [hord] at h
  have hd1 : (c : Perm (Fin 7)) ≠ 1 := by
    intro h
    have h1 := hord
    rw [h, orderOf_one] at h1
    norm_num at h1
  obtain ⟨k, hk⟩ := centralizer_pow (c : Perm (Fin 7)) hd7 hd1 σ (hσ c c.2)
  have hσ7 : σ ^ 7 = 1 := by
    rw [hk, ← pow_mul, mul_comm, pow_mul, hd7, one_pow]
  by_contra hne
  have hLsub : L ≤ Subgroup.zpowers σ := by
    intro l hl
    obtain ⟨m, hm⟩ := centralizer_pow σ hσ7 hne l (hσ l hl).symm
    rw [hm]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) m
  have hcard : Nat.card L ≤ Nat.card (Subgroup.zpowers σ) := Subgroup.card_le_of_le hLsub
  rw [Nat.card_zpowers, hL] at hcard
  have hord : orderOf σ ≤ 7 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hσ7)
  omega

theorem fixes_imp_one {X : Type} [Group X]
    (hX : Nonempty (X ≃* alternatingGroup (Fin 7)))
    (L₀ : Subgroup X) (hL₀ : Nat.card L₀ = 168)
    (τ : MulAut X) (hfix : ∀ x ∈ L₀, τ x = x) : τ = 1 := by
  obtain ⟨e⟩ := hX
  let f : X →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact hxy
  have hL₁ : Nat.card (L₀.map f) = 168 := by
    rw [Subgroup.card_map_of_injective hf]
    exact hL₀
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by norm_num) (by norm_num)).2 (A7Inner.transportAut e τ)
  have hσ1 : σ = 1 := by
    apply perm_eq_one_of_commute (L₀.map f) hL₁ σ
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hl
    have h1 : MulAut.conjNormal σ (e x) = e x := by
      rw [hσ, A7Inner.transportAut_apply, e.symm_apply_apply, hfix x hx]
    have h2 : σ * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ⁻¹
        = ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
      congrArg Subtype.val h1
    show σ * ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7))
        = ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hφ : A7Inner.transportAut e τ = 1 := by
    rw [← hσ, hσ1, map_one]
  ext x
  have h : e (τ x) = e x := by
    have := congrArg (fun φ : MulAut (alternatingGroup (Fin 7)) => φ (e x)) hφ
    simpa [A7Inner.transportAut_apply] using this
  show τ x = x
  exact e.injective h

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7AutFix

end
