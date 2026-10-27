module

public import CFSG.Quasithin.Background.C126A5PermBasic

public section

namespace CFSG.Quasithin.C126.A5

open Equiv Equiv.Perm

def kS : Finset (Perm (Fin 5)) := {1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3}

def c3 : Perm (Fin 5) := swap 2 3 * swap 3 4

set_option synthInstance.maxSize 2000 in
theorem coset_five : ∀ g : Perm (Fin 5), g ∉ kS →
    g * swap 0 1 * g⁻¹ ∈ kS → g * swap 2 3 * g⁻¹ ∈ kS →
    ∃ v ∈ kS, (c3 * (g * v)) ^ 5 = 1 ∧ c3 * (g * v) ≠ 1 := by
  unfold kS c3
  decide +kernel

theorem kS_mul : ∀ x ∈ kS, ∀ y ∈ kS, x * y ∈ kS := by
  unfold kS
  decide +kernel

theorem kS_inv : ∀ x ∈ kS, x⁻¹ ∈ kS := by
  unfold kS
  decide +kernel

theorem kS_card : kS.card = 4 := by
  unfold kS
  decide +kernel

def K0 : Subgroup (Perm (Fin 5)) where
  carrier := ↑kS
  one_mem' := by simp [kS]
  mul_mem' := fun {x y} hx hy => kS_mul x hx y hy
  inv_mem' := fun {x} hx => kS_inv x hx

theorem mem_K0 {x : Perm (Fin 5)} : x ∈ K0 ↔ x ∈ kS := Iff.rfl

theorem card_K0 : Nat.card K0 = 4 := by
  have : Nat.card K0 = kS.card := by
    simp [K0, Nat.card_eq_fintype_card]
  rw [this, kS_card]

theorem closure_cycle_std (D : Subgroup (Perm (Fin 5))) (hD : Nat.card D = 8)
    (h1 : swap 0 1 ∈ D) (h2 : swap 2 3 ∈ D) :
    D ⊔ Subgroup.closure {c3} = ⊤ := by
  have hK : K0 ≤ D := by
    intro x hx
    have hx' : x ∈ kS := hx
    unfold kS at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact D.one_mem
    · exact h1
    · exact h2
    · exact D.mul_mem h1 h2
  have hidx : (K0.subgroupOf D).index = 2 := by
    have h := Subgroup.relIndex_mul_card K0 D
    rw [inf_eq_left.2 hK, card_K0, hD] at h
    exact (show K0.relIndex D = 2 by omega)
  have hnorm : (K0.subgroupOf D).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨g, hgD, hgK⟩ : ∃ g ∈ D, g ∉ K0 := by
    by_contra hcon
    push Not at hcon
    have hle : D ≤ K0 := hcon
    have := Subgroup.card_le_of_le hle
    have := card_K0
    omega
  have hcj : ∀ k ∈ K0, g * k * g⁻¹ ∈ K0 := by
    intro k hk
    have := hnorm.conj_mem ⟨k, hK hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨g, hgD⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hs : swap 0 1 ∈ K0 := by simp [mem_K0, kS]
  have ht : swap 2 3 ∈ K0 := by simp [mem_K0, kS]
  obtain ⟨v, hv, hp5, hp1⟩ := coset_five g hgK (hcj _ hs) (hcj _ ht)
  have hvD : v ∈ D := hK hv
  set p := c3 * (g * v) with hp
  have hpX : p ∈ D ⊔ Subgroup.closure {c3} :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
      (Subgroup.mem_sup_left (D.mul_mem hgD hvD))
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf p = 5 := orderOf_eq_prime (by simpa using hp5) hp1
  have hcard : p.support.card < 2 * orderOf p := by
    rw [hord]
    have := Finset.card_le_univ p.support
    simp at this
    omega
  have hcyc : p.IsCycle := isCycle_of_prime_order (by rw [hord]; exact Nat.prime_five) hcard
  have hsupp : p.support = Finset.univ := by
    have h5 : p.support.card = 5 := by rw [← hcyc.orderOf, hord]
    exact Finset.eq_univ_of_card _ (by simpa using h5)
  have htop := closure_prime_cycle_swap (σ := p) (τ := swap 0 1)
    (by simpa using Nat.prime_five) hcyc hsupp ⟨0, 1, by decide, rfl⟩
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact hpX
  · exact Subgroup.mem_sup_left h1

theorem closure_cycle (π : Perm (Fin 5)) (D : Subgroup (Perm (Fin 5))) (hD : Nat.card D = 8)
    (h1 : swap (π 0) (π 1) ∈ D) (h2 : swap (π 2) (π 3) ∈ D) :
    D ⊔ Subgroup.closure {cyc3 π} = ⊤ := by
  set ψ : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj π).toMonoidHom with hψ
  set ψ' : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj π⁻¹).toMonoidHom with hψ'
  have hψψ' : ∀ g, ψ (ψ' g) = g := fun g => by simp [hψ, hψ']; group
  have hinj' : Function.Injective ψ' := Function.LeftInverse.injective hψψ'
  have hsurj : Function.Surjective ψ := Function.RightInverse.surjective hψψ'
  set D₁ : Subgroup (Perm (Fin 5)) := D.map ψ' with hD₁
  have hcard : Nat.card D₁ = 8 := by
    rw [hD₁, Subgroup.card_map_of_injective hinj', hD]
  have hsw : ∀ x y : Fin 5, ψ' (swap (π x) (π y)) = swap x y := by
    intro x y
    rw [swap_apply_apply π x y]
    simp [hψ']
    group
  have h1' : swap 0 1 ∈ D₁ := ⟨_, h1, hsw 0 1⟩
  have h2' : swap 2 3 ∈ D₁ := ⟨_, h2, hsw 2 3⟩
  have h := closure_cycle_std D₁ hcard h1' h2'
  have hmap := congrArg (Subgroup.map ψ) h
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective ψ hsurj, MonoidHom.map_closure,
    Set.image_singleton] at hmap
  have hD' : Subgroup.map ψ D₁ = D := by
    rw [hD₁, Subgroup.map_map]
    have : ψ.comp ψ' = MonoidHom.id _ := MonoidHom.ext fun g => hψψ' g
    rw [this, Subgroup.map_id]
  have hc : ψ c3 = cyc3 π := by
    unfold c3 cyc3
    rw [map_mul]
    have e : ∀ x y : Fin 5, ψ (swap x y) = swap (π x) (π y) := by
      intro x y
      rw [swap_apply_apply π x y]
      simp [hψ]
    rw [e, e]
  rw [hD', hc] at hmap
  exact hmap

end CFSG.Quasithin.C126.A5
