module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne.KE

theorem relIndex_dvd_of_le_of_index_dvd {G : Type*} [Group G] {N X R : Subgroup G} (hXR : X ≤ R)
    [(N.subgroupOf R).Normal] {m : ℕ} (hm : (N.subgroupOf R).index ∣ m) :
    N.relIndex X ∣ m := by
  have h1 : (N.subgroupOf R).relIndex (X.subgroupOf R) ∣ (N.subgroupOf R).index :=
    Subgroup.relIndex_dvd_index_of_normal _ _
  rw [Subgroup.relIndex_subgroupOf hXR] at h1
  exact h1.trans hm

theorem le_of_isPGroup_of_index_eq_pow {G : Type*} [Group G] {N R P : Subgroup G} (hPR : P ≤ R)
    [(N.subgroupOf R).Normal] {p ℓ k : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    (hidx : (N.subgroupOf R).index = ℓ ^ k) [Finite P] (hP : IsPGroup p P) : P ≤ N := by
  have : Fact p.Prime := ⟨hp⟩
  have hrel : N.relIndex P ∣ ℓ ^ k :=
    relIndex_dvd_of_le_of_index_dvd hPR (hidx ▸ dvd_rfl)
  obtain ⟨n, hn⟩ := hP.index (N.subgroupOf P)
  have hn' : N.relIndex P = p ^ n := hn
  rw [hn'] at hrel
  have hcop : Nat.Coprime (p ^ n) (ℓ ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hℓ).2 hpℓ)
  have h1 : p ^ n = 1 := Nat.Coprime.eq_one_of_dvd hcop hrel
  have h2 : (N.subgroupOf P).index = 1 := hn.trans h1
  intro x hx
  have := Subgroup.index_eq_one.1 h2
  have hx' : (⟨x, hx⟩ : P) ∈ N.subgroupOf P := by rw [this]; exact Subgroup.mem_top _
  exact hx'

end CFSG.RankThree.PartOne.KE
