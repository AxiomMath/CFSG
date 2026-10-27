module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA5

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_conj_threeCyc012 :
    ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 → ∃ σ : Perm (Fin 5), σ * a * σ⁻¹ = threeCyc012 := by
  unfold threeCyc012
  decide +kernel

theorem exists_conj_threeCyc234 :
    ∀ a : Perm (Fin 5), a ^ 3 = 1 → a ≠ 1 → ∃ σ : Perm (Fin 5), σ * a * σ⁻¹ = threeCyc234 := by
  unfold threeCyc234
  decide +kernel

theorem sign_eq_one_of_odd {n : ℕ} {σ : Perm (Fin n)} (h : Odd (orderOf σ)) :
    Perm.sign σ = 1 := by
  have h1 : Perm.sign σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem mem_of_odd_mul {N X K : Subgroup G} (hNX : X ≤ Subgroup.normalizer (N : Set G))
    (hKX : K ≤ X) (hK2 : IsPGroup 2 K) {l k : G} (hl : l ∈ N) (hk : k ∈ K)
    (hodd : Odd (orderOf (l * k))) : l * k ∈ N := by
  obtain ⟨a, ha⟩ := hK2 ⟨k, hk⟩
  have hka : k ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have key : ∀ n : ℕ, ∃ l' ∈ N, (l * k) ^ n = l' * k ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hkn : k ^ n ∈ X := X.pow_mem (hKX hk) n
      have hc : k ^ n * l * (k ^ n)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hNX hkn) l).mp hl
      refine ⟨l' * (k ^ n * l * (k ^ n)⁻¹), N.mul_mem hl' hc, ?_⟩
      rw [pow_succ, he]
      group
  obtain ⟨l', hl', he⟩ := key (2 ^ a)
  rw [hka, mul_one] at he
  set x := l * k with hx
  set m := orderOf x with hm
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have : x = (x ^ 2 ^ a) ^ u := by
    have h1 : x ^ ((u * (2 ^ a : ℕ) + v * m : ℤ)) = x := by
      have : (u * (2 ^ a : ℕ) + v * m : ℤ) = 1 := by simpa using huv
      rw [this, zpow_one]
    have h2 : x ^ ((u * (2 ^ a : ℕ) + v * m : ℤ)) = (x ^ 2 ^ a) ^ u := by
      rw [zpow_add, mul_comm u, zpow_mul, mul_comm v, zpow_mul, zpow_natCast, zpow_natCast, hm,
        pow_orderOf_eq_one]
      simp
    rw [← h2, h1]
  rw [this, he]
  exact N.zpow_mem hl' u

section Psi

variable {X K : Subgroup G} {c : G} (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)

include hψs

theorem alt5_le_map_conjClosure (hcX : c ∈ X) (hc3 : c ^ 3 = 1) (hcne : ψ ⟨c, hcX⟩ ≠ 1) :
    alternatingGroup (Fin 5) ≤ ((conjClosure X c).subgroupOf X).map ψ := by
  have ha3 : ψ ⟨c, hcX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hmem : ∀ σ : Perm (Fin 5), σ * ψ ⟨c, hcX⟩ * σ⁻¹ ∈
      ((conjClosure X c).subgroupOf X).map ψ := by
    intro σ
    obtain ⟨g, rfl⟩ := hψs σ
    refine ⟨g * ⟨c, hcX⟩ * g⁻¹, ?_, by simp⟩
    show _ ∈ (conjClosure X c).subgroupOf X
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨g, g.2, rfl⟩
  obtain ⟨σ₁, h₁⟩ := exists_conj_threeCyc012 _ ha3 hcne
  obtain ⟨σ₂, h₂⟩ := exists_conj_threeCyc234 _ ha3 hcne
  refine alt5_le_closure_threeCycles.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ (rfl | rfl)
  · exact h₁ ▸ hmem σ₁
  · exact h₂ ▸ hmem σ₂

theorem oTwoRes_le_conjClosure (hKX : K ≤ X) (hK2 : IsPGroup 2 K)
    (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K) (hcX : c ∈ X) (hc3 : c ^ 3 = 1)
    (hcne : ψ ⟨c, hcX⟩ ≠ 1) : oTwoRes X ≤ conjClosure X c := by
  have hnorm : X ≤ Subgroup.normalizer (conjClosure X c : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_conjClosure hy hg, fun hy => ?_⟩
    have := conj_mem_conjClosure hy (X.inv_mem hg)
    simpa [mul_assoc] using this
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxX, m, hm, hxm⟩
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)
  have hψodd : Odd (orderOf (ψ ⟨x, hxX⟩)) := by
    refine Odd.of_dvd_nat hodd ?_
    have := orderOf_map_dvd ψ (⟨x, hxX⟩ : ↥X)
    simpa using this
  have hsign := sign_eq_one_of_odd hψodd
  have hA : ψ ⟨x, hxX⟩ ∈ alternatingGroup (Fin 5) := Perm.mem_alternatingGroup.mpr hsign
  obtain ⟨y, hy, hyx⟩ := alt5_le_map_conjClosure ψ hψs hcX hc3 hcne hA
  have hyc : (y : G) ∈ conjClosure X c := hy
  have hk : (y : G)⁻¹ * x ∈ K := by
    rw [← hker ⟨_, X.mul_mem (X.inv_mem y.2) hxX⟩]
    have : (⟨(y : G)⁻¹ * x, X.mul_mem (X.inv_mem y.2) hxX⟩ : ↥X) = y⁻¹ * ⟨x, hxX⟩ := rfl
    rw [this, map_mul, map_inv, hyx, inv_mul_cancel]
  have hxe : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hxe]
  rw [hxe] at hodd
  exact mem_of_odd_mul hnorm hKX hK2 hyc hk hodd

end Psi

end CFSG.Quasithin.F53
