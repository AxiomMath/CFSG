module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G10

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem card_eight_of_sylow {P : Subgroup L3.Γ} (hP : IsSylowTwoOf P ⊤) : Nat.card P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.2.1.exists_card_eq
  have h1 := Subgroup.card_mul_index P
  rw [card_SL_three_two, hk] at h1
  have h2 : ¬ 2 ∣ P.index := by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
  have hk8 : k < 8 := by
    by_contra hk8
    have h3 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ k ≤ 168 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
    omega
  rw [hk]
  interval_cases k <;> norm_num at h1 ⊢ <;> omega

variable [Finite G] {T L I : Subgroup G}

theorem exists_three_lift (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I)
    (ρ : ↥L →* L3.Γ) (hρ : Function.Surjective ρ)
    (hker : ∀ l : ↥L, ρ l = 1 → (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G))
    {γ : L3.Γ} (hγ3 : γ ^ 3 = 1) (hγ1 : γ ≠ 1) :
    ∃ l : ↥L, orderOf (l : G) = 3 ∧ ∃ m : ℕ, ¬ 3 ∣ m ∧ ρ l = γ ^ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l₀, hl₀⟩ := hρ γ
  obtain ⟨e, m, hm3, hme⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos (l₀ : G)).ne' 3 (by norm_num)
  have hγm1 : γ ^ m ≠ 1 := by
    intro h
    have h1 : orderOf γ ∣ m := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime hγ3 hγ1] at h1
    exact hm3 h1
  refine ⟨l₀ ^ m, ?_, m, hm3, by rw [map_pow, hl₀]⟩
  have hl3e : ((l₀ ^ m : ↥L) : G) ^ 3 ^ e = 1 := by
    rw [Subgroup.coe_pow, ← pow_mul, mul_comm, ← hme, pow_orderOf_eq_one]
  have hl3C : ((l₀ ^ m : ↥L) : G) ^ 3 ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
    have := hker ((l₀ ^ m) ^ 3) (by rw [map_pow, map_pow, hl₀, ← pow_mul, mul_comm, pow_mul,
      hγ3, one_pow])
    simpa using this
  have hl3 : ((l₀ ^ m : ↥L) : G) ^ 3 = 1 :=
    eq_one_of_odd_of_centralizer h37 h38 h1011 hyp (L.pow_mem (l₀ ^ m).2 3) hl3C (n := 3 ^ e)
      (by rw [← pow_mul, mul_comm, pow_mul, hl3e, one_pow]) (Odd.pow (by decide))
  refine orderOf_eq_prime hl3 fun h1 => hγm1 ?_
  have h2 : l₀ ^ m = 1 := Subtype.ext h1
  have h3 := congrArg ρ h2
  rwa [map_pow, hl₀, map_one] at h3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
