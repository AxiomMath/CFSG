module

public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.EmptyFaithful.S153E59C
public import CFSG.Quasithin.EmptyFaithful.S153EGen

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

namespace S153EH60

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def c3M : M3 := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def t3M : M3 := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem c3M_cube : c3M * c3M * c3M = 1 := by decide

theorem c3M_ne : c3M ≠ 1 := by decide

theorem t3M_sq : t3M * t3M = 1 := by decide

theorem t3M_conj : t3M * c3M * t3M = c3M * c3M := by decide

set_option maxRecDepth 100000 in
theorem no_comm_c3M : ∀ N : M3, N * N = 1 → N ≠ 1 → N * c3M ≠ c3M * N := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem card_fix_M3 : ∀ M : M3, M * M * M = 1 → M ≠ 1 →
    (Finset.univ.filter (fun m : Fin 3 → ZMod 2 => M *ᵥ m = m)).card = 2 ∧
    (Finset.univ.filter (fun m : Fin 3 → ZMod 2 => (M * M)ᵀ *ᵥ m = m)).card = 2 := by
  decide +kernel

abbrev L32 : Type := ↥(StatedSL 3 (ZMod 2))

@[expose] def c3GL : GL (Fin 3) (ZMod 2) := ⟨c3M, c3M * c3M, by decide, by decide⟩

@[expose] def t3GL : GL (Fin 3) (ZMod 2) := ⟨t3M, t3M, by decide, by decide⟩

@[expose] def c3L : L32 := ⟨c3GL, S153E58.mem_statedSL_three_two _⟩

@[expose] def t3L : L32 := ⟨t3GL, S153E58.mem_statedSL_three_two _⟩

@[expose] def matL (γ : L32) : M3 := ((γ : GL (Fin 3) (ZMod 2)) : M3)

theorem matL_mul (γ δ : L32) : matL (γ * δ) = matL γ * matL δ := rfl

theorem matL_one : matL 1 = 1 := rfl

theorem matL_inj : Function.Injective matL := fun _ _ h => Subtype.ext (Units.ext h)

theorem matL_c3L : matL c3L = c3M := rfl

theorem matL_t3L : matL t3L = t3M := rfl

theorem c3L_pow_three : c3L ^ 3 = 1 := by
  apply matL_inj
  rw [pow_three', matL_mul, matL_mul, matL_c3L, c3M_cube, matL_one]

theorem c3L_ne_one : c3L ≠ 1 := by
  intro h
  exact c3M_ne (by rw [← matL_c3L, h, matL_one])

theorem orderOf_c3L : orderOf c3L = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c3L_pow_three c3L_ne_one

theorem t3L_mul_self : t3L * t3L = 1 := by
  apply matL_inj
  rw [matL_mul, matL_t3L, t3M_sq, matL_one]

theorem t3L_inv : t3L⁻¹ = t3L := inv_eq_of_mul_eq_one_right t3L_mul_self

theorem t3L_conj : t3L * c3L * t3L⁻¹ = c3L⁻¹ := by
  have h1 : c3L⁻¹ = c3L * c3L := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_three, c3L_pow_three]
  rw [t3L_inv, h1]
  apply matL_inj
  rw [matL_mul, matL_mul, matL_mul, matL_t3L, matL_c3L, t3M_conj]

section Order3

variable {γ : L32}

theorem pow_three_eq_one (hγ : orderOf γ = 3) : γ ^ 3 = 1 := by
  have := pow_orderOf_eq_one γ
  rwa [hγ] at this

theorem ne_one_of_order_three (hγ : orderOf γ = 3) : γ ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hγ
  omega

theorem matL_cube (hγ : orderOf γ = 3) : matL γ * matL γ * matL γ = 1 := by
  rw [← matL_mul, ← matL_mul, ← pow_three', pow_three_eq_one hγ, matL_one]

theorem matL_ne_one (hγ : orderOf γ = 3) : matL γ ≠ 1 := by
  intro h
  exact ne_one_of_order_three hγ (matL_inj (by rw [h, matL_one]))

theorem inv_eq_mul_self (hγ : orderOf γ = 3) : γ⁻¹ = γ * γ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_three, pow_three_eq_one hγ]

theorem matL_inv (hγ : orderOf γ = 3) : matL γ⁻¹ = matL γ * matL γ := by
  rw [inv_eq_mul_self hγ, matL_mul]

theorem card_fix_nat (hγ : orderOf γ = 3) :
    Nat.card {m : S153E58.V3 // natAct (StatedSL 3 (ZMod 2)) γ m = m} = 2 := by
  have h := (card_fix_M3 (matL γ) (matL_cube hγ) (matL_ne_one hγ)).1
  have e : {m : S153E58.V3 // natAct (StatedSL 3 (ZMod 2)) γ m = m} ≃
      {v : Fin 3 → ZMod 2 // matL γ *ᵥ v = v} :=
    Equiv.subtypeEquiv Multiplicative.toAdd (fun m => by
      change Multiplicative.ofAdd (matL γ *ᵥ Multiplicative.toAdd m) = m ↔ _
      constructor
      · intro h1
        have := congrArg Multiplicative.toAdd h1
        simpa using this
      · intro h1
        rw [h1]
        rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, h]

theorem card_fix_dual (hγ : orderOf γ = 3) :
    Nat.card {m : S153E58.V3 // dualNatAct (StatedSL 3 (ZMod 2)) γ m = m} = 2 := by
  have h := (card_fix_M3 (matL γ) (matL_cube hγ) (matL_ne_one hγ)).2
  have e : {m : S153E58.V3 // dualNatAct (StatedSL 3 (ZMod 2)) γ m = m} ≃
      {v : Fin 3 → ZMod 2 // (matL γ * matL γ)ᵀ *ᵥ v = v} :=
    Equiv.subtypeEquiv Multiplicative.toAdd (fun m => by
      change Multiplicative.ofAdd ((matL γ⁻¹)ᵀ *ᵥ Multiplicative.toAdd m) = m ↔ _
      rw [matL_inv hγ]
      constructor
      · intro h1
        have := congrArg Multiplicative.toAdd h1
        simpa using this
      · intro h1
        rw [h1]
        rfl)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, h]

end Order3

theorem eq_or_eq_inv_of_mem_zpowers {G : Type*} [Group G] {a x : G} (ha : orderOf a = 3)
    (hx : x ∈ Subgroup.zpowers a) (hx3 : orderOf x = 3) : x = a ∨ x = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : a ^ (k % 3) = a ^ k := by
    have := zpow_mod_orderOf a k
    rwa [ha] at this
  have ha3 : a ^ 3 = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with hk | hk | hk
  · rw [hk, zpow_zero] at h1
    rw [← h1, orderOf_one] at hx3
    omega
  · left
    rw [hk, zpow_one] at h1
    exact h1.symm
  · right
    rw [hk] at h1
    rw [← h1]
    apply eq_inv_of_mul_eq_one_left
    calc a ^ (2 : ℤ) * a = a ^ 3 := by rw [zpow_two, pow_three', mul_assoc]
      _ = 1 := ha3

theorem exists_conj_c3 {γ : L32} (hγ : orderOf γ = 3) : ∃ η : L32, η * γ * η⁻¹ = c3L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card L32 = 168 := S153E59.card_statedSL_three_two
  have hP : Subgroup.zpowers c3L ≤ ⊤ ∧ IsPGroup 3 (Subgroup.zpowers c3L) ∧
      ¬ 3 ∣ (Subgroup.zpowers c3L).relIndex ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 1) ?_, ?_⟩
    · rw [Nat.card_zpowers, orderOf_c3L]
      norm_num
    · rw [Subgroup.relIndex_top_right]
      have h1 := Subgroup.card_mul_index (Subgroup.zpowers c3L)
      rw [Nat.card_zpowers, orderOf_c3L, hcard] at h1
      omega
  have hQ : IsPGroup 3 (Subgroup.zpowers γ) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hγ]
    norm_num
  obtain ⟨k, -, hk⟩ := S153E.exists_conj_of_isSylow hP hQ le_top
  have hk' : k * γ * k⁻¹ ∈ Subgroup.zpowers c3L := mem_conjSubgroup_iff.mp (hk (Subgroup.mem_zpowers γ))
  have hk3 : orderOf (k * γ * k⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hγ
  rcases eq_or_eq_inv_of_mem_zpowers orderOf_c3L hk' hk3 with h | h
  · exact ⟨k, h⟩
  · refine ⟨t3L * k, ?_⟩
    calc t3L * k * γ * (t3L * k)⁻¹ = t3L * (k * γ * k⁻¹) * t3L⁻¹ := by group
      _ = t3L * c3L⁻¹ * t3L⁻¹ := by rw [h]
      _ = (t3L * c3L * t3L⁻¹)⁻¹ := by group
      _ = c3L := by rw [t3L_conj, inv_inv]

theorem mul_self_eq_one_of_order_two {η : L32} (h : orderOf η = 2) : η * η = 1 := by
  have := pow_orderOf_eq_one η
  rwa [h, pow_two] at this

theorem no_comm_of_order {γ η : L32} (hγ : orderOf γ = 3) (hη : orderOf η = 2) :
    γ * η ≠ η * γ := by
  intro hcomm
  obtain ⟨ζ, hζ⟩ := exists_conj_c3 hγ
  have h1 : c3L * (ζ * η * ζ⁻¹) = (ζ * η * ζ⁻¹) * c3L := by
    rw [← hζ]
    calc ζ * γ * ζ⁻¹ * (ζ * η * ζ⁻¹) = ζ * (γ * η) * ζ⁻¹ := by group
      _ = ζ * (η * γ) * ζ⁻¹ := by rw [hcomm]
      _ = ζ * η * ζ⁻¹ * (ζ * γ * ζ⁻¹) := by group
  have h2 : (ζ * η * ζ⁻¹) * (ζ * η * ζ⁻¹) = 1 := by
    calc (ζ * η * ζ⁻¹) * (ζ * η * ζ⁻¹) = ζ * (η * η) * ζ⁻¹ := by group
      _ = 1 := by rw [mul_self_eq_one_of_order_two hη]; group
  have h3 : ζ * η * ζ⁻¹ ≠ 1 := by
    intro h
    have : η = 1 := by
      calc η = ζ⁻¹ * (ζ * η * ζ⁻¹) * ζ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hη
    omega
  refine no_comm_c3M (matL (ζ * η * ζ⁻¹)) ?_ ?_ ?_
  · rw [← matL_mul, h2, matL_one]
  · intro h
    exact h3 (matL_inj (by rw [h, matL_one]))
  · rw [← matL_c3L, ← matL_mul, ← matL_mul, h1]

theorem exists_inv_conj {γ : L32} (hγ : orderOf γ = 3) : ∃ η : L32, η * γ * η⁻¹ = γ⁻¹ := by
  obtain ⟨ζ, hζ⟩ := exists_conj_c3 hγ
  refine ⟨ζ⁻¹ * t3L * ζ, ?_⟩
  have hγ' : γ = ζ⁻¹ * c3L * ζ := by rw [← hζ]; group
  rw [hγ']
  calc ζ⁻¹ * t3L * ζ * (ζ⁻¹ * c3L * ζ) * (ζ⁻¹ * t3L * ζ)⁻¹ = ζ⁻¹ * (t3L * c3L * t3L⁻¹) * ζ := by group
    _ = ζ⁻¹ * c3L⁻¹ * ζ := by rw [t3L_conj]
    _ = (ζ⁻¹ * c3L * ζ)⁻¹ := by group

end S153EH60

end CFSG.Quasithin
