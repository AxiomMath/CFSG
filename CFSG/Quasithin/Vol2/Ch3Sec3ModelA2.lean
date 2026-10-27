module

public import CFSG.Quasithin.Vol2.Ch3Sec3S6Sylow
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Act

public section

namespace CFSG.Quasithin.H13.ModelA2

open A6Coc S6Syl

@[expose] def x₁ : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def x₂ : Equiv.Perm (Fin 6) := Equiv.swap 4 5

@[expose] def x₃ : Equiv.Perm (Fin 6) := x₁ * x₂

@[expose] def fixU0 (X : Subgroup (Equiv.Perm (Fin 6))) : Set Vec4 :=
  {v | ∀ x ∈ X, act x v = v}

theorem x_facts : x₁ ^ 2 = 1 ∧ x₂ ^ 2 = 1 ∧ x₃ ^ 2 = 1 ∧ x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₃ ≠ 1 ∧
    x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧ x₁ * x₂ = x₃ ∧ x₁ * x₃ = x₂ ∧ x₂ * x₃ = x₁ ∧
    x₂ * x₁ = x₃ ∧ x₃ * x₁ = x₂ ∧ x₃ * x₂ = x₁ := by
  decide +kernel

theorem mem_elemsA (x : Equiv.Perm (Fin 6)) : x ∈ elemsA ↔ x = 1 ∨ x = x₁ ∨ x = x₂ ∨ x = x₃ := by
  simp [elemsA, x₁, x₂, x₃]

theorem orderOf_eq_two {x : Equiv.Perm (Fin 6)} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) : orderOf x = 2 :=
  orderOf_eq_prime h2 h1

theorem mem_zpowers_iff {x y : Equiv.Perm (Fin 6)} (h2 : x ^ 2 = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero hk
      simp only [hm, zpow_mul]
      rw [zpow_ofNat, h2, one_zpow]
    · right
      have e : k = 2 * (k / 2) + 1 := by omega
      simp only
      rw [e, zpow_add, zpow_mul, zpow_ofNat, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem subgroup_cases {X : Subgroup (Equiv.Perm (Fin 6))} (hX : X ≤ aBar2) :
    X = ⊥ ∨ X = Subgroup.zpowers x₁ ∨ X = Subgroup.zpowers x₂ ∨ X = Subgroup.zpowers x₃ ∨
      X = aBar2 := by
  obtain ⟨h1₂, h2₂, h3₂, -, -, -, -, -, -, h12, h13, h23, -, -, -⟩ := x_facts
  have hel : ∀ y ∈ X, y = 1 ∨ y = x₁ ∨ y = x₂ ∨ y = x₃ := fun y hy =>
    (mem_elemsA y).mp ((aBar2_eq y).mp (hX hy))
  have hA : ∀ y : Equiv.Perm (Fin 6), y ∈ aBar2 ↔ y = 1 ∨ y = x₁ ∨ y = x₂ ∨ y = x₃ := fun y =>
    (aBar2_eq y).trans (mem_elemsA y)
  by_cases a₁ : x₁ ∈ X <;> by_cases a₂ : x₂ ∈ X <;> by_cases a₃ : x₃ ∈ X
  ·
    right; right; right; right
    refine le_antisymm hX fun y hy => ?_
    rcases (hA y).mp hy with rfl | rfl | rfl | rfl
    · exact X.one_mem
    · exact a₁
    · exact a₂
    · exact a₃
  · exact absurd (h12 ▸ X.mul_mem a₁ a₂) a₃
  · exact absurd (h13 ▸ X.mul_mem a₁ a₃) a₂
  · right; left
    refine le_antisymm (fun y hy => ?_) ((Subgroup.zpowers_le).mpr a₁)
    rw [mem_zpowers_iff h1₂]
    rcases hel y hy with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hy a₂
    · exact absurd hy a₃
  · exact absurd (h23 ▸ X.mul_mem a₂ a₃) a₁
  · right; right; left
    refine le_antisymm (fun y hy => ?_) ((Subgroup.zpowers_le).mpr a₂)
    rw [mem_zpowers_iff h2₂]
    rcases hel y hy with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hy a₁
    · exact Or.inr rfl
    · exact absurd hy a₃
  · right; right; right; left
    refine le_antisymm (fun y hy => ?_) ((Subgroup.zpowers_le).mpr a₃)
    rw [mem_zpowers_iff h3₂]
    rcases hel y hy with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hy a₁
    · exact absurd hy a₂
    · exact Or.inr rfl
  · left
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [Subgroup.mem_bot]
    rcases hel y hy with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hy a₁
    · exact absurd hy a₂
    · exact absurd hy a₃

theorem fix_check : (Finset.univ.filter fun v : Vec4 => act x₁ v = v).card = 4 ∧
    (Finset.univ.filter fun v : Vec4 => act x₂ v = v).card = 8 ∧
    (Finset.univ.filter fun v : Vec4 => act x₃ v = v).card = 4 ∧
    ∀ v : Vec4, act x₁ v = v → act x₂ v = v := by
  decide +kernel

theorem fixU0_bot : fixU0 ⊥ = Set.univ := by
  ext v
  simp only [fixU0, Subgroup.mem_bot, forall_eq, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact act_one v

theorem fixU0_zpowers (x : Equiv.Perm (Fin 6)) :
    fixU0 (Subgroup.zpowers x) = {v | act x v = v} := by
  ext v
  simp only [fixU0, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    let H : Subgroup (Equiv.Perm (Fin 6)) :=
      { carrier := {y | act y v = v}
        one_mem' := act_one v
        mul_mem' := fun {a b} ha hb => by
          show act (a * b) v = v
          rw [act_mul, hb, ha]
        inv_mem' := fun {a} ha => by
          show act a⁻¹ v = v
          have := congrArg (act a⁻¹) ha
          rw [← act_mul, inv_mul_cancel, act_one] at this
          exact this.symm }
    exact (Subgroup.zpowers_le.mpr h : Subgroup.zpowers x ≤ H) hy

theorem fixU0_aBar2 : fixU0 aBar2 = {v | act x₁ v = v} := by
  obtain ⟨-, -, -, h⟩ := fix_check
  ext v
  simp only [fixU0, Set.mem_ofPred_eq]
  constructor
  · intro hv
    exact hv x₁ ((aBar2_eq x₁).mpr ((mem_elemsA x₁).mpr (Or.inr (Or.inl rfl))))
  · intro hv y hy
    have h2 := h v hv
    have h3 : act x₃ v = v := by rw [x₃, act_mul, h2, hv]
    rcases (mem_elemsA y).mp ((aBar2_eq y).mp hy) with rfl | rfl | rfl | rfl
    · exact act_one v
    · exact hv
    · exact h2
    · exact h3

theorem card_filter_eq (x : Equiv.Perm (Fin 6)) :
    Nat.card {v : Vec4 // act x v = v} = (Finset.univ.filter fun v : Vec4 => act x v = v).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] noncomputable def weight (X : Subgroup (Equiv.Perm (Fin 6))) : ℕ :=
  Nat.card X * Nat.card (fixU0 X)

theorem card_zpowers_of {x : Equiv.Perm (Fin 6)} (h2 : x ^ 2 = 1) (h1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_two h2 h1]

theorem card_aBar2 : Nat.card aBar2 = 4 := by
  have hnd : elemsA.Nodup := by decide +kernel
  have h : Nat.card aBar2 = elemsA.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [aBar2_eq, List.mem_toFinset])
  rw [h, List.toFinset_card_of_nodup hnd]
  rfl

theorem weight_values : weight ⊥ = 16 ∧ weight (Subgroup.zpowers x₁) = 8 ∧
    weight (Subgroup.zpowers x₂) = 16 ∧ weight (Subgroup.zpowers x₃) = 8 ∧ weight aBar2 = 16 := by
  obtain ⟨h1₂, h2₂, h3₂, n1, n2, n3, -⟩ := x_facts
  obtain ⟨c1, c2, c3, -⟩ := fix_check
  have hz : ∀ x : Equiv.Perm (Fin 6), Nat.card (fixU0 (Subgroup.zpowers x)) =
      (Finset.univ.filter fun v : Vec4 => act x v = v).card := fun x => by
    rw [fixU0_zpowers, ← card_filter_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [weight, fixU0_bot, Subgroup.card_bot, Nat.card_univ, one_mul, Nat.card_eq_fintype_card]
    decide
  · rw [weight, card_zpowers_of h1₂ n1, hz, c1]
  · rw [weight, card_zpowers_of h2₂ n2, hz, c2]
  · rw [weight, card_zpowers_of h3₂ n3, hz, c3]
  · rw [weight, card_aBar2, fixU0_aBar2]
    have : Nat.card {v : Vec4 | act x₁ v = v} = 4 := by
      rw [show ({v : Vec4 | act x₁ v = v} : Set Vec4) = {v | act x₁ v = v} from rfl]
      have := card_filter_eq x₁
      rw [c1] at this
      exact this
    rw [this]

end CFSG.Quasithin.H13.ModelA2
