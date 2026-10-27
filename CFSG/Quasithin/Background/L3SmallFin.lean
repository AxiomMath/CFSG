module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.L3Small

open CFSG.Quasithin L3

theorem isSimpleGroup_Γ : IsSimpleGroup Γ := by
  have hc : Subgroup.center Γ = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA, hr1]; simp)
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have e : Γ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

theorem card_Γ : Nat.card Γ = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def c₀ : Γ := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

@[expose] def a₀ : Γ := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩

theorem c₀_pow : c₀ ^ 3 = 1 := by decide

theorem c₀_ne_one : c₀ ≠ 1 := by decide

theorem a₀_mul_self : a₀ * a₀ = 1 := by decide

theorem a₀_mul_c₀_pow : (a₀ * c₀) ^ 7 = 1 := by decide

theorem comm_a₀_c₀_pow : (a₀ * c₀ * a₀ * c₀ * c₀) ^ 4 = 1 := by decide

theorem conj_c₀ : ∀ c : Γ, c ^ 3 = 1 → c ≠ 1 → ∃ h : Γ, h * c₀ * h⁻¹ = c := by
  decide +kernel

theorem orderOf_seven : orderOf (c₀ * (a₀ * c₀ * a₀)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_four : orderOf (c₀ * (a₀ * c₀ * a₀) ^ 2) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c₀ * (a₀ * c₀ * a₀) ^ 2)
    (by decide) (by decide)
  simpa using h

theorem closure_c₀ : Subgroup.closure ({c₀, a₀ * c₀ * a₀} : Set Γ) = ⊤ := by
  set X := Subgroup.closure ({c₀, a₀ * c₀ * a₀} : Set Γ) with hX
  have h1 : c₀ ∈ X := Subgroup.subset_closure (Or.inl rfl)
  have h2 : a₀ * c₀ * a₀ ∈ X := Subgroup.subset_closure (Or.inr rfl)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have d3 : 3 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X h1
    rwa [orderOf_eq_prime c₀_pow c₀_ne_one] at this
  have d7 : 7 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (X.mul_mem h1 h2)
    rwa [orderOf_seven] at this
  have d4 : 4 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (X.mul_mem h1 (X.pow_mem h2 2))
    rwa [orderOf_four] at this
  have d84 : 84 ∣ Nat.card X := by
    have h12 : 12 ∣ Nat.card X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 d4
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 d7
  have hmul := Subgroup.card_mul_index X
  rw [card_Γ] at hmul
  obtain ⟨k, hk⟩ := d84
  have hki : k * X.index = 2 := by
    have h3 : 84 * (k * X.index) = 84 * 2 := by
      rw [← mul_assoc, ← hk]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hk2 : k ∣ 2 := ⟨X.index, hki.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  ·
    exfalso
    have hidx : X.index = 2 := by omega
    have : IsSimpleGroup Γ := isSimpleGroup_Γ
    have : X.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h0 | h0
    · rw [h0] at h1
      exact c₀_ne_one (Subgroup.mem_bot.mp h1)
    · rw [h0, Subgroup.index_top] at hidx
      norm_num at hidx
  · have hidx : X.index = 1 := by omega
    exact Subgroup.index_eq_one.mp hidx

abbrev V4 := Fin 4 → ZMod 2

@[expose] def swap4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def blk (X Y : Fin 2 → Fin 2 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; Y 0 0, Y 0 1, 1, 0; Y 1 0, Y 1 1, 0, 1]

@[expose] def stepS (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (S : Finset V4) : Finset V4 :=
  S ∪ (S ×ˢ S).image (fun p => p.1 + p.2) ∪ S.image (fun x => swap4.mulVec x) ∪
    S.image (fun x => C.mulVec x)

@[expose] def closure4 (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : V4) : Finset V4 :=
  (stepS C)^[5] {0, v}

@[expose] def invSpanB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (S : Finset V4) (v : V4) : Bool :=
  decide (v ∈ S) && decide (S ≠ Finset.univ) && decide (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) &&
    decide (∀ x ∈ S, swap4.mulVec x ∈ S) && decide (∀ x ∈ S, C.mulVec x ∈ S)

@[expose] def relsB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Bool :=
  decide (C ^ 3 = 1) && decide ((swap4 * C) ^ 7 = 1) &&
    decide ((swap4 * C * swap4 * C * C) ^ 4 = 1)

@[expose] def redB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Bool :=
  decide (∃ v : V4, v ≠ 0 ∧ invSpanB C (closure4 C v) v = true)

theorem reducible_blk : ∀ X Y : Fin 2 → Fin 2 → ZMod 2, relsB (blk X Y) = true →
    redB (blk X Y) = true := by
  decide +kernel

end CFSG.Quasithin.L3Small
