module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem eq_one_of_two_three {w : G} {k : ℕ} (h2 : w ^ 2 ^ k = 1) (h3 : w ^ 3 = 1) : w = 1 := by
  have hd1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have : orderOf w ∣ 1 := hcop ▸ Nat.dvd_gcd hd1 hd2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)

theorem closure_pair_le (h : FF84Sec4 b L B K b₁ b₂) : Subgroup.closure ({b, b₁} : Set G) ≤ B :=
  (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact mem_b h
    · rw [Set.mem_singleton_iff.1 hz]; exact mem_b₁ h)

theorem S45_E_cen_2sub (h : FF84Sec4 b L B K b₁ b₂)
    (hD : Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G)))
    (_hf : ControlsFusionIn B) {V : Subgroup G} (hV : IsPGroup 2 V) (hVD : V ≤ Cen (b * b₁))
    (hb : b ∈ Nor V) : V ≤ Cen b ⊓ Cen b₁ := by
  have hbE : b ∈ Subgroup.closure ({b, b₁} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ V, x * b = b * x := by
    intro x hx
    have hxN : x ∈ Nor (Subgroup.closure ({b, b₁} : Set G)) := hD (hVD hx)
    have h1 : x * b * x⁻¹ ∈ Subgroup.closure ({b, b₁} : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hxN b).1 hbE
    have hE : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.closure ({b, b₁} : Set G) :=
      mul_mem h1 (inv_mem hbE)
    have h2 : b * x⁻¹ * b⁻¹ ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 hb x⁻¹).1 (inv_mem hx)
      simpa using this
    have hV' : x * b * x⁻¹ * b⁻¹ ∈ V := by
      have := mul_mem hx h2
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hV ⟨_, hV'⟩
    have hw3 := pow3_of_mem h (closure_pair_le h hE)
    have h1' : x * b * x⁻¹ * b⁻¹ = 1 := eq_one_of_two_three (congrArg Subtype.val hk) hw3
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h1', one_mul]
  intro x hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx), ?_⟩
  have hxD : x * (b * b₁) = (b * b₁) * x := Subgroup.mem_centralizer_singleton_iff.1 (hVD hx)
  refine Subgroup.mem_centralizer_singleton_iff.2 ?_
  have hxb := hcomm x hx
  have : b * (x * b₁) = b * (b₁ * x) := by
    calc b * (x * b₁) = x * b * b₁ := by rw [← mul_assoc, ← hxb, mul_assoc]
      _ = x * (b * b₁) := by rw [mul_assoc]
      _ = (b * b₁) * x := hxD
      _ = b * (b₁ * x) := by rw [mul_assoc]
  exact mul_left_cancel this

theorem S45_D_normalizes (h41 : FF84_4_1) (h : FF84Sec4 b L B K b₁ b₂)
    (h44 : Opp 3 (Cen (b * b₁)) = ⊥) :
    Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G)) := by
  intro x hx
  have hmem : x ∈ setMul (Opp 3 (Cen (b * b₁)))
      (Cen (b * b₁) ⊓ Nor (Subgroup.closure ({b, b₁} : Set G))) := by
    rw [(h41 G b L B K b₁ b₂ h).1]; exact hx
  obtain ⟨u, hu, k, hk, rfl⟩ := hmem
  rw [h44, Subgroup.mem_bot] at hu
  rw [hu, one_mul]
  exact (Subgroup.mem_inf.1 hk).2

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
