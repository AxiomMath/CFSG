module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts5
public import CFSG.Quasithin.Vol2.Ch10SecKHBC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace EK1

variable {Y : Type} [Group Y] {X S : Subgroup Y}

theorem mem_normalizer_of_subgroupOf (hSX : S ≤ X) {d : ↥X}
    (hd : d ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (d : Y) ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hd ⊢
  intro y
  constructor
  · intro hy
    have h1 := (hd ⟨y, hSX hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro hy
    have hyX : y ∈ X := by
      have h1 : (d : Y)⁻¹ * ((d : Y) * y * (d : Y)⁻¹) * (d : Y) ∈ X :=
        X.mul_mem (X.mul_mem (X.inv_mem d.2) (hSX hy)) d.2
      simpa [mul_assoc] using h1
    have h1 := (hd ⟨y, hyX⟩).mpr (Subgroup.mem_subgroupOf.mpr hy)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1

theorem isSylowTwoOf_subgroupOf [Finite Y] (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  have h : ((S.subgroupOf X).subgroupOf ⊤).index = (S.subgroupOf X).index :=
    Subgroup.relIndex_top_right _
  rw [h]
  exact hS.2.2

theorem not_dvd_two_pow {m k : ℕ} (hm : 2 ≤ m) : ¬ 2 ^ m - 1 ∣ 2 ^ k := by
  intro h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hev : 2 ^ m % 2 = 0 := by
    rw [show m = (m - 1) + 1 by omega, pow_succ, Nat.mul_mod_left]
  rcases j with _ | j
  · rw [pow_zero] at hj
    omega
  · have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ, Nat.mul_mod_left]
    omega

end EK1

open EK1 in
theorem factBorelNotTwo_holds : FactBorelNotTwo := by
  intro Y _ _ X B m hm hX ⟨S, hS, hB⟩ h2
  subst hB
  have hY : E2.IsBenderOf m ↥X ∨ IsPSL 3 2 m ↥X ∨ IsPSp4 2 m ↥X := by
    rcases hX with h | h | h | h | h
    · exact Or.inl ⟨hm, Or.inl h⟩
    · exact Or.inl ⟨hm, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨hm, Or.inr (Or.inr h)⟩
    · exact Or.inr (Or.inl h)
    · unfold E2.IsSp4Prime at h
      simp only [show m ≠ 1 by omega, ↓reduceIte] at h
      exact Or.inr (Or.inr h)
  obtain ⟨d, hd, hdo⟩ :=
    Vol2.Ch10.SecB.factBorelCartan (↥X) m hm hY (S.subgroupOf X) (isSylowTwoOf_subgroupOf hS)
  have hdB : (d : Y) ∈ X ⊓ Subgroup.normalizer (S : Set Y) :=
    ⟨d.2, mem_normalizer_of_subgroupOf hS.1 hd⟩
  obtain ⟨k, hk⟩ := h2 ⟨d, hdB⟩
  have h1 : orderOf (⟨d, hdB⟩ : ↥(X ⊓ Subgroup.normalizer (S : Set Y))) = 2 ^ m - 1 := by
    rw [← Subgroup.orderOf_coe, ← hdo]
    exact Subgroup.orderOf_coe d
  exact not_dvd_two_pow hm (h1 ▸ orderOf_dvd_of_pow_eq_one hk)

end CFSG.Quasithin.Vol2.Ch11.SecE
