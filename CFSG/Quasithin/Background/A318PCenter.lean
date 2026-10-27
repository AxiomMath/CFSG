module

public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.LinearAlgebra.LinearGroups.Elations
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem three_dvd_card_sub_one_of_center_statedSL {K : Type} [Field K] [Finite K]
    (h : Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3) : 3 ∣ Nat.card K - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 K)).toEquiv).trans h
  have hnt : Nontrivial (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
  obtain ⟨l, hl3, hzl⟩ := (CFSG.LinearGroups.mem_center_iff_exists_units).1 hz
  have hl1 : l ≠ 1 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hzl
  have hord : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  have hdvd := orderOf_dvd_natCard l
  rwa [hord, Nat.card_units] at hdvd

theorem three_dvd_add_one_of_center_statedSU {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ 1) ^ 2)
    (h : Nat.card (Subgroup.center ↥(StatedSU 3 (p ^ 1) K)) = 3) : 3 ∣ p + 1 := by
  have hcen := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 3) hK
    (by norm_num) (by simpa using hp2)).2
  rw [hcen] at h
  have hker := (CFSG.LinearGroups.unitary_scalar_kernel hp.out hK (n := 3) (by norm_num)).2.2
  rw [h] at hker
  have := Nat.gcd_dvd_right 3 (p ^ 1 + 1)
  rw [← hker] at this
  simpa using this

theorem a318CenterFact : A318CenterFact := by
  intro X _ _ hX hZ
  rcases hX with ⟨s, p, e, hp, he, hcase, hSL⟩ | h6 | h7 | hM
  · rcases hcase with ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩
    · exact Or.inl ⟨s, 2 ^ e, hmod, hSL⟩
    · have : Fact p.Prime := ⟨hp⟩
      refine Or.inl ⟨s, p ^ 1, ?_, hSL⟩
      cases s
      · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hSL
        have : Finite K := Nat.finite_of_card_ne_zero
          (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
        have h3 : Nat.card (Subgroup.center ↥(StatedSU 3 (p ^ 1) K)) = 3 :=
          (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm.trans hZ
        have hdvd := three_dvd_add_one_of_center_statedSU hp2 hK h3
        obtain ⟨c, hc⟩ := hdvd
        simp only [pow_one, Bool.false_eq_true, ↓reduceIte]
        unfold Int.ModEq
        omega
      · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hSL
        have : Finite K := Nat.finite_of_card_ne_zero
          (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
        have h3 : Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3 :=
          (Nat.card_congr (Subgroup.centerCongr φ).toEquiv).symm.trans hZ
        have hdvd := three_dvd_card_sub_one_of_center_statedSL h3
        rw [pow_one] at hK
        rw [hK] at hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hp1 : 1 ≤ p := hp.one_lt.le
        simp only [pow_one, ↓reduceIte]
        unfold Int.ModEq
        omega
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr (Or.inl h7))
  · exact Or.inr (Or.inr (Or.inr hM))

end CFSG.Quasithin
