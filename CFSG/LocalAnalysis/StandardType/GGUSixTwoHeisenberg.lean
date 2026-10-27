module

public import CFSG.Fischer.Classification.Basic.Heisenberg
public import CFSG.GroupTheory.FixedPointFreeOutsideCentral

public section

namespace CFSG.StandardType.USixTwo.Abs

open CFSG.Fischer.Classification
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

structure HeisSetup where
  a : Γ
  c : Γ
  f : Γ
  d : Γ
  hcr : CubeRel a c
  hfc : f * c * f⁻¹ = a
  hfa : f * a * f⁻¹ = c ^ 2
  hda : d * a * d⁻¹ = a
  hdc : d * c * d⁻¹ = a * c
  hfb : f * ⁅a, c⁆ * f⁻¹ = ⁅a, c⁆
  hdb : d * ⁅a, c⁆ * d⁻¹ = ⁅a, c⁆
  hbne : ⁅a, c⁆ ≠ 1

theorem isMulCommutative_of_isPGroup_three_card_le_nine {H : Type*} [Group H] [Finite H]
    (hp : IsPGroup 3 H) (hcard : Nat.card H ≤ 9) : ∀ x y : H, x * y = y * x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra h
    have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at hcard
    omega
  interval_cases k
  · haveI : Subsingleton H := Finite.card_le_one_iff_subsingleton.1 (by rw [hk]; norm_num)
    exact fun x y => Subsingleton.elim (x * y) (y * x)
  · have hcyc : IsCyclic H := isCyclic_of_prime_card (p := 3) (by rw [hk]; norm_num)
    letI : IsMulCommutative H := hcyc.isMulCommutative
    exact fun x y => (IsMulCommutative.is_comm (M := H)).comm x y
  · have h9 : Nat.card H = 9 := by rw [hk]; norm_num
    letI : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) h9
    exact fun x y => (IsMulCommutative.is_comm (M := H)).comm x y

namespace HeisSetup

variable (S : HeisSetup (Γ := Γ))

@[expose] def b : Γ := ⁅S.a, S.c⁆

theorem hb3 : S.b ^ 3 = 1 := by
  simpa [b] using S.hcr.commutator_pow_three

theorem hbne' : S.b ≠ 1 := by
  simpa [b] using S.hbne

theorem hfb' : S.f * S.b * S.f⁻¹ = S.b := by
  simpa [b] using S.hfb

theorem hdb' : S.d * S.b * S.d⁻¹ = S.b := by
  simpa [b] using S.hdb

@[expose] def R (g : Γ) : Prop := ∃ u : Γ, u * (S.a * S.b) * u⁻¹ = g

@[expose] def R' (x : Γ) : Prop := ∀ k : ℕ, S.R (x * S.b ^ k)

theorem R_conj {g w : Γ} (hg : S.R g) : S.R (w * g * w⁻¹) := by
  obtain ⟨u, hu⟩ := hg
  exact ⟨w * u, by rw [← hu]; group⟩

theorem R'_of_mod {x : Γ} (h : ∀ k < 3, S.R (x * S.b ^ k)) : S.R' x := by
  intro k
  conv_rhs => rw [← Nat.div_add_mod k 3]
  rw [pow_add, pow_mul, S.hb3, one_pow, one_mul]
  exact h (k % 3) (Nat.mod_lt _ (by norm_num))

theorem R'_conj {x w : Γ} (hx : S.R' x) (hw : w * S.b * w⁻¹ = S.b) :
    S.R' (w * x * w⁻¹) := by
  intro k
  have hk : w * S.b ^ k * w⁻¹ = S.b ^ k := by
    rw [← conj_pow, hw]
  have hthis : S.R (w * (x * S.b ^ k) * w⁻¹) := S.R_conj (w := w) (hx k)
  have hrew : w * (x * S.b ^ k) * w⁻¹ = (w * x * w⁻¹) * S.b ^ k := by
    calc w * (x * S.b ^ k) * w⁻¹
        = (w * x * w⁻¹) * (w * S.b ^ k * w⁻¹) := by group
      _ = (w * x * w⁻¹) * S.b ^ k := by rw [hk]
  rwa [hrew] at hthis

theorem R'_mul_b {x : Γ} (hx : S.R' x) (m : ℕ) : S.R' (x * S.b ^ m) := by
  intro k
  have hk : x * S.b ^ m * S.b ^ k = x * S.b ^ (m + k) := by rw [pow_add]; group
  rw [hk]
  exact hx (m + k)

theorem commutator_a_c : ⁅S.a, S.c⁆ = S.b := rfl

theorem hb_comm_c_inv : S.b * S.c⁻¹ = S.c⁻¹ * S.b :=
  S.hcr.commute_commutator_right.inv_right.eq

theorem hb_inv_comm_c : S.b⁻¹ * S.c = S.c * S.b⁻¹ :=
  S.hcr.commute_commutator_right.inv_left.eq

theorem hb_inv_comm_c_inv : S.b⁻¹ * S.c⁻¹ = S.c⁻¹ * S.b⁻¹ :=
  S.hcr.commute_commutator_right.inv_left.inv_right.eq

theorem hb_inv_eq_b_sq : S.b⁻¹ = S.b ^ 2 := by
  have h : S.b * S.b ^ 2 = 1 := by
    rw [show S.b * S.b ^ 2 = S.b ^ (1 + 2) by rw [pow_add, pow_one]]
    norm_num
    exact S.hb3
  exact inv_eq_of_mul_eq_one_right h

theorem c_conj_a : S.c * S.a * S.c⁻¹ = S.a * S.b⁻¹ := by
  calc S.c * S.a * S.c⁻¹ = (S.a * S.c * S.b⁻¹) * S.c⁻¹ := by
        rw [S.hcr.mul_comm_eq, S.commutator_a_c]
    _ = S.a * S.c * (S.b⁻¹ * S.c⁻¹) := by group
    _ = S.a * S.c * (S.c⁻¹ * S.b⁻¹) := by rw [S.hb_inv_comm_c_inv]
    _ = S.a * S.b⁻¹ := by group

theorem c_conj_ab : S.c * (S.a * S.b) * S.c⁻¹ = S.a := by
  calc S.c * (S.a * S.b) * S.c⁻¹ = S.c * S.a * (S.b * S.c⁻¹) := by group
    _ = S.c * S.a * (S.c⁻¹ * S.b) := by rw [S.hb_comm_c_inv]
    _ = (S.c * S.a * S.c⁻¹) * S.b := by group
    _ = (S.a * S.b⁻¹) * S.b := by rw [S.c_conj_a]
    _ = S.a := by group

theorem c_conj_a_b2 : S.c * S.a * S.c⁻¹ = S.a * S.b ^ 2 := by
  rw [S.c_conj_a, S.hb_inv_eq_b_sq]

theorem f_conj_c2 : S.f * S.c ^ 2 * S.f⁻¹ = S.a ^ 2 := by
  calc S.f * S.c ^ 2 * S.f⁻¹ = (S.f * S.c * S.f⁻¹) ^ 2 := by rw [← conj_pow]
    _ = S.a ^ 2 := by rw [S.hfc]

theorem f_conj_a2 : S.f * S.a ^ 2 * S.f⁻¹ = S.c := by
  calc S.f * S.a ^ 2 * S.f⁻¹ = (S.f * S.a * S.f⁻¹) ^ 2 := by rw [← conj_pow]
    _ = (S.c ^ 2) ^ 2 := by rw [S.hfa]
    _ = S.c ^ (2 * 2) := by rw [pow_mul]
    _ = S.c ^ 4 := by norm_num
    _ = S.c ^ 3 * S.c := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, pow_one]
    _ = S.c := by rw [S.hcr.cube_right, one_mul]

theorem d_conj_a2 : S.d * S.a ^ 2 * S.d⁻¹ = S.a ^ 2 := by
  calc S.d * S.a ^ 2 * S.d⁻¹ = (S.d * S.a * S.d⁻¹) ^ 2 := by rw [← conj_pow]
    _ = S.a ^ 2 := by rw [S.hda]

theorem ac_sq : (S.a * S.c) ^ 2 = S.a ^ 2 * S.c ^ 2 * S.b⁻¹ := by
  have hca : S.c * S.a = S.a * S.c * S.b⁻¹ := S.hcr.mul_comm_eq
  calc (S.a * S.c) ^ 2 = (S.a * S.c) * (S.a * S.c) := by rw [pow_two]
    _ = S.a * S.c * S.a * S.c := by simp only [mul_assoc]
    _ = S.a * (S.c * S.a) * S.c := by group
    _ = S.a * (S.a * S.c * S.b⁻¹) * S.c := by rw [hca]
    _ = S.a * S.a * S.c * (S.b⁻¹ * S.c) := by group
    _ = S.a * S.a * S.c * (S.c * S.b⁻¹) := by rw [S.hb_inv_comm_c]
    _ = S.a ^ 2 * S.c ^ 2 * S.b⁻¹ := by rw [pow_two, pow_two]; group

theorem d_conj_ac : S.d * (S.a * S.c) * S.d⁻¹ = S.a ^ 2 * S.c := by
  calc S.d * (S.a * S.c) * S.d⁻¹
      = (S.d * S.a * S.d⁻¹) * (S.d * S.c * S.d⁻¹) := by group
    _ = S.a * (S.a * S.c) := by simp only [S.hda, S.hdc, pow_one]
    _ = S.a ^ 2 * S.c := by rw [pow_two]; group

theorem d_conj_c2 : S.d * S.c ^ 2 * S.d⁻¹ = (S.a * S.c) ^ 2 := by
  calc S.d * S.c ^ 2 * S.d⁻¹ = (S.d * S.c * S.d⁻¹) ^ 2 := by rw [← conj_pow]
    _ = (S.a * S.c) ^ 2 := by rw [S.hdc]

theorem a_pow_four : S.a ^ 4 = S.a := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, S.hcr.cube_left, one_mul, pow_one]

theorem d_conj_a2c2 : S.d * (S.a ^ 2 * S.c ^ 2) * S.d⁻¹ = S.a * S.c ^ 2 * S.b⁻¹ := by
  calc S.d * (S.a ^ 2 * S.c ^ 2) * S.d⁻¹
      = (S.d * S.a ^ 2 * S.d⁻¹) * (S.d * S.c ^ 2 * S.d⁻¹) := by group
    _ = (S.a ^ 2) * ((S.a * S.c) ^ 2) := by rw [S.d_conj_a2, S.d_conj_c2]
    _ = S.a * S.c ^ 2 * S.b⁻¹ := by
        rw [S.ac_sq]
        have h4 : S.a ^ 2 * S.a ^ 2 = S.a ^ 4 := by rw [← pow_add]
        rw [show S.a ^ 2 * (S.a ^ 2 * S.c ^ 2 * S.b⁻¹) =
          (S.a ^ 2 * S.a ^ 2) * S.c ^ 2 * S.b⁻¹ by group]
        rw [h4, S.a_pow_four]

theorem R_ab : S.R (S.a * S.b) := ⟨1, by group⟩

theorem R_a : S.R S.a := by
  have h := S.R_conj (w := S.c) S.R_ab
  simpa [S.c_conj_ab] using h

theorem R_a_b2 : S.R (S.a * S.b ^ 2) := by
  have h := S.R_conj (w := S.c) S.R_a
  simpa [S.c_conj_a_b2] using h

theorem R'_a : S.R' S.a := by
  apply S.R'_of_mod
  intro k hk
  interval_cases k
  · simpa using S.R_a
  · simpa using S.R_ab
  · simpa using S.R_a_b2

theorem R'_c2 : S.R' (S.c ^ 2) := by
  have h := S.R'_conj (w := S.f) S.R'_a S.hfb'
  simpa [S.hfa] using h

theorem R'_a2 : S.R' (S.a ^ 2) := by
  have h := S.R'_conj (w := S.f) S.R'_c2 S.hfb'
  simpa [S.f_conj_c2] using h

theorem R'_c : S.R' S.c := by
  have h := S.R'_conj (w := S.f) S.R'_a2 S.hfb'
  simpa [S.f_conj_a2] using h

theorem R'_ac : S.R' (S.a * S.c) := by
  have h := S.R'_conj (w := S.d) S.R'_c S.hdb'
  simpa [S.hdc] using h

theorem R'_a2c : S.R' (S.a ^ 2 * S.c) := by
  have h := S.R'_conj (w := S.d) S.R'_ac S.hdb'
  simpa [S.d_conj_ac] using h

theorem R'_a2c2 : S.R' (S.a ^ 2 * S.c ^ 2) := by
  have h := S.R'_conj (w := S.d) S.R'_c2 S.hdb'
  have h' : S.R' ((S.a * S.c) ^ 2) := by simpa [S.d_conj_c2] using h
  rw [S.ac_sq, S.hb_inv_eq_b_sq] at h'
  have h2 := S.R'_mul_b h' 1
  have hb : S.b ^ 2 * S.b = 1 := by
    simpa [pow_succ] using S.hb3
  rw [mul_assoc] at h2
  simpa [hb] using h2

theorem R'_ac2 : S.R' (S.a * S.c ^ 2) := by
  have h := S.R'_conj (w := S.d) S.R'_a2c2 S.hdb'
  have h' : S.R' (S.a * S.c ^ 2 * S.b⁻¹) := by simpa [S.d_conj_a2c2] using h
  rw [S.hb_inv_eq_b_sq] at h'
  have h2 := S.R'_mul_b h' 1
  have hb : S.b ^ 2 * S.b = 1 := by
    simpa [pow_succ] using S.hb3
  rw [mul_assoc] at h2
  simpa [hb] using h2

theorem mem_closure_conj {g : Γ} (hg : g ∈ Subgroup.closure ({S.a, S.c} : Set Γ))
    (hgz : g ∉ Subgroup.zpowers S.b) : S.R g := by
  obtain ⟨i, j, k, hi, hj, hk, hg_eq⟩ := S.hcr.exists_eq_of_mem_closure hg
  rw [hg_eq]
  simp only [S.commutator_a_c]
  interval_cases i <;> interval_cases j
  · exfalso
    apply hgz
    rw [hg_eq]
    simp only [S.commutator_a_c]
    simpa using (Subgroup.npow_mem_zpowers S.b k)
  · simpa using S.R'_c k
  · simpa using S.R'_c2 k
  · simpa using S.R'_a k
  · simpa using S.R'_ac k
  · simpa using S.R'_ac2 k
  · simpa using S.R'_a2 k
  · simpa using S.R'_a2c k
  · simpa using S.R'_a2c2 k

theorem card_closure [Finite Γ] :
    Nat.card (Subgroup.closure ({S.a, S.c} : Set Γ)) = 27 := by
  classical
  let H : Subgroup Γ := Subgroup.closure ({S.a, S.c} : Set Γ)
  change Nat.card H = 27
  have hle : Nat.card H ≤ 27 := by
    let f : Fin 3 × Fin 3 × Fin 3 → H := fun p =>
      ⟨S.a ^ (p.1 : ℕ) * S.c ^ (p.2.1 : ℕ) * S.b ^ (p.2.2 : ℕ), by
        refine H.mul_mem (H.mul_mem (H.pow_mem ?_ _) (H.pow_mem ?_ _)) (H.pow_mem ?_ _)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.commutator_le_self H
            (Subgroup.commutator_mem_commutator
              (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))⟩
    have hsurj : Function.Surjective f := by
      intro g
      obtain ⟨i, j, k, hi, hj, hk, hg⟩ := S.hcr.exists_eq_of_mem_closure g.2
      refine ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), ?_⟩
      apply Subtype.ext
      simp only [S.commutator_a_c] at hg ⊢
      exact hg.symm
    haveI : Fintype H := Fintype.ofFinite H
    have hle := Fintype.card_le_of_surjective f hsurj
    change Nat.card H ≤ 27
    simpa [Nat.card_eq_fintype_card] using hle
  have hnonab : ¬ ∀ x y : H, x * y = y * x := by
    intro hcomm
    have hac : S.a * S.c = S.c * S.a := by
      have h := hcomm ⟨S.a, Subgroup.subset_closure (by simp)⟩
        ⟨S.c, Subgroup.subset_closure (by simp)⟩
      exact congrArg Subtype.val h
    have hb1 : S.b = 1 := by
      have h := S.hcr.mul_comm_eq
      rw [hac] at h
      have h1 : S.b⁻¹ = 1 := by
        apply mul_left_cancel (a := S.c * S.a)
        calc (S.c * S.a) * S.b⁻¹ = S.c * S.a := h.symm
          _ = (S.c * S.a) * 1 := by rw [mul_one]
      simpa using congrArg Inv.inv h1
    exact S.hbne' hb1
  haveI : Finite H := Subtype.finite
  have hexp : ∀ g : H, g ^ 3 = 1 := by
    intro g
    exact Subtype.ext (S.hcr.pow_three_eq_one g.2)
  have hExp : Monoid.exponent H ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (by intro g; exact hexp g)
  have hp : IsPGroup 3 H := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hExp)
  have hge : 27 ≤ Nat.card H := by
    by_contra hlt
    have h9 : Nat.card H ≤ 9 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [hk] at hlt ⊢
      have hk3 : k < 3 := by
        by_contra h
        have h3 : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> norm_num
    exact hnonab (isMulCommutative_of_isPGroup_three_card_le_nine hp h9)
  omega

end HeisSetup

end CFSG.StandardType.USixTwo.Abs

end
