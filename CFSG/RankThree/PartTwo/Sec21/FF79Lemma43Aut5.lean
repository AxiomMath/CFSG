module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43KFacts
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Aut5Fin
public import CFSG.RankThree.PartTwo.Sec21.FF79KAutL5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 CFSG.Quasithin.F7Two CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem is2El_pow_le {M : Type*} [Monoid M] {x : M} {m : ℕ} (h : x ^ (2 ^ m) = 1) (n : ℕ) :
    x ^ (2 ^ (m + n)) = 1 := by
  rw [pow_add, pow_mul, h, one_pow]

theorem eq_one_of_is2El_pow_three {M : Type*} [Group M] {x : M} (h2 : Is2El x)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := h2
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have h3' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hg : orderOf x ∣ Nat.gcd (2 ^ m) 3 := Nat.dvd_gcd h1 h3'
  have hc : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left _ (by norm_num)
  rw [hc] at hg
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)

theorem pow_four_of_is2El {M : Type*} [Group M] {x : M} (h60 : x ^ 60 = 1) (h2 : Is2El x) :
    x ^ 4 = 1 := by
  obtain ⟨m, hm⟩ := h2
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h60' : orderOf x ∣ 60 := orderOf_dvd_of_pow_eq_one h60
  rw [hj] at h60'
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hj]
  by_cases hj3 : 3 ≤ j
  · exfalso
    have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 hj3).trans h60'
    omega
  · push Not at hj3
    interval_cases j <;> norm_num

theorem is2El_conj_iff {M : Type*} [Group M] (g x : M) : Is2El (g * x * g⁻¹) ↔ Is2El x := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [conj_pow] at hm
    have : g * x ^ 2 ^ m * g⁻¹ = g * 1 * g⁻¹ := by rw [hm]; group
    simpa using this
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [conj_pow, hm]; group⟩

theorem center_G52 : Subgroup.center G52 = ⊥ := by
  haveI := isSimpleGroup_G52
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G52) with h | h
  · exact h
  · exact absurd (fun a b => (Subgroup.mem_center_iff.1
      (h ▸ Subgroup.mem_top b : b ∈ Subgroup.center G52)) a) not_commutative_G52

theorem conj_G52_inj {A B : G52} (h : MulAut.conj A = MulAut.conj B) : A = B := by
  have hz : B⁻¹ * A ∈ Subgroup.center G52 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : A * g * A⁻¹ = B * g * B⁻¹ := by
      have := congrArg (fun ψ : MulAut G52 => ψ g) h
      simpa [MulAut.conj_apply] using this
    calc g * (B⁻¹ * A) = B⁻¹ * (B * g * B⁻¹) * A := by group
      _ = B⁻¹ * (A * g * A⁻¹) * A := by rw [h1]
      _ = B⁻¹ * A * g := by group
  rw [center_G52, Subgroup.mem_bot] at hz
  exact (inv_mul_eq_one.1 hz).symm

theorem conj_G52_eq_one {A : G52} (h : MulAut.conj A = 1) : A = 1 :=
  conj_G52_inj (h.trans (map_one MulAut.conj).symm)

theorem aut_mul_conj {G : Type*} [Group G] (φ : MulAut G) (B : G) :
    φ * MulAut.conj B = MulAut.conj (φ B) * φ := by
  refine MulEquiv.ext fun g => ?_
  simp [MulAut.conj_apply]

theorem conj_aut_apply {G : Type*} [Group G] (φ : MulAut G) (B : G) :
    MulAut.conj (φ B) = φ * MulAut.conj B * φ⁻¹ := by
  rw [aut_mul_conj]; group

theorem dualG_mul_self : dualG * dualG = 1 := MulEquiv.ext fun g => gdual_gdual g

theorem aut_decomp (φ : MulAut G52) :
    ∃ A : G52, φ = MulAut.conj A ∨ φ = MulAut.conj A * dualG := by
  obtain ⟨A, σ, ε, hε, hψ⟩ :=
    (automorphism_generation (K := ZMod 2) (n := 5) (by norm_num)).2 (phiL5 φ)
  have hσ : σ = 1 := by
    ext x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl <;> simp
  subst hσ
  rw [map_one, mul_one] at hψ
  interval_cases ε
  · refine ⟨A, Or.inl (phiL5.injective ?_)⟩
    rw [phiL5_conj]
    simpa using hψ
  · refine ⟨A, Or.inr (phiL5.injective ?_)⟩
    rw [map_mul, phiL5_conj, phiL5_dualG, hψ, pow_one]

theorem exists_fixQ {y₁ y₂ : G52} (hy₁ : orderOf y₁ = 3) (hy₂ : orderOf y₂ = 3)
    (hc : y₁ * y₂ = y₂ * y₁) (hn : y₂ ∉ Subgroup.zpowers y₁) :
    ∃ Q : Subgroup G52, (∀ ψ : MulAut G52, ψ y₁ = y₁ → ψ y₂ = y₂ → ∀ g ∈ Q, ψ g = g) ∧
      (∀ A : G52, MulAut.conj A y₁ = y₁ → MulAut.conj A y₂ = y₂ → A ∈ Q) ∧
      (∀ A ∈ Q, A ^ 3 = 1) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_zpowers_sup hy₁ hy₂ hc hn
  obtain ⟨-, hel, hcent, -⟩ := syl3_structure Q
  refine ⟨(Q : Subgroup G52), ?_, ?_, ?_⟩
  · intro ψ h₁ h₂ g hg
    rw [hQ] at hg
    have hle : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ ≤
        MonoidHom.eqLocus ψ.toMonoidHom (MonoidHom.id G52) :=
      sup_le (Subgroup.zpowers_le.2 h₁) (Subgroup.zpowers_le.2 h₂)
    exact hle hg
  · intro A hA₁ hA₂
    have hA₁' : A * y₁ * A⁻¹ = y₁ := by simpa [MulAut.conj_apply] using hA₁
    have hA₂' : A * y₂ * A⁻¹ = y₂ := by simpa [MulAut.conj_apply] using hA₂
    have hAC : A ∈ Subgroup.centralizer (Q : Set G52) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ (Q : Subgroup G52) := hh
      rw [hQ] at hh'
      have hle : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ ≤ Subgroup.centralizer {A} := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc y₁ * A = A * y₁ * A⁻¹ * A := by rw [hA₁']
            _ = A * y₁ := by group
        · rw [Subgroup.mem_centralizer_singleton_iff]
          calc y₂ * A = A * y₂ * A⁻¹ * A := by rw [hA₂']
            _ = A * y₂ := by group
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh')
    rw [hcent] at hAC
    exact hAC
  · intro A hA
    exact elemPow_eq_one_of_isElementaryAbelian (A := (Q : Subgroup G52)) A hA

theorem aut_inv_fix {G : Type*} [Group G] {ψ : MulAut G} {x : G} (h : ψ x = x) : ψ⁻¹ x = x :=
  (ψ.symm_apply_eq).2 h.symm

theorem ff79KAut5Fix_holds : FF79KAut5Fix := by
  intro y₁ y₂ hy₁ hy₂ hc hn r r' hr₁ hr₂ hr'₁ hr'₂ hrE hr'E hr1 hr'1
  obtain ⟨Q, hQfix, hQmem, hQ3⟩ := exists_fixQ hy₁ hy₂ hc hn
  have hnot : ∀ (ψ : MulAut G52) (A : G52), ψ y₁ = y₁ → ψ y₂ = y₂ → ψ = MulAut.conj A →
      Is2El ψ → ψ = 1 := by
    intro ψ A h1 h2 hψ hE
    subst hψ
    have hA3 := hQ3 A (hQmem A h1 h2)
    apply eq_one_of_is2El_pow_three hE
    rw [← map_pow, hA3, map_one]
  obtain ⟨A, hA | hA⟩ := aut_decomp r
  · exact absurd (hnot r A hr₁ hr₂ hA hrE) hr1
  obtain ⟨A', hA' | hA'⟩ := aut_decomp r'
  · exact absurd (hnot r' A' hr'₁ hr'₂ hA' hr'E) hr'1
  have hs : r * r'⁻¹ = MulAut.conj (A * A'⁻¹) := by
    rw [hA, hA', mul_inv_rev, map_mul, map_inv]
    group
  have hsy₁ : MulAut.conj (A * A'⁻¹) y₁ = y₁ := by
    rw [← hs]; exact (congrArg r (aut_inv_fix hr'₁)).trans hr₁
  have hsy₂ : MulAut.conj (A * A'⁻¹) y₂ = y₂ := by
    rw [← hs]; exact (congrArg r (aut_inv_fix hr'₂)).trans hr₂
  have hBQ := hQmem _ hsy₁ hsy₂
  have hB3 := hQ3 _ hBQ
  have hcomm : MulAut.conj (A * A'⁻¹) * r' = r' * MulAut.conj (A * A'⁻¹) := by
    rw [aut_mul_conj, hQfix r' hr'₁ hr'₂ _ hBQ]
  have hr : r = MulAut.conj (A * A'⁻¹) * r' := by
    calc r = (r * r'⁻¹) * r' := by group
      _ = _ := by rw [hs]
  obtain ⟨m, hm⟩ := hrE
  obtain ⟨m', hm'⟩ := hr'E
  have e1 : r ^ 2 ^ (m + m') = 1 := is2El_pow_le hm m'
  have e2 : r' ^ 2 ^ (m + m') = 1 := by
    rw [add_comm]; exact is2El_pow_le hm' m
  rw [hr, Commute.mul_pow hcomm, e2, mul_one] at e1
  have h1 : MulAut.conj (A * A'⁻¹) = 1 := by
    apply eq_one_of_is2El_pow_three ⟨_, e1⟩
    rw [← map_pow, hB3, map_one]
  rw [hr, h1, one_mul]

theorem exists_dualFixed_of_commute (ρ : MulAut G52) (hcomm : ρ * dualG = dualG * ρ)
    (hE : Is2El ρ) (h1 : ρ ≠ 1) (h2 : ρ ≠ dualG) :
    ∃ A : G52, dualG A = A ∧ A ≠ 1 ∧ Is2El A ∧ ∀ c : G52, dualG c = c →
      MulAut.conj c * ρ * (MulAut.conj c)⁻¹ * ρ⁻¹ = MulAut.conj (c * A * c⁻¹ * A⁻¹) := by
  obtain ⟨A, hA | hA⟩ := aut_decomp ρ
  · rw [hA, aut_mul_conj] at hcomm
    have hdA : dualG A = A := conj_G52_inj (mul_right_cancel hcomm).symm
    refine ⟨A, hdA, fun h => h1 (by rw [hA, h, map_one]), ?_, fun c _ => ?_⟩
    · obtain ⟨m, hm⟩ := hE
      refine ⟨m, conj_G52_eq_one ?_⟩
      rw [map_pow, ← hA, hm]
    · rw [hA]; simp
  · have hcomm' : dualG * MulAut.conj A = MulAut.conj A * dualG := by
      have h3 : MulAut.conj A = MulAut.conj (dualG A) := by
        calc MulAut.conj A = MulAut.conj A * (dualG * dualG) := by rw [dualG_mul_self, mul_one]
          _ = (MulAut.conj A * dualG) * dualG := by rw [mul_assoc]
          _ = dualG * (MulAut.conj A * dualG) := by rw [hA] at hcomm; exact hcomm
          _ = (dualG * MulAut.conj A) * dualG := by rw [mul_assoc]
          _ = MulAut.conj (dualG A) * dualG * dualG := by rw [aut_mul_conj]
          _ = MulAut.conj (dualG A) := by rw [mul_assoc, dualG_mul_self, mul_one]
      rw [aut_mul_conj, ← h3]
    have hdA : dualG A = A := by
      rw [aut_mul_conj] at hcomm'
      exact conj_G52_inj (mul_right_cancel hcomm')
    refine ⟨A, hdA, fun h => h2 (by rw [hA, h, map_one, one_mul]), ?_, fun c hc => ?_⟩
    · obtain ⟨m, hm⟩ := hE
      refine ⟨m + 1, conj_G52_eq_one ?_⟩
      have hδ : dualG ^ (2 ^ (m + 1)) = 1 := by
        rw [pow_succ', pow_mul, pow_two, dualG_mul_self, one_pow]
      have hρ : ρ ^ (2 ^ (m + 1)) = 1 := by rw [pow_succ, pow_mul, hm, one_pow]
      have hCm : Commute (MulAut.conj A) dualG := hcomm'.symm
      rw [hA, hCm.mul_pow, hδ, mul_one] at hρ
      rw [map_pow]
      exact hρ
    · have hdc : dualG * (MulAut.conj c)⁻¹ = (MulAut.conj c)⁻¹ * dualG := by
        have : dualG * MulAut.conj c = MulAut.conj c * dualG := by
          rw [aut_mul_conj, hc]
        have hCm : Commute dualG (MulAut.conj c) := this
        exact hCm.inv_right.eq
      rw [hA]
      calc MulAut.conj c * (MulAut.conj A * dualG) * (MulAut.conj c)⁻¹ *
            (MulAut.conj A * dualG)⁻¹
          = MulAut.conj c * MulAut.conj A * (dualG * (MulAut.conj c)⁻¹) * dualG⁻¹ *
            (MulAut.conj A)⁻¹ := by group
        _ = MulAut.conj c * MulAut.conj A * ((MulAut.conj c)⁻¹ * dualG) * dualG⁻¹ *
            (MulAut.conj A)⁻¹ := by rw [hdc]
        _ = MulAut.conj (c * A * c⁻¹ * A⁻¹) := by simp only [map_mul, map_inv]; group

theorem ff79KO2L5_holds : FF79KO2L5 := by
  intro φ hφ2 hφ1 y₁ y₂ hy₁ hy₂ hc hn hφy₁ hφy₂ r hrφ hrE hr1 hrφ'
  obtain ⟨Q, hQfix, hQmem, hQ3⟩ := exists_fixQ hy₁ hy₂ hc hn
  rcases aut_involution_L5 φ hφ2 with ⟨A, hA⟩ | ⟨H, hH⟩
  · exfalso
    apply hφ1
    have hy₁' : MulAut.conj A y₁ = y₁ := by rw [← hA]; exact hφy₁
    have hy₂' : MulAut.conj A y₂ = y₂ := by rw [← hA]; exact hφy₂
    have hA3 : A ^ 3 = 1 := hQ3 A (hQmem A hy₁' hy₂')
    have h3 : φ ^ 3 = 1 := by rw [hA, ← map_pow, hA3, map_one]
    calc φ = φ ^ 3 * (φ * φ)⁻¹ := by group
      _ = 1 := by rw [h3, hφ2]; simp
  · set κ : MulAut G52 := MulAut.conj H with hκ
    obtain ⟨t, rfl⟩ : ∃ t : MulAut G52, r = κ * t * κ⁻¹ := ⟨κ⁻¹ * r * κ, by group⟩
    have htcomm : t * dualG = dualG * t := by
      rw [hH] at hrφ
      calc t * dualG = κ⁻¹ * ((κ * t * κ⁻¹) * (κ * dualG * κ⁻¹)) * κ := by group
        _ = κ⁻¹ * ((κ * dualG * κ⁻¹) * (κ * t * κ⁻¹)) * κ := by rw [hrφ]
        _ = dualG * t := by group
    have htE : Is2El t := (is2El_conj_iff κ t).1 hrE
    have ht1 : t ≠ 1 := fun h => hr1 (by rw [h]; group)
    have htδ : t ≠ dualG := fun h => hrφ' (by rw [h, hH])
    obtain ⟨B, hdB, hB1, hBE, hBc⟩ := exists_dualFixed_of_commute t htcomm htE ht1 htδ
    have h60 : ∀ g : G52, dualG g = g → g ^ 60 = 1 := fun g hg => dual_fixed_pow_sixty hg
    have hB4 : B ^ 4 = 1 := pow_four_of_is2El (h60 B hdB) hBE
    obtain ⟨c, hcd, hcne⟩ := dual_fixed_comm hdB hB4 hB1
    refine ⟨κ c, ?_, ?_⟩
    · rw [hH]
      show κ (dualG (κ.symm (κ c))) = κ c
      rw [MulEquiv.symm_apply_apply, hcd]
    · intro hE2
      have e : MulAut.conj (κ c) * (κ * t * κ⁻¹) * (MulAut.conj (κ c))⁻¹ * (κ * t * κ⁻¹)⁻¹ =
          κ * (MulAut.conj c * t * (MulAut.conj c)⁻¹ * t⁻¹) * κ⁻¹ := by
        rw [conj_aut_apply]; group
      rw [e, is2El_conj_iff, hBc c hcd] at hE2
      obtain ⟨m, hm⟩ := hE2
      have hm' : (c * B * c⁻¹ * B⁻¹) ^ 2 ^ m = 1 := conj_G52_eq_one (by rw [map_pow]; exact hm)
      have hdcom : dualG (c * B * c⁻¹ * B⁻¹) = c * B * c⁻¹ * B⁻¹ := by
        simp only [map_mul, map_inv, hcd, hdB]
      exact hcne (pow_four_of_is2El (h60 _ hdcom) ⟨m, hm'⟩)

end CFSG.RankThree.PartTwo.Sec21.FF79
