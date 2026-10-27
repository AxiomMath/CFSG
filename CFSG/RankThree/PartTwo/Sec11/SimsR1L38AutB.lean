module

import CFSG.RankThree.PartTwo.Sec11.SimsR1L38AutA
public import CFSG.RankThree.PartTwo.KFacts.K72L3Omega

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Aut

open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] [hF8 : Fact (Nat.card F = 8)]

theorem card_mod_three : Nat.card F % 3 = 2 := by rw [hF8.out]

theorem eq_one_of_pow_three_eq_one (c : F) (h : c ^ 3 = 1) : c = 1 := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at h
  have : Fintype F := Fintype.ofFinite F
  have h7 : c ^ 7 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc
    rwa [Fintype.card_eq_nat_card, hF8.out] at this
  calc c = c * (c ^ 3) ^ 2 := by rw [h]; ring
    _ = c ^ 7 := by ring
    _ = 1 := h7

theorem ringEquiv_pow_three (ψ : F ≃+* F) : ψ ^ 3 = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F) Nat.prime_two (by norm_num : 1 ≤ 3) (by rw [hF8.out]; norm_num)
  rw [← hcard]
  exact pow_card_eq_one'

end Field

section Involution

variable {F : Type} [Field F] [Finite F] [CharP F 2] [hF8 : Fact (Nat.card F = 8)]

open Matrix

theorem sl_eq_one_of_commute_involution {T X : SpecialLinearGroup (Fin 3) F}
    (hT : T * T = 1) (hT1 : T ≠ 1) (hX : X ^ 3 = 1) (hTX : T * X = X * T) : X = 1 := by
  have h1 : (T : Matrix (Fin 3) (Fin 3) F) * T = 1 := by
    simpa using
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hT
  have h2 : (X : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    simpa using
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hX
  have h3 : (T : Matrix (Fin 3) (Fin 3) F) * X = X * T := by
    simpa using
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hTX
  have hT1' : (T : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h => hT1 (Subtype.ext h)
  exact Subtype.ext (matrix_eq_one_of_commute_involution eq_one_of_pow_three_eq_one h1 hT1' h2 h3)

theorem proj_eq_one_of_commute_involution {t x : projectiveSL 3 F}
    (ht : t * t = 1) (ht1 : t ≠ 1) (hx : x ^ 3 = 1) (htx : t * x = x * t) : x = 1 := by
  have hinj := proj_three_injective (K := F) card_mod_three
  obtain ⟨T, rfl⟩ := proj_surjective 3 F t
  obtain ⟨X, rfl⟩ := proj_surjective 3 F x
  have h1 : T * T = 1 := hinj (by rw [map_mul, ht, map_one])
  have h2 : T ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have h3 : X ^ 3 = 1 := hinj (by rw [map_pow, hx, map_one])
  have h4 : T * X = X * T := hinj (by rw [map_mul, map_mul, htx])
  rw [sl_eq_one_of_commute_involution h1 h2 h3 h4, map_one]

theorem center_projectiveSL_eq_bot : Subgroup.center (projectiveSL 3 F) = ⊥ := by
  have hK := card_mod_three (F := F)
  let ι : SpecialLinearGroup (Fin 3) F ≃* projectiveSL 3 F :=
    MulEquiv.ofBijective (proj 3 F) ⟨proj_three_injective hK, proj_surjective 3 F⟩
  apply center_eq_bot_of_mulEquiv_of_center_eq_bot ι.symm
  rw [← scalars_eq_center]
  exact scalars_three_eq_bot_of_mod_three hK

theorem commute_of_conj_eq {G : Type*} [Group G] {a z : G} (h : a * z * a⁻¹ = z) :
    a * z = z * a :=
  calc a * z = a * z * a⁻¹ * a := (inv_mul_cancel_right _ _).symm
    _ = z * a := by rw [h]

theorem eq_one_of_pow_two_pow_of_commute {x : projectiveSL 3 F} (hx : orderOf x = 3) :
    ∀ (k : ℕ) (g : projectiveSL 3 F), g ^ 2 ^ k = 1 → Commute g x → g = 1 := by
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx] at this
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  intro k
  induction k with
  | zero => intro g hg _; simpa using hg
  | succ k ih =>
    intro g hg hc
    have hg2 : g ^ 2 = 1 := by
      apply ih (g ^ 2) _ (hc.pow_left 2)
      rw [← pow_mul, ← pow_succ']
      exact hg
    by_contra hne
    exact hx1 (proj_eq_one_of_commute_involution (by rw [← pow_two, hg2]) hne hx3 hc.eq)

theorem eq_one_of_mem_linearAutGroup {x : projectiveSL 3 F} (hx : orderOf x = 3)
    {τ : MulAut (projectiveSL 3 F)} (hτN : τ ∈ linearAutGroup 3 F) {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1) (hfix : τ x = x) : τ = 1 := by
  obtain ⟨g, rfl⟩ := isInnerAut_of_mem_linearAutGroup (card_mod_three (F := F)) hτN
  have hg : g ^ 2 ^ k = 1 := by
    have h1 : MulAut.conj (g ^ 2 ^ k) = 1 := by rw [map_pow]; exact hτ
    have hc : g ^ 2 ^ k ∈ Subgroup.center (projectiveSL 3 F) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (commute_of_conj_eq this).symm
    rw [center_projectiveSL_eq_bot] at hc
    exact Subgroup.mem_bot.mp hc
  have hcomm : Commute g x := by
    have h1 : g * x * g⁻¹ = x := hfix
    exact commute_of_conj_eq h1
  rw [eq_one_of_pow_two_pow_of_commute hx k g hg hcomm, map_one]

end Involution

section TwoElements

variable {F : Type} [Field F] [Finite F] [CharP F 2] [hF8 : Fact (Nat.card F = 8)]

theorem exists_conjAut_dualAut_pow {τ : MulAut (projectiveSL 3 F)} {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1) :
    ∃ (A : GL (Fin 3) F) (ε : ℕ), ε ≤ 1 ∧ τ = conjAut 3 F A * dualAut 3 F ^ ε := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, ψ, ε, hε, rfl⟩ := hform τ
  haveI : (linearAutGroup 3 F).Normal := (stdPinnedPSL_stable (n := 3) (K := F) le_rfl).normal
  let π := QuotientGroup.mk' (linearAutGroup 3 F)
  have hπA : π (conjAut 3 F A) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A)
  obtain ⟨a, ha⟩ : ∃ a, a = π (fieldAut 3 F ψ) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = π (dualAut 3 F) := ⟨_, rfl⟩
  have hcomm : Commute a d := by
    rw [ha, hd]
    exact (standardFieldGraph_commute (fieldAut_mem_standardFieldGraph ψ)
      dualAut_mem_standardFieldGraph).map π
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow, ← map_pow, ringEquiv_pow_three ψ, map_one, map_one]
  have hd2 : d ^ 2 = 1 := by
    rw [hd, ← map_pow, pow_two, (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1,
      map_one]
  have hb : π (conjAut 3 F A * fieldAut 3 F ψ * dualAut 3 F ^ ε) = a * d ^ ε := by
    rw [map_mul, map_mul, map_pow, hπA, one_mul, ← ha, ← hd]
  have hbk : (a * d ^ ε) ^ 2 ^ k = 1 := by
    rw [← hb, ← map_pow, hτ, map_one]
  have hdε : (d ^ ε) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hd2, one_pow]
  have hb2 : (a * d ^ ε) ^ 2 = a ^ 2 := by
    rw [(hcomm.pow_right ε).mul_pow, hdε, mul_one]
  have ha2 : (a ^ 2) ^ 2 ^ k = 1 := by
    rw [← hb2, ← pow_mul, mul_comm, pow_mul, hbk, one_pow]
  have ha2' : a ^ 2 = 1 := by
    have h3 : (a ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    have := pow_gcd_eq_one.mpr ⟨ha2, h3⟩
    rwa [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, pow_one] at this
  have ha1 : a = 1 := by
    have := pow_gcd_eq_one.mpr ⟨ha2', ha3⟩
    rwa [show Nat.gcd 2 3 = 1 by norm_num, pow_one] at this
  have hmem : fieldAut 3 F ψ ∈ linearAutGroup 3 F := by
    apply (QuotientGroup.eq_one_iff _).mp
    show π (fieldAut 3 F ψ) = 1
    rw [← ha]
    exact ha1
  rw [linearAutGroup_eq_range] at hmem
  obtain ⟨B, hB⟩ := hmem
  have hψ : ψ = 1 := by
    refine (eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl B⁻¹ ψ ?_).1
    rw [map_inv, hB, inv_mul_cancel]
  exact ⟨A, ε, hε, by rw [hψ, map_one, mul_one]⟩

theorem isCyclic_of_two_subgroup_fixing {x : projectiveSL 3 F} (hx : orderOf x = 3)
    (P : Subgroup (MulAut (projectiveSL 3 F))) (hP : IsPGroup 2 P)
    (hfix : ∀ τ ∈ P, τ x = x) : IsCyclic P := by
  have hpow : ∀ τ ∈ P, ∃ k, τ ^ 2 ^ k = 1 := by
    intro τ hτ
    obtain ⟨k, hk⟩ := hP ⟨τ, hτ⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hshape : ∀ τ ∈ P, τ ≠ 1 → ∃ A : GL (Fin 3) F, τ = conjAut 3 F A * dualAut 3 F := by
    intro τ hτ hne
    obtain ⟨k, hk⟩ := hpow τ hτ
    obtain ⟨A, ε, hε, hτe⟩ := exists_conjAut_dualAut_pow hk
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exfalso
      apply hne
      rw [pow_zero, mul_one] at hτe
      exact eq_one_of_mem_linearAutGroup hx (hτe ▸ conjAut_mem_linearAutGroup A) hk (hfix τ hτ)
    · exact ⟨A, by rw [hτe, pow_one]⟩
  have huniq : ∀ τ₁ ∈ P, ∀ τ₂ ∈ P, τ₁ ≠ 1 → τ₂ ≠ 1 → τ₁ = τ₂ := by
    intro τ₁ h₁ τ₂ h₂ n₁ n₂
    obtain ⟨A, hA⟩ := hshape τ₁ h₁ n₁
    obtain ⟨B, hB⟩ := hshape τ₂ h₂ n₂
    have hm : τ₁ * τ₂⁻¹ ∈ P := P.mul_mem h₁ (P.inv_mem h₂)
    obtain ⟨k, hk⟩ := hpow _ hm
    have hN : τ₁ * τ₂⁻¹ = conjAut 3 F (A * B⁻¹) := by
      rw [hA, hB, _root_.mul_inv_rev, map_mul, map_inv]
      group
    have := eq_one_of_mem_linearAutGroup hx (hN ▸ conjAut_mem_linearAutGroup _) hk (hfix _ hm)
    exact mul_inv_eq_one.mp this
  by_cases htriv : ∀ τ ∈ P, τ = 1
  · refine ⟨⟨1, fun y => ?_⟩⟩
    have hy : y = 1 := Subtype.ext (htriv y y.2)
    rw [hy]
    exact ⟨0, zpow_zero _⟩
  · obtain ⟨τ₀, hτ₀, hne⟩ : ∃ τ ∈ P, τ ≠ 1 := by
      by_contra h
      exact htriv fun τ hτ => by_contra fun hτ1 => h ⟨τ, hτ, hτ1⟩
    refine ⟨⟨⟨τ₀, hτ₀⟩, fun y => ?_⟩⟩
    by_cases hy : (y : MulAut (projectiveSL 3 F)) = 1
    · have hy' : y = 1 := Subtype.ext hy
      rw [hy']
      exact ⟨0, zpow_zero _⟩
    · have hy' : y = ⟨τ₀, hτ₀⟩ := Subtype.ext (huniq y y.2 τ₀ hτ₀ hy hne)
      rw [hy']
      exact ⟨1, zpow_one _⟩

end TwoElements

section Transvection

variable {F : Type} [Field F] [Finite F] [CharP F 2] [hF8 : Fact (Nat.card F = 8)]

open Matrix

@[expose] def tv (i j : Fin 3) (h : i ≠ j) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j h 1⟩

theorem tv_val (i j : Fin 3) (h : i ≠ j) :
    ((tv i j h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + Matrix.single i j 1 := rfl

theorem tv_mul_self (i j : Fin 3) (h : i ≠ j) :
    tv i j h * tv i j h = (1 : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  have := Matrix.transvection_mul_transvection_same i j h (1 : F) 1
  rw [one_add_one_eq_two, CharTwo.two_eq_zero, Matrix.transvection_zero] at this
  exact this

theorem fieldAut_proj_tv (ψ : F ≃+* F) (i j : Fin 3) (h : i ≠ j) :
    fieldAut 3 F ψ (proj 3 F (tv i j h)) = proj 3 F (tv i j h) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, tv_val]
  ext a b
  by_cases hab : a = b <;> by_cases hij : i = a ∧ j = b <;>
    simp [Matrix.one_apply, Matrix.single_apply, hab, hij]

theorem dualAut_proj_tv (i j : Fin 3) (h : i ≠ j) :
    dualAut 3 F (proj 3 F (tv i j h)) = proj 3 F (tv j i h.symm) := by
  rw [dualAut_proj, inv_eq_of_mul_eq_one_right (tv_mul_self i j h)]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_transpose, tv_val, tv_val]
  simp

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem mul_eq_mul_of_slConjugation_eq {A : GL (Fin 3) F} {g h : SpecialLinearGroup (Fin 3) F}
    (hAg : slConjugation 3 F A g = h) :
    (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F) * A := by
  have h1 := coe_slConjugation A g
  rw [hAg] at h1
  calc (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)
      = A * g * (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * A) := by
        rw [Units.inv_mul, mul_one]
    _ = (h : Matrix (Fin 3) (Fin 3) F) * A := by rw [← mul_assoc, ← h1]

theorem commute_single_of_fixes {A : GL (Fin 3) F} (i j : Fin 3) (h : i ≠ j)
    (hfix : conjAut 3 F A (proj 3 F (tv i j h)) = proj 3 F (tv i j h)) :
    Commute (Matrix.single i j (1 : F)) (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [conjAut_proj] at hfix
  have h1 := proj_three_injective (K := F) card_mod_three hfix
  have h2 := mul_eq_mul_of_slConjugation_eq h1
  rw [tv_val, mul_add, add_mul, mul_one, one_mul] at h2
  exact (add_left_cancel h2).symm

theorem rel_of_fixes_dual {A : GL (Fin 3) F} (i j : Fin 3) (h : i ≠ j)
    (hfix : conjAut 3 F A (dualAut 3 F (proj 3 F (tv i j h))) = proj 3 F (tv i j h)) :
    (A : Matrix (Fin 3) (Fin 3) F) * Matrix.single j i (1 : F) =
      Matrix.single i j (1 : F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [dualAut_proj_tv, conjAut_proj] at hfix
  have h1 := proj_three_injective (K := F) card_mod_three hfix
  have h2 := mul_eq_mul_of_slConjugation_eq h1
  rw [tv_val, tv_val, mul_add, add_mul, mul_one, one_mul] at h2
  exact add_left_cancel h2

theorem eq_one_of_fixes_transvections {τ : MulAut (projectiveSL 3 F)} {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1)
    (hfix : ∀ (i j : Fin 3) (h : i ≠ j), τ (proj 3 F (tv i j h)) = proj 3 F (tv i j h)) :
    τ = 1 := by
  obtain ⟨A, ε, hε, rfl⟩ := exists_conjAut_dualAut_pow hτ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hfix ⊢
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
      (fun i j h => commute_single_of_fixes i j h (hfix i j h))
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply Units.ne_zero A
      rw [← hc]
      simp
    have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hc]
    rw [hA, conjAut_scalar]
  · exfalso
    rw [pow_one] at hfix
    have r01 := rel_of_fixes_dual (A := A) 0 1 (by decide) (hfix 0 1 (by decide))
    have r12 := rel_of_fixes_dual (A := A) 1 2 (by decide) (hfix 1 2 (by decide))
    set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have h20 : M * Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : F) = 0 := by
      calc M * Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : F)
          = M * (Matrix.single (2 : Fin 3) (1 : Fin 3) (1 : F) *
              Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F)) := by
            rw [Matrix.single_mul_single_same, one_mul]
        _ = (M * Matrix.single (2 : Fin 3) (1 : Fin 3) (1 : F)) *
              Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F) := by rw [mul_assoc]
        _ = (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : F) * M) *
              Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F) := by rw [r12]
        _ = Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : F) *
              (M * Matrix.single (1 : Fin 3) (0 : Fin 3) (1 : F)) := by rw [mul_assoc]
        _ = Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : F) *
              (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : F) * M) := by rw [r01]
        _ = (Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : F) *
              Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : F)) * M := by rw [mul_assoc]
        _ = 0 := by
          rw [Matrix.single_mul_single_of_ne (1 : F) (1 : Fin 3) (2 : Fin 3) (0 : Fin 3)
            (by decide : (2 : Fin 3) ≠ 0) (1 : F), zero_mul]
    have h20' : (Matrix.single (2 : Fin 3) (0 : Fin 3) (1 : F) : Matrix (Fin 3) (Fin 3) F) = 0 := by
      have := congrArg (fun N => ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * N) h20
      simpa [← mul_assoc, hM] using this
    have h := congrFun (congrFun h20' 2) 0
    simp at h

end Transvection

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Aut
