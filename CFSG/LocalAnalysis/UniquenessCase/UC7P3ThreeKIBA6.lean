module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBSmall
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBWeights
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBU33
import CFSG.RankThree.PartOne.S15K.CommonEigen
import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofOneTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace ThreeKIB

open Module Module.End

private theorem pairs_three_inj {K : Type*} [Field K] (h11 : (-1 : K) ≠ 1) {d : K}
    (hd : d = 1 ∨ d = -1) :
    ∀ i j : Fin 3, ![-1, d, -d] i = ![-1, d, -d] j → ![d, -d, -1] i = ![d, -d, -1] j → i = j := by
  intro i j hi hj
  fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> grind

private theorem pairs_four_inj {K : Type*} [Field K] {u g : K} (hu : u ≠ u * u) (hu3 : u ^ 3 = 1)
    (hg3 : g ^ 3 = 1) :
    ∀ i j : Fin 4, ![u, g * g, u * u, g * g * (g * g)] i = ![u, g * g, u * u, g * g * (g * g)] j →
      ![g, u, g * g, u * u] i = ![g, u, g * g, u * u] j → i = j := by
  intro i j hi hj
  fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> grind

private theorem ne_one_of_cube {K : Type*} [Field K] {u g : K} (hu1 : u ≠ 1) (hg1 : g ≠ 1)
    (hu3 : u ^ 3 = 1) (hg3 : g ^ 3 = 1) : ∀ i, ![u, g * g, u * u, g * g * (g * g)] i ≠ 1 := by
  intro i; fin_cases i <;> simp <;> grind

private theorem ne_one_of_cube' {K : Type*} [Field K] {u : K} (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) :
    ∀ i, ![u, u, u * u, u * u] i ≠ 1 := by
  intro i; fin_cases i <;> simp <;> grind

private theorem isPGroup_four : IsPGroup 2 (Multiplicative (ZMod 2 × ZMod 2)) :=
  fun g => ⟨1, by revert g; decide⟩

private theorem sq_four : ∀ a : Multiplicative (ZMod 2 × ZMod 2), a ^ 2 = 1 := by decide

private theorem ne_one_four : Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2) ≠ 1 := by decide

theorem exists_fixed_of_four {L J : Type} [Group L] [Finite L] [Group J] [Finite J] {K W : Type*}
    [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (φ : J →* L) (hφ : Function.Surjective φ) (hcop : Nat.Coprime (Nat.card φ.ker) (2 * 3))
    (h2K : (2 : K) ≠ 0) (τ : J →* End K W) (hτ : ∀ x, τ x = 1 → φ x = 1)
    (f : Multiplicative (ZMod 2 × ZMod 2) →* L) (hf : Function.Injective f) {y : L}
    (hy3 : y ^ 3 = 1) (hyN : ∀ a, y * f a * y⁻¹ ∈ f.range)
    (hy₁ : y * f (.ofAdd (0, 1)) * y⁻¹ = f (.ofAdd (1, 0)))
    (hy₂ : y * f (.ofAdd (1, 1)) * y⁻¹ = f (.ofAdd (0, 1))) {ŷ : J} (hŷ3 : ŷ ^ 3 = 1)
    (hŷ : φ ŷ = y) : ∃ w : W, w ≠ 0 ∧ τ ŷ w = w := by
  have hk3 : ¬ 3 ∣ Nat.card φ.ker := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (Nat.Coprime.of_dvd_left (dvd_mul_left 3 2) hcop.symm)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f', ŷ₀, hf', hŷ₀, hN⟩ := exists_lift_hom φ hφ
    (Nat.Coprime.of_dvd_left (dvd_mul_right 2 3) hcop.symm) isPGroup_four f hyN
  obtain ⟨y₁, hy₁z, ⟨k, hk⟩, hφy₁⟩ := CFSG.RankThree.PartTwo.Sec13.Res7Proof.exists_three_part φ
    hy3 ŷ₀ hŷ₀
  have hy₁3 : y₁ ^ 3 = 1 := CFSG.RankThree.PartTwo.Sec13.Res7Proof.eq_one_of_three_pow
    (O := φ.ker) (r := k) (by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
    (by rw [MonoidHom.mem_ker, map_pow, hφy₁, hy3]) hk3
  have hy₁N : y₁ ∈ Subgroup.normalizer (f'.range : Set J) := Subgroup.zpowers_le.2 hN hy₁z
  set ρ := τ.comp f'
  have hr₁ : ∀ v, ρ (.ofAdd (1, 0)) (τ y₁ v) = τ y₁ (ρ (.ofAdd (0, 1)) v) :=
    apply_of_conj τ (conj_lift hf hf' hy₁N (by rw [hφy₁]; exact hy₁))
  have hr₂ : ∀ v, ρ (.ofAdd (0, 1)) (τ y₁ v) = τ y₁ (ρ (.ofAdd (1, 0)) (ρ (.ofAdd (0, 1)) v)) :=
    fun v => (apply_of_conj τ (conj_lift hf hf' hy₁N (by rw [hφy₁]; exact hy₂)) v).trans (by
      rw [show (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) = .ofAdd (1, 0) * .ofAdd (0, 1)
        from rfl, map_mul, map_mul, mul_apply]; rfl)
  have hsq : ∀ a, ρ a ^ 2 = 1 := fun a => by rw [← map_pow, sq_four, map_one]
  have hP₁1 : ρ (.ofAdd (1, 0)) ≠ 1 := fun h => ne_one_four (hf (((hf' _).symm.trans
    (hτ _ h)).trans (map_one f).symm))
  obtain ⟨v, hv0, c, d, hc1, hc2, hP₁v, hP₂v⟩ :=
    exists_jointEigen (n := 2) (by exact_mod_cast h2K) (hsq _) hP₁1 (R := ρ (.ofAdd (0, 1)))
      ((Commute.all _ _).map ρ)
  obtain rfl : c = -1 := (mul_self_eq_one_iff.1 (by rw [← pow_two, hc2])).resolve_left hc1
  have hd : d * d = 1 := by
    rw [← pow_two]; exact CFSG.RankThree.PartOne.S15K.eigenvalue_pow_eq_one (hsq _) hv0 hP₂v
  have hYv₁ : ρ (.ofAdd (1, 0)) (τ y₁ v) = d • τ y₁ v := by rw [hr₁, hP₂v, map_smul]
  have hYv₂ : ρ (.ofAdd (0, 1)) (τ y₁ v) = (-d) • τ y₁ v := by
    rw [hr₂, hP₂v, map_smul, hP₁v, smul_smul, map_smul, mul_neg_one]
  have hYYv₁ : ρ (.ofAdd (1, 0)) (τ y₁ (τ y₁ v)) = (-d) • τ y₁ (τ y₁ v) := by
    rw [hr₁, hYv₂, map_smul]
  have hYYv₂ : ρ (.ofAdd (0, 1)) (τ y₁ (τ y₁ v)) = (-1 : K) • τ y₁ (τ y₁ v) := by
    rw [hr₂, hYv₂, map_smul, hYv₁, smul_smul, map_smul, neg_mul, hd]
  have hli := linearIndependent_of_eigen₂ (ρ (.ofAdd (1, 0))) (ρ (.ofAdd (0, 1)))
    ![-1, d, -d] ![d, -d, -1]
    (pairs_three_inj (fun h => h2K (by linear_combination -h)) (mul_self_eq_one_iff.1 hd))
    ![v, τ y₁ v, τ y₁ (τ y₁ v)]
    (fun i => by
      fin_cases i
      exacts [hv0, apply_ne_zero τ _ hv0, apply_ne_zero τ _ (apply_ne_zero τ _ hv0)])
    (fun i => by fin_cases i; exacts [hP₁v, hYv₁, hYYv₁])
    (fun i => by fin_cases i; exacts [hP₂v, hYv₂, hYYv₂])
  have hw0 : v + τ y₁ v + τ y₁ (τ y₁ v) ≠ 0 := fun h => one_ne_zero <|
    Fintype.linearIndependent_iff.1 hli (fun _ => 1) (by
      simp only [Fin.sum_univ_three, one_smul]; exact h) 0
  have hYw : τ y₁ (v + τ y₁ v + τ y₁ (τ y₁ v)) = v + τ y₁ v + τ y₁ (τ y₁ v) := by
    have h3 : τ y₁ (τ y₁ (τ y₁ v)) = v := by
      rw [← mul_apply, ← mul_apply, ← map_mul, ← map_mul, ← pow_three', hy₁3, map_one, one_apply]
    rw [map_add, map_add, h3]
    abel
  obtain ⟨h, -, hconj⟩ := CFSG.RankThree.PartTwo.Sec13.Res7Proof.exists_conj_of_three φ
    (O := φ.ker) (fun x => MonoidHom.mem_ker.symm) hk3 hy₁3 hŷ3 (hφy₁.trans hŷ.symm)
  exact ⟨τ h _, apply_ne_zero τ h hw0, (apply_of_conj τ hconj _).trans (congrArg (τ h) hYw)⟩

private def a6α : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6γ : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [3, 4, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6t : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 3, 1, 4] * List.formPerm [2, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6e₁ : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6e₂ : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 2] * List.formPerm [1, 3], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6f₁ : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [1, 4] * List.formPerm [2, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6f₂ : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 3] * List.formPerm [1, 4], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private def pair {n : ℕ} (x y : alternatingGroup (Fin 6)) (m : Multiplicative (ZMod n × ZMod n)) :
    alternatingGroup (Fin 6) :=
  x ^ (Multiplicative.toAdd m).1.val * y ^ (Multiplicative.toAdd m).2.val

private def e9 : Multiplicative (ZMod 3 × ZMod 3) →* alternatingGroup (Fin 6) where
  toFun := pair a6α a6γ
  map_one' := by decide
  map_mul' := by decide

private def e4a : Multiplicative (ZMod 2 × ZMod 2) →* alternatingGroup (Fin 6) where
  toFun := pair a6e₁ a6e₂
  map_one' := by decide
  map_mul' := by decide

private def e4b : Multiplicative (ZMod 2 × ZMod 2) →* alternatingGroup (Fin 6) where
  toFun := pair a6f₁ a6f₂
  map_one' := by decide
  map_mul' := by decide

private theorem isPGroup_nine : IsPGroup 3 (Multiplicative (ZMod 3 × ZMod 3)) :=
  fun g => ⟨1, by revert g; decide⟩

private theorem cube_nine : ∀ a : Multiplicative (ZMod 3 × ZMod 3), a ^ 3 = 1 := by decide

private theorem e9_facts : (∀ a, a6t * e9 a * a6t⁻¹ ∈ e9.range) ∧ (∀ a, e9 a = 1 → a = 1) ∧
    a6t * e9 (.ofAdd (1, 0)) * a6t⁻¹ = e9 (.ofAdd (0, 1)) ∧
    a6t * e9 (.ofAdd (0, 2)) * a6t⁻¹ = e9 (.ofAdd (1, 0)) ∧
    e9 (.ofAdd (1, 0)) = a6α ∧ e9 (.ofAdd (1, 1)) = a6α * a6γ ∧
    Multiplicative.ofAdd ((1, 0) : ZMod 3 × ZMod 3) ≠ 1 := by decide

private theorem e4a_facts : a6α ^ 3 = 1 ∧ (∀ a, a6α * e4a a * a6α⁻¹ ∈ e4a.range) ∧
    a6α * e4a (.ofAdd (0, 1)) * a6α⁻¹ = e4a (.ofAdd (1, 0)) ∧
    a6α * e4a (.ofAdd (1, 1)) * a6α⁻¹ = e4a (.ofAdd (0, 1)) ∧ ∀ a, e4a a = 1 → a = 1 := by
  decide

private theorem e4b_facts : (a6α * a6γ) ^ 3 = 1 ∧
    (∀ a, a6α * a6γ * e4b a * (a6α * a6γ)⁻¹ ∈ e4b.range) ∧
    a6α * a6γ * e4b (.ofAdd (0, 1)) * (a6α * a6γ)⁻¹ = e4b (.ofAdd (1, 0)) ∧
    a6α * a6γ * e4b (.ofAdd (1, 1)) * (a6α * a6γ)⁻¹ = e4b (.ofAdd (0, 1)) ∧
    ∀ a, e4b a = 1 → a = 1 := by
  decide

theorem coverActsTriviallyOnSmall_alt6 :
    CoverActsTriviallyOnSmall 3 (alternatingGroup (Fin 6)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine coverActsTriviallyOnSmall_of_rep Nat.prime_three
    fun J _ _ φ hφ hcop K _ _ h2K h3K W _ _ _ hW τ hτ => ?_
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hN9, hinj9, hconj₁, hconj₂, hα, hαγ, hne⟩ := e9_facts
  obtain ⟨f', t₁, hf', ht₁, hN⟩ := exists_lift_hom φ hφ
    (Nat.Coprime.of_dvd_left (dvd_mul_left 3 2) hcop.symm) isPGroup_nine e9 hN9
  set ρ := τ.comp f'
  have he9 : Function.Injective e9 := (injective_iff_map_eq_one e9).2 hinj9
  have hcube : ∀ a, ρ a ^ 3 = 1 := fun a => by rw [← map_pow, cube_nine, map_one]
  have hA1 : ρ (.ofAdd (1, 0)) ≠ 1 := fun h => hne (he9 (((hf' _).symm.trans (hτ _ h)).trans
    (map_one e9).symm))
  have hAT : ∀ w, ρ (.ofAdd (1, 0)) (τ t₁ w) = τ t₁ (ρ (.ofAdd (0, 1)) (ρ (.ofAdd (0, 1)) w)) :=
    fun w => (apply_of_conj τ (conj_lift he9 hf' hN (a := .ofAdd (0, 2)) (b := .ofAdd (1, 0))
      (by rw [ht₁]; exact hconj₂)) w).trans (by
        rw [show (Multiplicative.ofAdd ((0, 2) : ZMod 3 × ZMod 3)) = .ofAdd (0, 1) * .ofAdd (0, 1)
          from rfl, map_mul, map_mul, mul_apply]; rfl)
  have hΓT : ∀ w, ρ (.ofAdd (0, 1)) (τ t₁ w) = τ t₁ (ρ (.ofAdd (1, 0)) w) :=
    apply_of_conj τ (conj_lift he9 hf' hN (a := .ofAdd (1, 0)) (b := .ofAdd (0, 1))
      (by rw [ht₁]; exact hconj₁))
  obtain ⟨v, hv0, u, g, hu1, hu3, hAv, hΓv⟩ := exists_jointEigen h3K (hcube _) hA1
    (R := ρ (.ofAdd (0, 1))) ((Commute.all _ _).map ρ)
  have hg3 : g ^ 3 = 1 := CFSG.RankThree.PartOne.S15K.eigenvalue_pow_eq_one (hcube _) hv0 hΓv
  have step : ∀ w a b, ρ (.ofAdd (1, 0)) w = a • w → ρ (.ofAdd (0, 1)) w = b • w →
      ρ (.ofAdd (1, 0)) (τ t₁ w) = (b * b) • τ t₁ w ∧ ρ (.ofAdd (0, 1)) (τ t₁ w) = a • τ t₁ w :=
    fun w a b ha hb => ⟨by rw [hAT, hb, map_smul, hb, smul_smul, map_smul],
      by rw [hΓT, ha, map_smul]⟩
  obtain ⟨h1A, h1Γ⟩ := step v u g hAv hΓv
  obtain ⟨h2A, h2Γ⟩ := step _ _ _ h1A h1Γ
  obtain ⟨h3A, h3Γ⟩ := step _ _ _ h2A h2Γ
  have hu0 : u ≠ 0 := by rintro rfl; norm_num at hu3
  have hu : u ≠ u * u := fun h => hu1 (mul_left_cancel₀ hu0 (h.symm.trans (mul_one u).symm))
  have hli := linearIndependent_of_eigen₂ (ρ (.ofAdd (1, 0))) (ρ (.ofAdd (0, 1)))
    ![u, g * g, u * u, g * g * (g * g)] ![g, u, g * g, u * u] (pairs_four_inj hu hu3 hg3)
    ![v, τ t₁ v, τ t₁ (τ t₁ v), τ t₁ (τ t₁ (τ t₁ v))]
    (fun i => by
      fin_cases i
      exacts [hv0, apply_ne_zero τ _ hv0, apply_ne_zero τ _ (apply_ne_zero τ _ hv0),
        apply_ne_zero τ _ (apply_ne_zero τ _ (apply_ne_zero τ _ hv0))])
    (fun i => by fin_cases i; exacts [hAv, h1A, h2A, h3A])
    (fun i => by fin_cases i; exacts [hΓv, h1Γ, h2Γ, h3Γ])
  have hdim : finrank K W ≤ Fintype.card (Fin 4) := by rw [Fintype.card_fin]; exact hW
  obtain ⟨h4a₁, h4a₂, h4a₃, h4a₄, h4a₅⟩ := e4a_facts
  obtain ⟨wA, hwA0, hwA⟩ := exists_fixed_of_four φ hφ hcop h2K τ hτ e4a
    ((injective_iff_map_eq_one e4a).2 h4a₅) h4a₁ h4a₂ h4a₃ h4a₄ (ŷ := f' (.ofAdd (1, 0)))
    (by rw [← map_pow, cube_nine, map_one]) (by rw [hf', hα])
  obtain ⟨h4b₁, h4b₂, h4b₃, h4b₄, h4b₅⟩ := e4b_facts
  obtain ⟨wB, hwB0, hwB⟩ := exists_fixed_of_four φ hφ hcop h2K τ hτ e4b
    ((injective_iff_map_eq_one e4b).2 h4b₅) h4b₁ h4b₂ h4b₃ h4b₄ (ŷ := f' (.ofAdd (1, 1)))
    (by rw [← map_pow, cube_nine, map_one]) (by rw [hf', hαγ])
  have hg1 : g = 1 := by
    by_contra hg1
    exact hwA0 (eq_zero_of_eigen_ne_one hli hdim
      (fun i => by fin_cases i; exacts [hAv, h1A, h2A, h3A]) (ne_one_of_cube hu1 hg1 hu3 hg3) hwA)
  subst hg1
  have hB : ∀ w, ρ (.ofAdd (1, 1)) w = ρ (.ofAdd (1, 0)) (ρ (.ofAdd (0, 1)) w) := fun w => by
    rw [show (Multiplicative.ofAdd ((1, 1) : ZMod 3 × ZMod 3)) = .ofAdd (1, 0) * .ofAdd (0, 1)
      from rfl, map_mul, mul_apply]
  have e0 : ρ (.ofAdd (1, 1)) v = u • v := by rw [hB, hΓv, one_smul, hAv]
  have e1 : ρ (.ofAdd (1, 1)) (τ t₁ v) = u • τ t₁ v := by
    rw [hB, h1Γ, map_smul, h1A, mul_one, one_smul]
  have e2 : ρ (.ofAdd (1, 1)) (τ t₁ (τ t₁ v)) = (u * u) • τ t₁ (τ t₁ v) := by
    rw [hB, h2Γ, mul_one, one_smul, h2A]
  have e3 : ρ (.ofAdd (1, 1)) (τ t₁ (τ t₁ (τ t₁ v))) = (u * u) • τ t₁ (τ t₁ (τ t₁ v)) := by
    rw [hB, h3Γ, map_smul, h3A]
    simp only [mul_one, one_smul]
  exact hwB0 (eq_zero_of_eigen_ne_one hli hdim (b := ![u, u, u * u, u * u])
    (fun i => by fin_cases i; exacts [e0, e1, e2, e3]) (ne_one_of_cube' hu1 hu3) hwB)

end ThreeKIB

theorem KIB3Small_holds : KIB3Small :=
  ⟨ThreeKIB.coverActsTriviallyOnSmall_alt6, fun _ hv hq3 hq1 =>
    ThreeKIB.coverActsTriviallyOnSmall_u33 hv hq3 hq1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
