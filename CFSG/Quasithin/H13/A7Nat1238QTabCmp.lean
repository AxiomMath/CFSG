module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSource
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

@[expose] def List1222 (X : Type) [Group X] : Prop :=
  (Nat.card X = 168 ∨ Nat.card X = 6048 ∨ Nat.card X = 9999360) ∨
    ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ ∃ φ : X →* alternatingGroup (Fin n), Function.Surjective φ ∧
      φ.ker ≤ center X

section Orders

theorem card_alternating_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem odd_card_ker_of_le_center {X Y : Type} [Group X] [Group Y] [Finite X]
    (hZ : Odd (Nat.card (center X))) {φ : X →* Y} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ center X) :
    Odd (Nat.card φ.ker) ∧ Nat.card φ.ker * Nat.card Y = Nat.card X :=
  ⟨Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hker),
    Subgroup.card_ker_mul_card_of_surjective hφ⟩

theorem not_list1222_of_card {X : Type} [Group X] [Finite X] (hZ : Odd (Nat.card (center X)))
    {v : ℕ} (hX : Nat.card X = v) (h1 : v ≠ 168 ∧ v ≠ 6048 ∧ v ≠ 9999360)
    (h2 : ∀ n k : ℕ, 5 ≤ n → n ≤ 8 → Odd k → v ≠ n.factorial / 2 * k) : ¬ List1222 X := by
  rintro (h | ⟨n, hn5, hn8, φ, hφ, hker⟩)
  · rcases h with h | h | h <;> omega
  · obtain ⟨hodd, hc⟩ := odd_card_ker_of_le_center hZ hφ hker
    rw [card_alternating_fin n (by omega)] at hc
    exact h2 n _ hn5 hn8 hodd (by rw [← hX, ← hc, mul_comm])

theorem forall_ne_alt_mul_odd {v : ℕ}
    (h : ∀ k : ℕ, Odd k → v ≠ 60 * k ∧ v ≠ 360 * k ∧ v ≠ 2520 * k ∧ v ≠ 20160 * k) :
    ∀ n k : ℕ, 5 ≤ n → n ≤ 8 → Odd k → v ≠ n.factorial / 2 * k := by
  intro n k hn5 hn8 hk
  obtain ⟨h5, h6, h7, h8⟩ := h k hk
  interval_cases n
  · simpa [Nat.factorial] using h5
  · simpa [Nat.factorial] using h6
  · simpa [Nat.factorial] using h7
  · simpa [Nat.factorial] using h8

theorem eq_eight_of_mul_factorial {n k v : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8) (hk : Odd k)
    (h : k * (n.factorial / 2) = v) (hv : v = 20160 ∨ v = 60480) : n = 8 ∧ k * 20160 = v := by
  obtain ⟨j, rfl⟩ := hk
  interval_cases n <;> norm_num [Nat.factorial] at h <;> omega

theorem not_list1222_of_card' {X : Type} [Group X] [Finite X] (hZ : Odd (Nat.card (center X)))
    {v : ℕ} (hX : Nat.card X = v) (h1 : v ≠ 168 ∧ v ≠ 6048 ∧ v ≠ 9999360)
    (h2 : ∀ k : ℕ, Odd k → v ≠ 60 * k ∧ v ≠ 360 * k ∧ v ≠ 2520 * k ∧ v ≠ 20160 * k) :
    ¬ List1222 X :=
  not_list1222_of_card hZ hX h1 (forall_ne_alt_mul_odd h2)

end Orders

section Linear

variable {X : Type} [Group X] [Finite X]

theorem not_list1222_of_psl_three_four
    (hZ : Odd (Nat.card (center X))) (hX : IsPSL 3 2 2 X) : ¬ List1222 X := by
  obtain ⟨hc, -, hA⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X hX
  rintro (h | ⟨n, hn5, hn8, φ, hφ, hker⟩)
  · rcases h with h | h | h <;> omega
  · obtain ⟨hodd, hc2⟩ := odd_card_ker_of_le_center hZ hφ hker
    rw [card_alternating_fin n (by omega), hc] at hc2
    obtain ⟨rfl, hk8⟩ := eq_eight_of_mul_factorial hn5 hn8 hodd hc2 (Or.inl rfl)
    have hk : Nat.card φ.ker = 1 := by omega
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
      exact hk
    exact (hA (Fin 8) (by simp)).false (MulEquiv.ofBijective φ ⟨hinj, hφ⟩)

theorem statedScalars_subgroupOf_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) :
    (Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H ≤ center ↥H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, Assembly.LowTwoRank.StatedScalars,
    ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact (Subgroup.mem_center_iff.1 hx (y : GL ι K))

theorem not_list1222_of_sl_three_four
    (hZ : Odd (Nat.card (center X))) (hX : IsSL3 4 X) : ¬ List1222 X := by
  classical
  obtain ⟨F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  set S := Assembly.LowTwoRank.StatedSL 3 F with hSdef
  set N := (Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf S with hN
  have hcS : Nat.card ↥S = 60480 := by
    rw [hSdef, ← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFc]
    decide
  have hcX : Nat.card X = 60480 := by rw [Nat.card_congr e.toEquiv, hcS]
  have hP : IsPSL 3 2 2 (Assembly.LowTwoRank.StatedProj S) :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, F, hF, hFfin,
      by rw [hFc]; norm_num, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hPc, -, hPA⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated _ hP
  set ψ : X →* Assembly.LowTwoRank.StatedProj S := (QuotientGroup.mk' N).comp e.toMonoidHom
    with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective N).comp e.surjective
  have hψk : ψ.ker ≤ center X := by
    intro x hx
    have hx' : e x ∈ N := (QuotientGroup.eq_one_iff _).1 hx
    have hc := statedScalars_subgroupOf_le_center S hx'
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact hc (e y)
  have hcψ : Nat.card ψ.ker = 3 := by
    have := Subgroup.card_ker_mul_card_of_surjective hψs
    rw [hcX, hPc] at this
    omega
  rintro (h | ⟨n, hn5, hn8, φ, hφ, hker⟩)
  · rcases h with h | h | h <;> omega
  · obtain ⟨hodd, hc2⟩ := odd_card_ker_of_le_center hZ hφ hker
    rw [card_alternating_fin n (by omega), hcX] at hc2
    obtain ⟨rfl, hk8⟩ := eq_eight_of_mul_factorial hn5 hn8 hodd hc2 (Or.inr rfl)
    ·
      have hZk : center X ≤ φ.ker := by
        intro z hz
        rw [MonoidHom.mem_ker]
        have hc : φ z ∈ center (alternatingGroup (Fin 8)) := by
          rw [Subgroup.mem_center_iff]
          intro y
          obtain ⟨x, rfl⟩ := hφ y
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x)]
        rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
        exact hc
      have heq : ψ.ker = φ.ker :=
        Subgroup.eq_of_le_of_card_ge (hψk.trans hZk) (by omega)
      exact (hPA (Fin 8) (by simp)).false
        ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq heq).trans
            (QuotientGroup.quotientKerEquivOfSurjective φ hφ)))

omit [Finite X] in
theorem not_list1222_of_psl_two_prime {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (hX : IsPSL 2 p 1 X) : ¬ List1222 X := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 2 p 1 hX).2
  have hpX : p ∣ Nat.card X := by
    obtain ⟨-, F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
    have hodd : Odd (Nat.card F) := by
      rw [hFc, pow_one]
      exact hp.odd_of_ne_two (by omega)
    have hc := CFSG.ComponentClassification.UnbalancingLocal.two_mul_card_psl_two_of_odd F hodd
    rw [← Nat.card_congr e.toEquiv, hFc, pow_one] at hc
    have h1 : p ∣ Nat.card X * 2 := ⟨p ^ 2 - 1, hc⟩
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hp_ne : ∀ q : ℕ, q.Prime → q ∣ 2 ∨ q ∣ 3 ∨ q ∣ 5 ∨ q ∣ 7 ∨ q ∣ 31 → q ≤ 31 := by
    intro q hq h
    rcases h with h | h | h | h | h <;> exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
  rintro (h | ⟨n, hn5, hn8, φ, hφ, hker⟩)
  ·
    have key : ∀ v : ℕ, v = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 31 → p ∣ v → p = 31 := by
      intro v hv hpv
      rw [hv] at hpv
      rcases (Nat.Prime.dvd_mul hp).1 hpv with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
              omega
            · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
              omega
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h
            omega
        · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : (7 : ℕ).Prime)).1 h
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : (31 : ℕ).Prime)).1 h
    have hdvd : p ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 * 31 := by
      rcases h with h | h | h <;> rw [h] at hpX
      · exact hpX.trans (by norm_num)
      · exact hpX.trans (by norm_num)
      · exact hpX.trans (by norm_num)
    have := key _ rfl hdvd
    subst this
    omega
  ·
    have hinj : Function.Injective φ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
      · exact (MonoidHom.ker_eq_bot_iff φ).1 h
      · exfalso
        have h1 : ∀ s : alternatingGroup (Fin n), s = 1 := fun s => by
          obtain ⟨x, rfl⟩ := hφ s
          exact (MonoidHom.mem_ker).1 (h ▸ mem_top x)
        have h2 : Nat.card (alternatingGroup (Fin n)) = 1 :=
          Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩, inferInstance⟩
        rw [card_alternating_fin n (by omega)] at h2
        interval_cases n <;> simp [Nat.factorial] at h2
    have hc : Nat.card X = n.factorial / 2 := by
      rw [← card_alternating_fin n (by omega)]
      exact Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hφ⟩)
    rw [hc] at hpX
    have h1 : p ∣ n.factorial := hpX.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num)
      (by omega)))
    have := (Nat.Prime.dvd_factorial hp).1 h1
    omega

end Linear

end CFSG.Quasithin.H13.A7
