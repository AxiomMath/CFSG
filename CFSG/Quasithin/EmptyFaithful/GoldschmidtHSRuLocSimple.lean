module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open CFSG.Quasithin CFSG.Quasithin.A312Ru CFSG.ProperTwoGeneratedCore.CosetNormalizer Equiv

variable {H : Type} [Group H]

theorem mem_of_mem_ker_toPermHom {N : Subgroup H} {g : H}
    (hg : g ∈ (MulAction.toPermHom H (H ⧸ N)).ker) : g ∈ N := by
  have h1 := congrArg (fun f : Perm (H ⧸ N) => f ((1 : H) : H ⧸ N)) (MonoidHom.mem_ker.mp hg)
  simp at h1
  simpa using QuotientGroup.eq.mp h1

variable [Finite H] [IsSimpleGroup H]

theorem card_le_factorial_of_index {N : Subgroup H} (hN : N ≠ ⊤) :
    Nat.card H ≤ N.index.factorial := by
  have hker : (MulAction.toPermHom H (H ⧸ N)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (MulAction.toPermHom H (H ⧸ N)).ker with h | h
    · exact h
    · exfalso
      apply hN
      rw [eq_top_iff]
      intro g _
      exact mem_of_mem_ker_toPermHom (h ▸ Subgroup.mem_top g)
  have h1 := Nat.card_le_card_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp hker)
  rw [Nat.card_perm] at h1
  exact h1

theorem exists_perm_seven {N : Subgroup H} (hN : N.index = 7) :
    ∃ ι : H →* Perm (Fin 7), Function.Injective ι ∧ ∀ i j : Fin 7, ∃ h : H, ι h i = j := by
  classical
  have hcard : Nat.card (H ⧸ N) = 7 := hN
  let e : (H ⧸ N) ≃ Fin 7 := (Finite.equivFin (H ⧸ N)).trans (finCongr hcard)
  let ρ0 : H →* Perm (H ⧸ N) := MulAction.toPermHom H (H ⧸ N)
  have hker : ρ0.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ0.ker with h | h
    · exact h
    · exfalso
      have : N = ⊤ := top_le_iff.mp (fun g _ => mem_of_mem_ker_toPermHom (h ▸ Subgroup.mem_top g))
      rw [this, Subgroup.index_top] at hN
      omega
  refine ⟨e.permCongrHom.toMonoidHom.comp ρ0, ?_, fun i j => ?_⟩
  · exact e.permCongrHom.injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker)
  · obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H (e.symm i) (e.symm j)
    refine ⟨y, ?_⟩
    show e (ρ0 y (e.symm i)) = j
    have h1 : ρ0 y (e.symm i) = y • e.symm i := rfl
    rw [h1, hy]
    simp

theorem factorization_168_three : (168 : ℕ).factorization 3 = 1 := by
  rw [show (168 : ℕ) = 3 * 56 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp [Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 56 by norm_num)]

theorem isPSL_of_order_six (hcard : Nat.card H = 168) {x : H} (hx : orderOf x = 6) :
    IsPSL 3 2 1 H := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : H := x ^ 2 with ha
  have ha3 : orderOf a = 3 := by
    rw [ha, orderOf_pow' x (by norm_num : 2 ≠ 0), hx]
    norm_num
  have hA3 : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  have hA : Nat.card (Subgroup.zpowers a) = 3 ^ (Nat.card H).factorization 3 := by
    rw [hA3, hcard, factorization_168_three]
    norm_num
  let P : Sylow 3 H := Sylow.ofCard (Subgroup.zpowers a) hA
  have hPA : (P : Subgroup H) = Subgroup.zpowers a := rfl
  have hx6 : Nat.card (Subgroup.zpowers x) = 6 := by rw [Nat.card_zpowers, hx]
  have hcomm : ∀ k l : ℤ, x ^ k * a ^ l = a ^ l * x ^ k := fun k l => by
    have h1 : a ^ l = x ^ (2 * l) := by
      rw [zpow_mul, ha]
      simp
    rw [h1]
    exact (((Commute.refl x).zpow_right (2 * l)).zpow_left k).eq
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer ((P : Subgroup H) : Set H) := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine Subgroup.centralizer_le_normalizer ((P : Subgroup H) : Set H) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.zpowers a := by rw [← hPA]; exact hh
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact (hcomm k l).symm
  set N := Subgroup.normalizer ((P : Subgroup H) : Set H) with hNdef
  have hNcard := Subgroup.card_mul_index N
  have hm : N.index = Nat.card (Sylow 3 H) := (Sylow.card_eq_index_normalizer P).symm
  have hmod := card_sylow_modEq_one 3 H
  have h6N : 6 ∣ Nat.card N := hx6 ▸ Subgroup.card_dvd_of_le hxN
  obtain ⟨t, ht⟩ := h6N
  rw [ht, hcard] at hNcard
  have ht28 : t * N.index = 28 := by
    have h : 6 * (t * N.index) = 6 * 28 := by rw [← mul_assoc, hNcard]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hm28 : N.index ∣ 28 := Dvd.intro_left t ht28
  have hmod' : N.index % 3 = 1 := by
    rw [hm]
    exact hmod
  have hmpos : 0 < N.index := Nat.pos_of_dvd_of_pos hm28 (by norm_num)
  have hcases : N.index = 1 ∨ N.index = 4 ∨ N.index = 7 ∨ N.index = 28 := by
    have key : ∀ m : ℕ, m ∣ 28 → m % 3 = 1 → m = 1 ∨ m = 4 ∨ m = 7 ∨ m = 28 := by
      intro m hm h3
      have := Nat.le_of_dvd (by norm_num) hm
      interval_cases m <;> omega
    exact key _ hm28 hmod'
  rcases hcases with h1 | h4 | h7 | h28
  · exfalso
    have hN : N = ⊤ := Subgroup.index_eq_one.mp h1
    have hnorm : (P : Subgroup H).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    have hPc : Nat.card (P : Subgroup H) = 3 := by rw [hPA]; exact hA3
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup H) with h | h
    · rw [h, Subgroup.card_bot] at hPc
      omega
    · rw [h, Subgroup.card_top, hcard] at hPc
      omega
  · exfalso
    have hN : N ≠ ⊤ := fun h => by rw [h, Subgroup.index_top] at h4; omega
    have := card_le_factorial_of_index hN
    rw [h4, hcard] at this
    revert this
    decide
  · obtain ⟨ι, hι, htr⟩ := exists_perm_seven h7
    exact isPSL_three_two_of_perm_seven hcard ι hι htr
  · exfalso
    have hNx : N = Subgroup.zpowers x := by
      symm
      refine Subgroup.eq_of_le_of_card_ge hxN ?_
      rw [hx6]
      rw [h28] at ht28
      omega
    have hP : Subgroup.normalizer ((P : Subgroup H) : Set H) ≤
        Subgroup.centralizer (P : Set H) := by
      intro g hg
      rw [← hNdef, hNx] at hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ Subgroup.zpowers a := by rw [← hPA]; exact hh
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
      exact (hcomm k l).symm
    have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
    have hidx := hcompl.index_eq_card
    have hPidx : (P : Subgroup H).index = 56 := by
      have := Subgroup.card_mul_index (P : Subgroup H)
      have hPc : Nat.card (P : Subgroup H) = 3 := by rw [hPA]; exact hA3
      rw [hPc, hcard] at this
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker (MonoidHom.transferSylow P hP))
      with h | h
    · rw [hPidx, h, Subgroup.card_bot] at hidx
      omega
    · rw [hPidx, h, Subgroup.card_top, hcard] at hidx
      omega

theorem isPSL_three_two_of_simple_card_168 (hcard : Nat.card H = 168) : IsPSL 3 2 1 H := by
  by_cases h6 : ∃ x : H, orderOf x = 6
  · obtain ⟨x, hx⟩ := h6
    exact isPSL_of_order_six hcard hx
  · push Not at h6
    have hnonab : ∃ a b : H, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have : IsMulCommutative H := ⟨⟨hcon⟩⟩
      have hp : (Nat.card H).Prime := Group.is_simple_iff_prime_card.mp inferInstance
      rw [hcard] at hp
      exact absurd hp (by norm_num)
    obtain ⟨-, -, ℓ, φ, -, -, -, hmodel⟩ :=
      simple_order_168_without_six_projective_seven_recognition H hnonab hcard h6
    exact CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven
      hmodel

end CFSG.Quasithin.HSRuLoc.Mod
