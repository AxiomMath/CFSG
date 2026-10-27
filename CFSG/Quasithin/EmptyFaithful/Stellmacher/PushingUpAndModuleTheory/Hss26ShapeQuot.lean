module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups

public section

namespace CFSG.Quasithin.F53

open Equiv

@[expose] def NoNormalTwo (Q : Type*) [Group Q] : Prop :=
  ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥

section Abstract

variable {Q : Type*} [Group Q]

theorem normalCore_eq_bot_of_noNormalTwo (hQ : NoNormalTwo Q) {T : Subgroup Q}
    (hT : IsPGroup 2 T) : T.normalCore = ⊥ :=
  hQ _ inferInstance (hT.to_le (Subgroup.normalCore_le T))

theorem card_le_factorial_index [Finite Q] {T : Subgroup Q} (h : T.normalCore = ⊥) :
    Nat.card Q ≤ T.index.factorial := by
  have hinj : Function.Injective (MulAction.toPermHom Q (Q ⧸ T)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]; exact h
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_perm] at this

theorem card_eq_six [Finite Q] (hQ : NoNormalTwo Q) {T : Subgroup Q}
    (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hi : T.index = 3) : Nat.card Q = 6 := by
  have h1 := card_le_factorial_index (normalCore_eq_bot_of_noNormalTwo hQ hT)
  rw [hi] at h1
  have h2 := T.card_mul_index
  have h3 : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT0
  rw [hi] at h2
  have : Nat.factorial 3 = 6 := rfl
  omega

theorem nonempty_mulEquiv_perm3 [Finite Q] (hQ : NoNormalTwo Q)
    {T : Subgroup Q} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hi : T.index = 3) :
    Nonempty (Q ≃* Perm (Fin 3)) := by
  have hc := card_eq_six hQ hT hT0 hi
  have hinj : Function.Injective (MulAction.toPermHom Q (Q ⧸ T)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    exact normalCore_eq_bot_of_noNormalTwo hQ hT
  have hbij : Function.Bijective (MulAction.toPermHom Q (Q ⧸ T)) := by
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [Nat.card_perm, hc]
    show 6 = (T.index).factorial
    rw [hi]; rfl
  have hcard : Nat.card (Q ⧸ T) = 3 := hi
  exact ⟨(MulEquiv.ofBijective _ hbij).trans (Equiv.permCongrHom (Finite.equivFinOfCardEq hcard))⟩

theorem sylow5_normal [Finite Q] {a : ℕ} (ha : a ≤ 3) (hQ : Nat.card Q = 5 * 2 ^ a) (y : Q)
    (hy : orderOf y = 5) (v : Q) : v * y * v⁻¹ ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 Q))
  have hf : (Nat.card Q).factorization 5 = 1 := by
    rw [hQ, Nat.factorization_def _ Nat.prime_five]
    interval_cases a <;> decide +kernel
  have hP : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity, hf]; norm_num
  have hidx : (P : Subgroup Q).index = 2 ^ a := by
    have := (P : Subgroup Q).card_mul_index
    rw [hP, hQ] at this
    omega
  have hn : Nat.card (Sylow 5 Q) = 1 := by
    have h1 := card_sylow_modEq_one 5 Q
    have h2 : Nat.card (Sylow 5 Q) ∣ 2 ^ a := hidx ▸ P.card_dvd_index
    have hmain : ∀ n : ℕ, n % 5 = 1 → n ∣ 2 ^ a → n = 1 := by
      intro n hn1 hn2
      have h5 : 2 ^ a ≤ 8 := by
        calc 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha
          _ = 8 := by norm_num
      have : n ≤ 8 := (Nat.le_of_dvd (by positivity) hn2).trans h5
      clear hQ hf hP hidx h1 h2 hy
      interval_cases a <;> interval_cases n <;> first | rfl | omega
    exact hmain _ h1 h2
  have : Subsingleton (Sylow 5 Q) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hPn : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  have hz : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  obtain ⟨R, hR⟩ := hz.exists_le_sylow
  have hRP : R = P := Subsingleton.elim _ _
  subst hRP
  have heq : Subgroup.zpowers y = (R : Subgroup Q) :=
    Subgroup.eq_of_le_of_card_ge hR (by rw [hP, Nat.card_zpowers, hy])
  rw [heq]
  exact hPn.conj_mem y (heq ▸ Subgroup.mem_zpowers y) v

end Abstract

section PermFive

theorem perm5_no_commute : ∀ y : Perm (Fin 5), y ^ 5 = 1 → y ≠ 1 →
    ∀ t : Perm (Fin 5), t * t = 1 → t ≠ 1 → t * y ≠ y * t := by decide +kernel

theorem commute_or_inv {G : Type*} [Group G] {v y : G} (hv : v * v = 1) (hy : orderOf y = 5)
    (hj : ∃ j : Fin 5, v * y * v⁻¹ = y ^ (j : ℕ)) : v * y = y * v ∨ v * y * v⁻¹ = y⁻¹ := by
  obtain ⟨⟨j, hjlt⟩, hj⟩ := hj
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hy5 : y ^ 5 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have h1 : y ^ (j * j) = y ^ 1 := by
    calc y ^ (j * j) = (y ^ j) ^ j := pow_mul y j j
      _ = (v * y * v⁻¹) ^ j := by rw [hj]
      _ = v * y ^ j * v⁻¹ := conj_pow
      _ = v * (v * y * v⁻¹) * v⁻¹ := by rw [hj]
      _ = y ^ 1 := by
        rw [hvi, pow_one]
        calc v * (v * y * v) * v = (v * v) * y * (v * v) := by group
          _ = y := by rw [hv]; simp
  have h2 : j * j ≡ 1 [MOD 5] := hy ▸ pow_eq_pow_iff_modEq.1 h1
  simp only at hj
  interval_cases j
  · exact absurd h2 (by decide)
  · left
    rw [pow_one] at hj
    exact mul_inv_eq_iff_eq_mul.1 hj
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · right
    rw [hj]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy5)

theorem mem_zpowers_fin {G : Type*} [Group G] {y x : G} (hy : orderOf y = 5)
    (hx : x ∈ Subgroup.zpowers y) : ∃ j : Fin 5, x = y ^ (j : ℕ) := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨⟨(n % 5).toNat, by omega⟩, ?_⟩
  have h1 : ((n % 5).toNat : ℤ) = n % 5 := Int.toNat_of_nonneg (by omega)
  rw [← zpow_mod_orderOf, hy, Nat.cast_ofNat]
  show y ^ (n % 5) = y ^ (n % 5).toNat
  rw [← zpow_natCast, h1]

theorem perm5_no_index_three (K : Subgroup (Perm (Fin 5))) (hK : K.index = 3) : False := by
  have hKc : Nat.card K = 40 := by
    have := K.card_mul_index
    rw [hK, card_perm5] at this
    omega
  set C := K.normalCore with hC
  have hCK : C ≤ K := Subgroup.normalCore_le K
  have hidx : C.index ≤ 6 := by
    have h1 : C.index = Nat.card (MulAction.toPermHom (Perm (Fin 5)) (Perm (Fin 5) ⧸ K)).range := by
      rw [hC, Subgroup.normalCore_eq_ker]
      exact Subgroup.index_ker _
    have h2 := Subgroup.card_le_card_group
      (MulAction.toPermHom (Perm (Fin 5)) (Perm (Fin 5) ⧸ K)).range
    rw [Nat.card_perm] at h2
    have h3 : Nat.card (Perm (Fin 5) ⧸ K) = 3 := hK
    rw [h3] at h2
    rw [h1]
    exact h2.trans (by decide)
  have hC20 : 20 ≤ Nat.card C := by
    have h1 := C.card_mul_index
    rw [card_perm5] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card C * C.index ≤ 19 * 6 := Nat.mul_le_mul (by omega) hidx
    omega
  have hnot : ¬ IsPGroup 2 C := by
    intro hp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
    have hd : 2 ^ k ∣ 120 := hk ▸ (card_perm5 ▸ Subgroup.card_subgroup_dvd_card C)
    have hk5 : 5 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 hk5
    have := this.trans hd
    omega
  have hnorm : ∀ k ∈ (⊤ : Subgroup (Perm (Fin 5))), ∀ y ∈ C, k * y * k⁻¹ ∈ C :=
    fun k _ y hy => (inferInstance : C.Normal).conj_mem y hy k
  set c3 : Perm (Fin 5) := swap 0 1 * swap 1 2 with hc3
  have hc3o : orderOf c3 = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_ <;> rw [hc3] <;> decide +kernel
  have hmem := mem_of_normal_odd_five ⊤ C (le_top) hnorm hnot c3 (Subgroup.mem_top _)
    (by rw [hc3o]; decide)
  have hd : orderOf (⟨c3, hCK hmem⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have : orderOf (⟨c3, hCK hmem⟩ : K) = 3 := by rw [← hc3o, ← Subgroup.orderOf_coe]
  rw [this, hKc] at hd
  omega

theorem eq_alternatingGroup_of_card_sixty (K : Subgroup (Perm (Fin 5))) (h : Nat.card K = 60) :
    K = alternatingGroup (Fin 5) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have h1 := K.card_mul_index
  rw [h, card_perm5] at h1
  omega

theorem perm5_shape (K : Subgroup (Perm (Fin 5))) {T : Subgroup ↥K} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hT0 : T ≠ ⊥) (hK : NoNormalTwo ↥K) :
    Nonempty (↥K ≃* Perm (Fin 3)) ∨ K = alternatingGroup (Fin 5) ∨ K = ⊤ ∨
      ∃ y ∈ K, orderOf y = 5 ∧ ∀ t ∈ K, t * t = 1 → t ≠ 1 → t * y * t⁻¹ = y⁻¹ := by
  have h120 : Nat.card K ∣ 120 := card_perm5 ▸ Subgroup.card_subgroup_dvd_card K
  have hmul := T.card_mul_index
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hT
  have hT2 : 1 < Nat.card T := (Subgroup.one_lt_card_iff_ne_bot T).mpr hT0
  obtain ⟨m, hm⟩ : ∃ m, T.index = m := ⟨_, rfl⟩
  rw [hm] at hmul hTi
  have hmd : m ∣ 120 := (Dvd.intro_left _ hmul).trans h120
  have hm1 : m ≤ 120 := Nat.le_of_dvd (by norm_num) hmd
  have hmcases : m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 15 := by
    clear hmul hm ha h120
    interval_cases m <;> omega
  rcases hmcases with rfl | rfl | rfl | rfl
  · exfalso
    have hT' : T = ⊤ := Subgroup.index_eq_one.mp hm
    subst hT'
    exact hT0 (hK ⊤ inferInstance hT)
  · exact Or.inl (nonempty_mulEquiv_perm3 hK hT hT0 hm)
  · right; right; right
    have ha3 : a ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h1 : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
      have h2 : 2 ^ a ∣ 120 := ha ▸ ((Dvd.intro _ rfl : Nat.card T ∣ Nat.card T * 5).trans
        (hmul ▸ h120))
      have := h1.trans h2
      omega
    have hKc : Nat.card K = 5 * 2 ^ a := by rw [← hmul, ha]; ring
    have hKc' : a ≠ 3 := by
      rintro rfl
      apply perm5_no_index_three K
      have := K.card_mul_index
      rw [hKc, card_perm5] at this
      omega
    have h5 : 5 ∣ Nat.card K := ⟨2 ^ a, hKc⟩
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 h5
    have hy : orderOf (y' : Perm (Fin 5)) = 5 := by rw [Subgroup.orderOf_coe, hy']
    have hy5 : (y' : Perm (Fin 5)) ^ 5 = 1 := by
      have := pow_orderOf_eq_one (y' : Perm (Fin 5))
      rwa [hy] at this
    have hy1 : (y' : Perm (Fin 5)) ≠ 1 := fun h1 => by simp [h1] at hy
    refine ⟨y', y'.2, hy, fun t ht ht2 ht1 => ?_⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (sylow5_normal ha3 hKc y' hy' ⟨t, ht⟩)
    have h2 : t * y' * t⁻¹ ∈ Subgroup.zpowers (y' : Perm (Fin 5)) :=
      Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
    exact (commute_or_inv ht2 hy (mem_zpowers_fin hy h2 |>.imp fun j hj => hj)).resolve_left
      (perm5_no_commute _ hy5 hy1 t ht2 ht1)
  · have h15 : 15 ∣ Nat.card K := Dvd.intro_left _ hmul
    have hA := alt5_le_of_dvd K h15
    have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
      rw [card_perm5] at h
      omega
    have h60 : 60 ∣ Nat.card K := hA60 ▸ Subgroup.card_dvd_of_le hA
    have hle : Nat.card K ≤ 120 := Nat.le_of_dvd (by norm_num) h120
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hc : Nat.card K = 60 ∨ Nat.card K = 120 := by omega
    rcases hc with hc | hc
    · exact Or.inr (Or.inl (eq_alternatingGroup_of_card_sixty K hc))
    · exact Or.inr (Or.inr (Or.inl (Subgroup.eq_top_of_card_eq K (by rw [card_perm5]; exact hc))))

theorem perm3_shape (K : Subgroup (Perm (Fin 3))) {T : Subgroup ↥K} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hT0 : T ≠ ⊥) (hK : NoNormalTwo ↥K) :
    Nonempty (↥K ≃* Perm (Fin 3)) := by
  have h6 : Nat.card K ∣ 6 := card_perm3 ▸ Subgroup.card_subgroup_dvd_card K
  have hmul := T.card_mul_index
  obtain ⟨m, hm⟩ : ∃ m, T.index = m := ⟨_, rfl⟩
  rw [hm] at hmul hTi
  have hmd : m ∣ 6 := (Dvd.intro_left _ hmul).trans h6
  have hm1 : m ≤ 6 := Nat.le_of_dvd (by norm_num) hmd
  have hmcases : m = 1 ∨ m = 3 := by
    clear hmul hm h6
    interval_cases m <;> omega
  rcases hmcases with rfl | rfl
  · exfalso
    have hT' : T = ⊤ := Subgroup.index_eq_one.mp hm
    subst hT'
    exact hT0 (hK ⊤ inferInstance hT)
  · exact nonempty_mulEquiv_perm3 hK hT hT0 hm

end PermFive

end CFSG.Quasithin.F53
