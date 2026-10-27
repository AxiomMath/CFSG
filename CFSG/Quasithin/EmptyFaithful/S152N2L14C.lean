module

public import CFSG.Quasithin.EmptyFaithful.S152FinSmall

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

theorem card_of_isSmallGroup152 {X : Type*} [Group X] (hX : IsSmallGroup152 X) :
    Nat.card X = 6 ∨ Nat.card X = 10 ∨ Nat.card X = 20 := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  · right; left
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  · right; right
    rw [Nat.card_congr e.toEquiv]
    exact card_sz_zero_eq_twenty

theorem isSolvable_of_card_six_or_ten {X : Type*} [Group X] [Finite X]
    (h : Nat.card X = 6 ∨ Nat.card X = 10) : Group.IsSolvable X := by
  have hsq : Squarefree (Nat.card X) := by
    rcases h with h | h
    · rw [h]
      have := (Nat.squarefree_mul (m := 2) (n := 3) (by norm_num)).mpr
        ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
      simpa using this
    · rw [h]
      have := (Nat.squarefree_mul (m := 2) (n := 5) (by norm_num)).mpr
        ⟨Nat.prime_two.squarefree, Nat.prime_five.squarefree⟩
      simpa using this
  have : IsZGroup X := IsZGroup.of_squarefree hsq
  infer_instance

theorem isSolvable_of_card_twenty {X : Type*} [Group X] [Finite X] (hcard : Nat.card X = 20) :
    Group.IsSolvable X := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hPcard : Nat.card (P : Subgroup X) = 5 := by
    rw [P.card_eq_multiplicity, hcard]
    have : (20 : ℕ).factorization 5 = 1 := S152Fin.factorization_twenty_five
    rw [this]
    norm_num
  have hidx : (P : Subgroup X).index = 4 := by
    have := (P : Subgroup X).card_mul_index
    rw [hPcard, hcard] at this
    omega
  have hn5 : Nat.card (Sylow 5 X) = 1 := by
    have h1 := card_sylow_modEq_one 5 X
    have h2 := P.card_dvd_index
    rw [hidx] at h2
    have hle : Nat.card (Sylow 5 X) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 5 X) := Nat.card_pos
    unfold Nat.ModEq at h1
    interval_cases h : Nat.card (Sylow 5 X) <;> simp_all
  have hsub : Subsingleton (Sylow 5 X) := by
    have : Nat.card (Sylow 5 X) ≤ 1 := hn5.le
    exact (Finite.card_le_one_iff_subsingleton).mp (by simpa [Nat.card_eq_fintype_card] using this)
  have hPn : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
  have hPcyc : IsCyclic (P : Subgroup X) := isCyclic_of_prime_card hPcard
  have hPs : Group.IsSolvable (P : Subgroup X) := inferInstance
  have hq : Nat.card (X ⧸ (P : Subgroup X)) = 4 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hqp : IsPGroup 2 (X ⧸ (P : Subgroup X)) := by
    refine (IsPGroup.iff_card).mpr ⟨2, ?_⟩
    rw [hq]; norm_num
  have : Group.IsNilpotent (X ⧸ (P : Subgroup X)) := hqp.isNilpotent
  have hqs : Group.IsSolvable (X ⧸ (P : Subgroup X)) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient (P : Subgroup X)

theorem isSolvable_of_isSmallGroup152 {X : Type*} [Group X] [Finite X] (hX : IsSmallGroup152 X) :
    Group.IsSolvable X := by
  rcases card_of_isSmallGroup152 hX with h | h | h
  · exact isSolvable_of_card_six_or_ten (Or.inl h)
  · exact isSolvable_of_card_six_or_ten (Or.inr h)
  · exact isSolvable_of_card_twenty h

theorem isSolvable_of_equiv_D33 {X : Type*} [Group X] (e : X ≃* DihedralGroup 3 × DihedralGroup 3) :
    Group.IsSolvable X := by
  have h6 : Group.IsSolvable (DihedralGroup 3) := by
    have : Nat.card (DihedralGroup 3) = 6 := by rw [DihedralGroup.nat_card]
    exact isSolvable_of_card_six_or_ten (Or.inl this)
  have : Group.IsSolvable (DihedralGroup 3 × DihedralGroup 3) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem pCore_two_eq_bot_of_involution_products {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ x : X, x * x = 1 → x ≠ 1 →
      ∃ g : X, (x * (g * x * g⁻¹)) ^ p = 1 ∧ x * (g * x * g⁻¹) ≠ 1) :
    CFSG.Open.pCore 2 X = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCore 2 X with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := X)
  have hQn : Q.Normal := CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := X)
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hk
  have hdvd : 2 ∣ Nat.card Q := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : (x : X) * (x : X) = 1 := by
    have : (x : X) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hx
      exact hx ▸ pow_orderOf_eq_one _
    simpa [sq] using this
  have hx1 : (x : X) ≠ 1 := by
    intro h1
    have : orderOf x = 1 := by
      rw [← Subgroup.orderOf_coe, h1, orderOf_one]
    rw [hx] at this
    exact absurd this (by norm_num)
  obtain ⟨g, hy3, hy1⟩ := h (x : X) hx2 hx1
  have hxg : g * (x : X) * g⁻¹ ∈ Q := hQn.conj_mem _ x.2 g
  have hyQ : (x : X) * (g * x * g⁻¹) ∈ Q := Q.mul_mem x.2 hxg
  obtain ⟨m, hm⟩ := hQ2 ⟨_, hyQ⟩
  have hm' : ((x : X) * (g * x * g⁻¹)) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hdvdp : orderOf ((x : X) * (g * x * g⁻¹)) ∣ p := orderOf_dvd_of_pow_eq_one hy3
  have hdvd2 : orderOf ((x : X) * (g * x * g⁻¹)) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
  rcases (Nat.dvd_prime hp).mp hdvdp with h3 | h3
  · exact hy1 (orderOf_eq_one_iff.mp h3)
  · rw [h3] at hdvd2
    have := (Nat.Prime.dvd_of_dvd_pow hp hdvd2 : p ∣ 2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

theorem pCore_two_eq_bot_of_equiv {X D : Type*} [Group X] [Finite X] [Group D] (e : X ≃* D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ x : D, x * x = 1 → x ≠ 1 →
      ∃ g : D, (x * (g * x * g⁻¹)) ^ p = 1 ∧ x * (g * x * g⁻¹) ≠ 1) :
    CFSG.Open.pCore 2 X = ⊥ := by
  refine pCore_two_eq_bot_of_involution_products hp hp2 ?_
  intro x hx2 hx1
  obtain ⟨g, hg3, hg1⟩ := h (e x) (by rw [← map_mul, hx2, map_one])
    (fun h' => hx1 (e.injective (by rw [h', map_one])))
  have key : e (x * (e.symm g * x * (e.symm g)⁻¹)) = e x * (g * e x * g⁻¹) := by simp
  refine ⟨e.symm g, ?_, ?_⟩
  · apply e.injective
    rw [map_pow, key, map_one]
    exact hg3
  · intro h'
    apply hg1
    rw [← key, h', map_one]

theorem S3_invol : ∀ x : Equiv.Perm (Fin 3), x * x = 1 → x ≠ 1 →
    ∃ g : Equiv.Perm (Fin 3), (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1 := by decide +kernel

theorem D5_invol : ∀ x : DihedralGroup 5, x * x = 1 → x ≠ 1 →
    ∃ g : DihedralGroup 5, (x * (g * x * g⁻¹)) ^ 5 = 1 ∧ x * (g * x * g⁻¹) ≠ 1 := by decide +kernel

theorem D33_invol : ∀ x : DihedralGroup 3 × DihedralGroup 3, x * x = 1 → x ≠ 1 →
    ∃ g : DihedralGroup 3 × DihedralGroup 3,
      (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1 := by decide +kernel

theorem pCore_eq_bot_of_sz {X : Type*} [Group X] (e : X ≃* ↥(CFSG.Open.Sz 0)) :
    CFSG.Open.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite X := Finite.of_equiv _ e.symm.toEquiv
  set N := CFSG.Open.pCore 2 X with hN
  have hmapN : (N.map e.toMonoidHom).Normal :=
    (CFSG.LieType.BorelTits.pCore_normal (r := 2) (G := X)).map e.toMonoidHom e.surjective
  have hmapp : IsPGroup 2 (N.map e.toMonoidHom) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (r := 2) (G := X)).map e.toMonoidHom
  have hle := le_pCore 2 hmapN hmapp
  rw [pCore_two_sz_zero_eq_bot] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp (le_bot_iff.mp hle)

theorem pCore_eq_bot_of_isSmallGroup152 {X : Type*} [Group X] [Finite X] (hX : IsSmallGroup152 X) :
    CFSG.Open.pCore 2 X = ⊥ := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact pCore_two_eq_bot_of_equiv e Nat.prime_three (by norm_num) S3_invol
  · exact pCore_two_eq_bot_of_equiv e Nat.prime_five (by norm_num) D5_invol
  · exact pCore_eq_bot_of_sz e

theorem pCore_eq_bot_of_equiv_D33 {X : Type*} [Group X] [Finite X]
    (e : X ≃* DihedralGroup 3 × DihedralGroup 3) : CFSG.Open.pCore 2 X = ⊥ :=
  pCore_two_eq_bot_of_equiv e Nat.prime_three (by norm_num) D33_invol

theorem card_of_equiv_D33 {X : Type*} [Group X] (e : X ≃* DihedralGroup 3 × DihedralGroup 3) :
    Nat.card X = 36 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]

theorem eq_or_eq_of_relIndex_prime {Γ : Type*} [Group Γ] {A B C : Subgroup Γ} (hAB : A ≤ B)
    (hBC : B ≤ C) (hp : (A.relIndex C).Prime) : B = A ∨ B = C := by
  have h := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  rw [← h] at hp
  rcases Nat.prime_mul_iff.mp hp with ⟨-, h1⟩ | ⟨-, h1⟩
  · right
    exact le_antisymm hBC (Subgroup.relIndex_eq_one.mp h1)
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB

end S152N2

end CFSG.Quasithin
