module

public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input

public section

namespace CFSG.Monster.Existence

open CFSG.Open

theorem sq_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {a : G} (h : orderOf a = 2) :
    a ^ 2 = 1 := by
  rw [← h, pow_orderOf_eq_one]

theorem ne_one_of_orderOf_eq_two {G : Type*} [Group G] {a : G} (h : orderOf a = 2) : a ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  norm_num at h

theorem eq_of_isCyclic_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite G
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · exact one_pow 2
    · exact sq_eq_one_of_orderOf_eq_two ha
    · exact sq_eq_one_of_orderOf_eq_two hb
  have hcard : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(ne_one_of_orderOf_eq_two ha).symm, (ne_one_of_orderOf_eq_two hb).symm⟩
  have := Finset.card_le_card hsub
  omega

theorem QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one {n : ℕ} [NeZero n] {x : QuaternionGroup n}
    (hx : x ^ 2 = 1) : x = 1 ∨ x = QuaternionGroup.a n := by
  rcases x with i | i
  · rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at hx
    rw [QuaternionGroup.one_def, QuaternionGroup.a.injEq, QuaternionGroup.a.injEq]
    have hv : i = ((i.val : ℕ) : ZMod (2 * n)) := (ZMod.natCast_zmod_val i).symm
    rw [hv, ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hx
    have hlt : i.val < 2 * n := ZMod.val_lt i
    obtain ⟨k, hk⟩ := hx
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have h4 : 2 * n * k < 2 * n * 2 := by rw [← hk]; omega
    have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left h4
    interval_cases k
    · left
      rw [hv]
      have : i.val = 0 := by omega
      rw [this, Nat.cast_zero]
    · right
      rw [hv]
      have : i.val = n := by omega
      rw [this]
  · rw [QuaternionGroup.xa_sq, QuaternionGroup.one_def, QuaternionGroup.a.injEq,
      ZMod.natCast_eq_zero_iff] at hx
    exfalso
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact absurd (Nat.le_of_dvd hn hx) (by omega)

theorem eq_of_mulEquiv_quaternion_of_orderOf_eq_two {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (e : G ≃* QuaternionGroup n) {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have hea : e a ^ 2 = 1 := by rw [← map_pow, sq_eq_one_of_orderOf_eq_two ha, map_one]
  have heb : e b ^ 2 = 1 := by rw [← map_pow, sq_eq_one_of_orderOf_eq_two hb, map_one]
  have ha1 : e a ≠ 1 := fun h => ne_one_of_orderOf_eq_two ha (e.injective (h.trans e.map_one.symm))
  have hb1 : e b ≠ 1 := fun h => ne_one_of_orderOf_eq_two hb (e.injective (h.trans e.map_one.symm))
  apply e.injective
  rcases QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one hea with h | h
  · exact absurd h ha1
  rcases QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one heb with h' | h'
  · exact absurd h' hb1
  rw [h, h']

section Anchored

variable {E : Type} [Group E]

theorem odd_card_inf_conj_of_anchored [Finite E] (M : Subgroup E)
    (hM : ∀ i ∈ M, orderOf i = 2 → ∀ g : E, g * i * g⁻¹ ∈ M → g ∈ M) {g : E} (hg : g ∉ M) :
    Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hodd.two_dvd
  have hi : orderOf (y : E) = 2 := (Subgroup.orderOf_coe y).trans hy
  have hiM : (y : E) ∈ M := (Subgroup.mem_inf.1 y.2).1
  obtain ⟨m, hm, hmi⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 y.2).2
  have hmi' : g⁻¹ * m * g = (y : E) := by
    rw [← hmi]
    simp
  apply hg
  refine hM (y : E) hiM hi g ?_
  rw [← hmi']
  simpa [mul_assoc] using hm

theorem fusionStronglyEmbedded_of_anchored [Finite E] (M : Subgroup E) (hne : M ≠ ⊤) {t : E}
    (htM : t ∈ M) (ht : orderOf t = 2)
    (hM : ∀ i ∈ M, orderOf i = 2 → ∀ g : E, g * i * g⁻¹ ∈ M → g ∈ M) :
    fusionStronglyEmbedded M := by
  refine ⟨hne, ?_, fun g hg => odd_card_inf_conj_of_anchored M hM hg⟩
  have h : orderOf (⟨t, htM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  exact even_iff_two_dvd.2 (h ▸ orderOf_dvd_natCard _)

end Anchored

section Odd

variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
theorem eq_one_of_isPGroup_two_of_odd {K : Subgroup E} (hK : Odd (Nat.card K)) {y : E}
    (hyK : y ∈ K) {k : ℕ} (hy : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf (⟨y, hyK⟩ : K) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hy)
  have h2 : orderOf (⟨y, hyK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf (⟨y, hyK⟩ : K)) (Nat.card K) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hK))
  have h3 := Nat.Coprime.eq_one_of_dvd hcop h2
  rw [orderOf_eq_one_iff] at h3
  exact congrArg Subtype.val h3

omit [Finite E] in
theorem le_of_isPGroup_two_of_odd_index {N : Subgroup E} [N.Normal] (hidx : Odd N.index)
    {P : Subgroup E} (hP : IsPGroup 2 P) : P ≤ N := by
  intro t ht
  obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk t : E ⧸ N) ^ 2 ^ k = 1 := by
    rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk t : E ⧸ N) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk t : E ⧸ N) ∣ N.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk t : E ⧸ N)) N.index :=
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hidx))
  have h4 := Nat.Coprime.eq_one_of_dvd hcop h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

end Odd

theorem natCard_center_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (Q : Subgroup X) : Nat.card (Subgroup.center (Q.map e.toMonoidHom)) =
      Nat.card (Subgroup.center Q) :=
  Nat.card_congr (Subgroup.centerCongr (Q.equivMapOfInjective e.toMonoidHom e.injective)).symm.toEquiv

theorem four_le_card_center_sylow_of_isBenderGroup
    {X : Type} [Group X] [Finite X]
    (hX : fusionIsBenderGroup X) (Q : Sylow 2 X) : 4 ≤ Nat.card (Subgroup.center Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨-, -, -, hc, -⟩ :=
      CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf
        (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)
    have hc' : Nat.card (Subgroup.center ((Q : Subgroup X).map e.toMonoidHom)) = _ := hc
    rw [natCard_center_map_mulEquiv] at hc'
    rw [hc']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · obtain ⟨-, -, -, hc, -⟩ :=
      CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2 f hf
        (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)
    have hc' : Nat.card (Subgroup.center ((Q : Subgroup X).map e.toMonoidHom)) = _ := hc
    rw [natCard_center_map_mulEquiv] at hc'
    rw [hc']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  · obtain ⟨-, -, -, hc, -⟩ :=
      CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 a ha
        (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)
    have hc' : Nat.card (Subgroup.center ((Q : Subgroup X).map e.toMonoidHom)) = _ := hc
    rw [natCard_center_map_mulEquiv] at hc'
    rw [hc']
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem eq_top_of_anchored_involutions
    {E : Type} [Group E] [Finite E] (M : Subgroup E)
    (hM : ∀ i ∈ M, orderOf i = 2 → ∀ g : E, g * i * g⁻¹ ∈ M → g ∈ M)
    (T : Sylow 2 E) (hTM : (T : Subgroup E) ≤ M) (hZ : Nat.card (Subgroup.center T) = 2)
    {a b : E} (haT : a ∈ T) (hbT : b ∈ T) (hab : a ≠ b) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : M = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hSE := fusionStronglyEmbedded_of_anchored M hne (hTM haT) ha hM
  have ha' : orderOf (⟨a, haT⟩ : T) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hb' : orderOf (⟨b, hbT⟩ : T) = 2 := by rw [Subgroup.orderOf_mk]; exact hb
  have hab' : (⟨a, haT⟩ : T) ≠ ⟨b, hbT⟩ := fun h => hab (congrArg Subtype.val h)
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 E M
      hSE with hcq | ⟨M₀, N, hM₀, hN, hM₀N, -, hodd, hidx, hB⟩
  · rcases hcq T with hcyc | ⟨r, hr, ⟨e⟩⟩
    · exact hab' (eq_of_isCyclic_of_orderOf_eq_two ha' hb')
    · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
      exact hab' (eq_of_mulEquiv_quaternion_of_orderOf_eq_two e ha' hb')
  · have hTN : (T : Subgroup E) ≤ N := le_of_isPGroup_two_of_odd_index hidx T.isPGroup'
    let T₁ : Sylow 2 N := T.subtype hTN
    let f : N →* N ⧸ M₀.subgroupOf N := QuotientGroup.mk' _
    let T₂ : Sylow 2 (N ⧸ M₀.subgroupOf N) := T₁.mapSurjective (QuotientGroup.mk'_surjective _)
    have hinj : Function.Injective (f.comp (T₁ : Subgroup N).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy
      obtain ⟨k, hk⟩ := T₁.isPGroup' y
      have hk' : (((y : N) : E)) ^ 2 ^ k = 1 := by
        have := congrArg (fun z : T₁ => ((z : N) : E)) hk
        simpa using this
      have := eq_one_of_isPGroup_two_of_odd hodd hy hk'
      exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext this))
    have hrange : (f.comp (T₁ : Subgroup N).subtype).range =
        (T₂ : Subgroup (N ⧸ M₀.subgroupOf N)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, Sylow.coe_mapSurjective]
    have e₁ : (T₁ : Subgroup N) ≃* (T₂ : Subgroup (N ⧸ M₀.subgroupOf N)) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    have e₀ : (T₁ : Subgroup N) ≃* (T : Subgroup E) := by
      rw [Sylow.coe_subtype]
      exact Subgroup.subgroupOfEquivOfLe hTN
    have hc : Nat.card (Subgroup.center (T₂ : Subgroup (N ⧸ M₀.subgroupOf N))) = 2 := by
      exact (Nat.card_congr (Subgroup.centerCongr (e₁.symm.trans e₀)).toEquiv).trans hZ
    have h4 := four_le_card_center_sylow_of_isBenderGroup hB T₂
    omega

end CFSG.Monster.Existence
