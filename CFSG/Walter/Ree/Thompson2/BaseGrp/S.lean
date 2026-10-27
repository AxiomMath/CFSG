module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.JT

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

section A4

variable {G : Type*} [Group G] {a t : G}

theorem inv_eq_mul_self (ht : t ^ 3 = 1) : t⁻¹ = t * t := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three]
  exact ht

theorem A4_rel₁ (ha : a * a = 1) (h : (a * t) ^ 3 = 1) : a * t * a = t⁻¹ * a * t⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [pow_three'] at h
  have e : a * t * a * (t * a * t) = 1 := by rw [← h]; group
  rw [eq_inv_of_mul_eq_one_left e, mul_inv_rev, mul_inv_rev, hai, mul_assoc]

theorem A4_rel₂ (ha : a * a = 1) (h : (a * t) ^ 3 = 1) : t * a * t = a * t⁻¹ * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [pow_three'] at h
  have e : t * a * t * (a * t * a) = 1 := by
    calc t * a * t * (a * t * a) = a⁻¹ * (a * t * (a * t) * (a * t)) * a := by group
      _ = 1 := by rw [h]; group
  rw [eq_inv_of_mul_eq_one_left e, mul_inv_rev, mul_inv_rev, hai, mul_assoc]

theorem A4_comm (ha : a * a = 1) (ht : t ^ 3 = 1) (h : (a * t) ^ 3 = 1) :
    a * (t⁻¹ * a * t) = t⁻¹ * a * t * a := by
  have h1 := A4_rel₁ ha h
  have h2 := A4_rel₂ ha h
  have hti := inv_eq_mul_self ht
  have htt : t⁻¹ * t⁻¹ = t := by
    rw [hti]
    rw [show t * t * (t * t) = t * t * t * t by group, ← pow_three', ht, one_mul]
  calc a * (t⁻¹ * a * t) = a * t * (t * a * t) := by rw [hti]; group
    _ = a * t * (a * t⁻¹ * a) := by rw [h2]
    _ = (a * t * a) * t⁻¹ * a := by group
    _ = t⁻¹ * a * (t⁻¹ * t⁻¹) * a := by rw [h1]; group
    _ = t⁻¹ * a * t * a := by rw [htt]

theorem A4_conj (ha : a * a = 1) (ht : t ^ 3 = 1) (h : (a * t) ^ 3 = 1) :
    t * a * t⁻¹ = a * (t⁻¹ * a * t) := by
  have h2 := A4_rel₂ ha h
  have hti := inv_eq_mul_self ht
  rw [A4_comm ha ht h]
  calc t * a * t⁻¹ = t * a * t⁻¹ * (a * a) := by rw [ha, mul_one]
    _ = t * (a * t⁻¹ * a) * a := by group
    _ = t * (t * a * t) * a := by rw [h2]
    _ = (t * t) * a * t * a := by group
    _ = t⁻¹ * a * t * a := by rw [hti]

end A4

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ) [Fintype k]

omit [Fintype k] in
theorem J_mem_N : C.J ∈ C.N := C.ι_mem _

omit [Fintype k] in
theorem T_mem_N : C.T ∈ C.N := C.ι_mem _

omit [Fintype k] in
theorem commute_J_of_inv {K : G} (hK : ∀ t : kˣ, K⁻¹ * C.tor t * K = C.tor t⁻¹) :
    K * C.J = C.J * K := by
  have h := hK (-1)
  rw [inv_neg_one] at h
  change K⁻¹ * C.J * K = C.J at h
  calc K * C.J = K * (K⁻¹ * C.J * K) := by rw [h]
    _ = C.J * K := by group

omit [Fintype k] in
theorem exists_S {K : G} (hK2 : K * K = 1) (hKN : K ∉ C.N)
    (hKinv : ∀ t : kˣ, K⁻¹ * C.tor t * K = C.tor t⁻¹) (hKT : (K * C.T) ^ 3 = 1) :
    ∃ S : Sylow 2 G, C.J ∈ (S : Subgroup G) ∧ K ∈ (S : Subgroup G) ∧
      C.T ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
  have hT3 := C.T_pow_three
  set K₁ := C.T⁻¹ * K * C.T with hK₁
  have hcomm : K * K₁ = K₁ * K := A4_comm hK2 hT3 hKT
  have hconj : C.T * K * C.T⁻¹ = K * K₁ := A4_conj hK2 hT3 hKT
  have hK₁2 : K₁ * K₁ = 1 := by rw [hK₁, show C.T⁻¹ * K * C.T * (C.T⁻¹ * K * C.T) =
    C.T⁻¹ * (K * K) * C.T by group, hK2]; group
  have hK₁N : K₁ ∉ C.N := by
    intro h; apply hKN
    have : K = C.T * K₁ * C.T⁻¹ := by rw [hK₁]; group
    rw [this]
    exact C.N.mul_mem (C.N.mul_mem C.T_mem_N h) (C.N.inv_mem C.T_mem_N)
  have hKK₁N : K * K₁ ∉ C.N := by
    intro h; apply hKN
    have : K = C.T⁻¹ * (K * K₁) * C.T := by rw [← hconj]; group
    rw [this]
    exact C.N.mul_mem (C.N.mul_mem (C.N.inv_mem C.T_mem_N) h) C.T_mem_N
  have hK1 : K ≠ 1 := fun h => hKN (h ▸ C.N.one_mem)
  have hK₁1 : K₁ ≠ 1 := fun h => hK₁N (h ▸ C.N.one_mem)
  have hKK₁ : K ≠ K₁ := by
    intro h
    apply hK1
    have hc : K * C.T = C.T * K := by
      calc K * C.T = C.T * (C.T⁻¹ * K * C.T) := by group
        _ = C.T * K := by rw [← hK₁, ← h]
    calc K = K ^ 3 * C.T ^ 3 := by
          rw [hT3, mul_one, pow_three', hK2, one_mul]
      _ = (K * C.T) ^ 3 := (Commute.mul_pow hc 3).symm
      _ = 1 := hKT
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions K K₁ hK2 hK₁2 hcomm with hV
  have hVk : IsKleinFour V := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    K K₁ hK2 hK₁2 hK1 hK₁1 hKK₁ hcomm
  have hmemV : ∀ x, x ∈ V ↔ x = K * K₁ ∨ x = K ∨ x = K₁ ∨ x = 1 := fun x => Iff.rfl
  have hJK : K * C.J = C.J * K := C.commute_J_of_inv hKinv
  have hJT := C.J_mul_T
  have hJK₁ : K₁ * C.J = C.J * K₁ := by
    have hTJ : C.T⁻¹ * C.J = C.J * C.T⁻¹ := by
      calc C.T⁻¹ * C.J = C.T⁻¹ * (C.J * C.T) * C.T⁻¹ := by group
        _ = C.T⁻¹ * (C.T * C.J) * C.T⁻¹ := by rw [hJT]
        _ = C.J * C.T⁻¹ := by group
    calc K₁ * C.J = C.T⁻¹ * K * (C.T * C.J) := by rw [hK₁]; group
      _ = C.T⁻¹ * (K * C.J) * C.T := by rw [← hJT]; group
      _ = C.T⁻¹ * C.J * K * C.T := by rw [hJK]; group
      _ = C.J * K₁ := by rw [hTJ, hK₁]; group
  have hcJ : ∀ x ∈ V, ∀ y ∈ Subgroup.zpowers C.J, x * y = y * x := by
    intro x hx y hy
    have hxJ : x * C.J = C.J * x := by
      rcases (hmemV x).mp hx with rfl | rfl | rfl | rfl
      · rw [mul_assoc, hJK₁, ← mul_assoc, hJK, mul_assoc]
      · exact hJK
      · exact hJK₁
      · group
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hxJ m).eq
  have hJV : C.J ∉ V := by
    intro h
    rcases (hmemV _).mp h with h | h | h | h
    · exact hKK₁N (h ▸ C.J_mem_N)
    · exact hKN (h ▸ C.J_mem_N)
    · exact hK₁N (h ▸ C.J_mem_N)
    · exact C.J_ne_one h
  obtain ⟨hcard, hset⟩ := W67.card_sup_mul_card_inf_of_commute V (Subgroup.zpowers C.J) hcJ
  have hinf : V ⊓ Subgroup.zpowers C.J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases JT.mem_zpowers_of_orderOf_eq_two C.orderOf_J |>.mp hx.2 with h | h
    · exact h
    · exact absurd (h ▸ hx.1) hJV
  rw [hinf, Subgroup.card_bot, mul_one, hVk.card_four, Nat.card_zpowers, C.orderOf_J] at hcard
  set S₀ := V ⊔ Subgroup.zpowers C.J with hS₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀p : IsPGroup 2 S₀ := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨S, hS⟩ := hS₀p.exists_le_sylow
  have hSS₀ : (S : Subgroup G) = S₀ :=
    (Subgroup.eq_of_le_of_card_ge hS (by rw [C.h.card_sylow S, hcard])).symm
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hSS₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · rw [hSS₀]; exact Subgroup.mem_sup_left ((hmemV K).mpr (Or.inr (Or.inl rfl)))
  ·
    have hTV : ∀ x ∈ V, C.T * x * C.T⁻¹ ∈ V := by
      intro x hx
      rcases (hmemV x).mp hx with rfl | rfl | rfl | rfl
      · rw [show C.T * (K * K₁) * C.T⁻¹ = (C.T * K * C.T⁻¹) * (C.T * K₁ * C.T⁻¹) by group,
          hconj, show C.T * K₁ * C.T⁻¹ = K by rw [hK₁]; group, mul_assoc, ← hcomm, ← mul_assoc,
          hK2, one_mul]
        exact (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [hconj]; exact (hmemV _).mpr (Or.inl rfl)
      · rw [show C.T * K₁ * C.T⁻¹ = K by rw [hK₁]; group]
        exact (hmemV _).mpr (Or.inr (Or.inl rfl))
      · rw [mul_one, mul_inv_cancel]; exact V.one_mem
    have hTS : ∀ x ∈ S₀, C.T * x * C.T⁻¹ ∈ S₀ := by
      intro x hx
      have hx' : x ∈ ((S₀ : Subgroup G) : Set G) := hx
      rw [hS₀, hset] at hx'
      obtain ⟨v, hv, j, hj, rfl⟩ := hx'
      have hjc : C.T * j * C.T⁻¹ = j := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
        rw [← (Commute.zpow_left (show Commute C.J C.T from hJT) m).eq, mul_inv_cancel_right]
      rw [show C.T * (v * j) * C.T⁻¹ = (C.T * v * C.T⁻¹) * (C.T * j * C.T⁻¹) by group, hjc]
      exact S₀.mul_mem (Subgroup.mem_sup_left (hTV v hv)) (Subgroup.mem_sup_right hj)
    rw [Subgroup.mem_normalizer_iff, hSS₀]
    intro x
    refine ⟨hTS x, fun hx => ?_⟩
    have := hTS _ (hTS _ hx)
    rwa [show C.T * (C.T * (C.T * x * C.T⁻¹) * C.T⁻¹) * C.T⁻¹ =
      C.T * C.T * C.T * x * (C.T * C.T * C.T)⁻¹ by group, ← pow_three', hT3, one_mul, inv_one,
      mul_one] at this

omit [Fintype k] in
theorem exists_c
    (S : Sylow 2 G) (hT : C.T ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∃ c : G, orderOf c = 7 ∧ c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) ∧
      C.T⁻¹ * c * C.T ∈ Subgroup.zpowers c := by
  set NS := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNS
  have hcard : Nat.card NS = 168 := C.card_normalizer_sylow S
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (168 : ℕ).factorization 7 = 1 := by
    rw [show (168 : ℕ) = 7 ^ 1 * 24 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow (by norm_num),
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have h7card : ∀ Q : Sylow 7 NS, Nat.card Q = 7 := by
    intro Q
    rw [Sylow.card_eq_multiplicity, hcard, hfac, pow_one]
  have hn3 : ¬ 3 ∣ Nat.card (Sylow 7 NS) := by
    obtain ⟨Q⟩ : Nonempty (Sylow 7 NS) := inferInstance
    have h1 := card_sylow_modEq_one 7 NS
    have h2 := Q.card_dvd_index
    have hidx : (Q : Subgroup NS).index = 24 := by
      have := Subgroup.card_mul_index (Q : Subgroup NS)
      rw [h7card, hcard] at this
      omega
    rw [hidx] at h2
    intro h3
    have h24 : Nat.card (Sylow 7 NS) ≤ 24 := Nat.le_of_dvd (by norm_num) h2
    unfold Nat.ModEq at h1
    interval_cases hn : Nat.card (Sylow 7 NS) <;> simp_all
  set T' : NS := ⟨C.T, hT⟩
  have hT'p : IsPGroup 3 (Subgroup.zpowers T') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, C.orderOf_T, pow_one])
  have hfix := hT'p.card_modEq_card_fixedPoints (Sylow 7 NS)
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 7 NS, ∀ g : Subgroup.zpowers T', g • Q = Q := by
    by_contra hno
    push Not at hno
    have hempty : Nat.card (MulAction.fixedPoints (Subgroup.zpowers T') (Sylow 7 NS)) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨Q, hQ⟩
      obtain ⟨g, hg⟩ := hno Q
      exact hg (hQ g)
    rw [hempty] at hfix
    exact hn3 (Nat.dvd_of_mod_eq_zero hfix)
  have hTQ : T' ∈ Subgroup.normalizer ((Q : Subgroup NS) : Set NS) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (hQ ⟨T', Subgroup.mem_zpowers T'⟩)
  have hQc : IsCyclic (Q : Subgroup NS) := isCyclic_of_prime_card (h7card Q)
  obtain ⟨⟨c', hc'Q⟩, hgen⟩ := hQc.exists_generator
  have hco : orderOf c' = 7 := by
    rw [← Subgroup.orderOf_mk c' hc'Q, orderOf_eq_card_of_forall_mem_zpowers hgen, h7card]
  refine ⟨c', ?_, c'.2, ?_⟩
  · rw [Subgroup.orderOf_coe, hco]
  · have hmem : T'⁻¹ * c' * T' ∈ (Q : Subgroup NS) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hTQ) c').mp hc'Q
      rwa [inv_inv] at this
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨_, hmem⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have := congrArg (fun x : (Q : Subgroup NS) => ((x : NS) : G)) hn
    simpa using this

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
