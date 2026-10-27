module

public import CFSG.RankThree.PartOne.N143.GroupLemmas

public section

namespace CFSG.RankThree.PartOne.N143

open scoped Pointwise

section Sup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_zpowers_of_normalizer {Y : Subgroup G} {z : G} (hz3 : z ^ 3 = 1) (hzY : z ∉ Y)
    (hzN : z ∈ Subgroup.normalizer (Y : Set G)) :
    Nat.card (Subgroup.zpowers z ⊔ Y : Subgroup G) = 3 * Nat.card Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (Y : Set G) := (Subgroup.zpowers_le).2 hzN
  have hz1 : z ≠ 1 := fun h => hzY (h ▸ Y.one_mem)
  have hK3 : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  have hbot : Y.subgroupOf (Subgroup.zpowers z) = ⊥ := by
    have : Fact (Nat.card (Subgroup.zpowers z)).Prime := ⟨by rw [hK3]; exact Nat.prime_three⟩
    rcases (Y.subgroupOf (Subgroup.zpowers z)).eq_bot_or_eq_top_of_prime_card with h | h
    · exact h
    · exfalso
      apply hzY
      have : (⟨z, Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z) ∈ Y.subgroupOf (Subgroup.zpowers z) := by
        rw [h]
        trivial
      exact this
  have : (Y.subgroupOf (Subgroup.zpowers z)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hle
  have : (Y.subgroupOf (Subgroup.zpowers z ⊔ Y)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  have hc1 := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers z) Y hle).toEquiv
  have hKq : Nat.card (Subgroup.zpowers z ⧸ Y.subgroupOf (Subgroup.zpowers z)) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf (Subgroup.zpowers z))
    have h1 : Nat.card (Y.subgroupOf (Subgroup.zpowers z)) = 1 := by
      rw [hbot]
      simp
    rw [hK3, h1, mul_one] at h
    exact h.symm
  have hH := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Y.subgroupOf (Subgroup.zpowers z ⊔ Y))
  rw [← hc1, hKq, card_subgroupOf_of_le le_sup_right] at hH
  exact hH

theorem exists_commuting_of_normalizing {Y : Subgroup G} {z : G} (hz3 : z ^ 3 = 1) (hzY : z ∉ Y)
    (hzN : z ∈ Subgroup.normalizer (Y : Set G)) (hY3 : (Nat.card Y).factorization 3 = 1) :
    ∃ x ∈ Y, orderOf x = 3 ∧ x * z = z * x := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (Y : Set G) := (Subgroup.zpowers_le).2 hzN
  have hz1 : z ≠ 1 := fun h => hzY (h ▸ Y.one_mem)
  have hK3 : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz3 hz1
  set H : Subgroup G := Subgroup.zpowers z ⊔ Y with hH
  have hHcard : Nat.card H = 3 * Nat.card Y := card_sup_zpowers_of_normalizer hz3 hzY hzN
  have hYpos : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hH3 : (Nat.card H).factorization 3 = 2 := by
    rw [hHcard, Nat.factorization_mul (by norm_num) hYpos]
    simp [hY3, Nat.Prime.factorization_self Nat.prime_three]
  have hzH : z ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hYH : Y ≤ H := le_sup_right
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  have hKH : Subgroup.zpowers z' = (Subgroup.zpowers z).subgroupOf H := by
    ext w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa [hz'] using congrArg Subtype.val hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext (by simpa [hz'] using hi)⟩
  have hKpg : IsPGroup 3 (Subgroup.zpowers z') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers]
    have : orderOf z' = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hz3 hz1
    simpa using this
  obtain ⟨S, hS⟩ := hKpg.exists_le_sylow
  have hScard : Nat.card S = 9 := by
    rw [Sylow.card_eq_multiplicity, hH3]
    norm_num
  have : (Y.subgroupOf H).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  let π : ↥H →* ↥H ⧸ Y.subgroupOf H := QuotientGroup.mk' (Y.subgroupOf H)
  have hq3 : Nat.card (↥H ⧸ Y.subgroupOf H) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf H)
    rw [card_subgroupOf_of_le hYH, hHcard] at h
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have : 3 * Nat.card Y = Nat.card (↥H ⧸ Y.subgroupOf H) * Nat.card Y := h
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  have hmap := card_eq_map_mul_inf_ker π (S : Subgroup ↥H)
  have hker : π.ker = Y.subgroupOf H := QuotientGroup.ker_mk' _
  rw [hker, hScard] at hmap
  have hmap_le : Nat.card ((S : Subgroup ↥H).map π) ≤ 3 :=
    (Subgroup.card_le_card_group _).trans hq3.le
  set T : Subgroup ↥H := (S : Subgroup ↥H) ⊓ Y.subgroupOf H with hT
  have hT_ge : 3 ≤ Nat.card T := by
    by_contra hlt
    have : Nat.card T ≤ 2 := by omega
    have h2 : Nat.card ((S : Subgroup ↥H).map π) * Nat.card T ≤ 3 * 2 :=
      Nat.mul_le_mul hmap_le this
    omega
  have hTdvdS : Nat.card T ∣ 9 := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hTdvdY : Nat.card T ∣ Nat.card Y := by
    rw [← card_subgroupOf_of_le hYH]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hT3 : Nat.card T = 3 := by
    have h9 : ¬ 9 ∣ Nat.card Y := by
      intro h
      have : 3 ^ 2 ∣ Nat.card Y := by simpa using h
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hYpos).1 this
      omega
    obtain ⟨i, hi, hTi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show Nat.card T ∣ 3 ^ 2 by simpa using hTdvdS)
    interval_cases i
    · exfalso
      rw [pow_zero] at hTi
      omega
    · rw [hTi]
      norm_num
    · exfalso
      apply h9
      have : Nat.card T = 9 := by rw [hTi]; norm_num
      rw [this] at hTdvdY
      exact hTdvdY
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 (by rw [hT3])
  have hx'S : (x' : ↥H) ∈ (S : Subgroup ↥H) := (x'.2).1
  have hx'Y : (x' : ↥H) ∈ Y.subgroupOf H := (x'.2).2
  have hz'S : z' ∈ (S : Subgroup ↥H) := hS (Subgroup.mem_zpowers z')
  have hcomm : IsMulCommutative ↥(S : Subgroup ↥H) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := ↥(S : Subgroup ↥H)) (p := 3)
      (by rw [hScard]; norm_num)
  have hcom := hcomm.is_comm.comm (⟨(x' : ↥H), hx'S⟩ : ↥S) ⟨z', hz'S⟩
  have hcom' : (x' : ↥H) * z' = z' * (x' : ↥H) := congrArg Subtype.val hcom
  refine ⟨((x' : ↥H) : G), hx'Y, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hx'
  · exact congrArg Subtype.val hcom'

end Sup

theorem three_pow_pred_dvd_sub_one {a r : ℕ} (hr : 1 ≤ r) (h : 3 ^ a ∣ r ^ 3 - 1) :
    3 ^ (a - 1) ∣ r - 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  by_cases hr1 : r = 1
  · subst hr1
    simp
  have hr2 : 2 ≤ r := by omega
  have h3 : 3 ∣ r ^ 3 - 1 := (dvd_pow_self 3 ha.ne').trans h
  have hmod : r % 3 = 1 := by
    have h1 : r ^ 3 % 3 = 1 := by
      have : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ hr
      omega
    have h2 : r ^ 3 % 3 = (r % 3) ^ 3 % 3 := Nat.pow_mod r 3 3
    have hlt : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : r % 3 <;> simp_all
  have hxy : 3 ∣ r - 1 := by omega
  have hx : ¬ 3 ∣ r := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlte := padicValNat.pow_sub_pow (p := 3) (x := r) (y := 1) (by decide) (by omega) hxy hx
    (n := 3) (by norm_num)
  rw [one_pow] at hlte
  have hne : r ^ 3 - 1 ≠ 0 := by
    have : 1 < r ^ 3 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hne' : r - 1 ≠ 0 := by omega
  have h1 := (padicValNat_dvd_iff_le (p := 3) hne).1 h
  have h33 : padicValNat 3 3 = 1 := padicValNat_self
  rw [hlte, h33] at h1
  exact (padicValNat_dvd_iff_le (p := 3) hne').2 (by omega)

section Cyclic

variable {G : Type*} [Group G]

theorem cyclic3_commutator_cube [Finite G] {U : Subgroup G} [IsCyclic U] {a : ℕ}
    (hU : Nat.card U = 3 ^ a) {z : G} (hz3 : z ^ 3 = 1)
    (hzN : z ∈ Subgroup.normalizer (U : Set G)) : ∀ g ∈ U, (z * g * z⁻¹ * g⁻¹) ^ 3 = 1 := by
  classical
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  let σ : MulAut U := U.normalizerMonoidHom ⟨z, hzN⟩
  have hσ : ∀ g : U, ((σ g : U) : G) = z * g * z⁻¹ := fun g => rfl
  by_cases hu1 : u = 1
  · intro g hg
    have : (⟨g, hg⟩ : U) ∈ Subgroup.zpowers u := hu _
    rw [hu1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    have hg1 : g = 1 := congrArg Subtype.val this
    subst hg1
    simp
  obtain ⟨r, hr⟩ : ∃ r : ℕ, σ u = u ^ r := by
    have : σ u ∈ Subgroup.zpowers u := hu (σ u)
    rw [← mem_powers_iff_mem_zpowers] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, hr.symm⟩
  have hσall : ∀ g : U, σ g = g ^ r := by
    intro g
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hu g)
    rw [map_zpow, hr, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hσ3 : σ ^ 3 = 1 := by
    have : (⟨z, hzN⟩ : Subgroup.normalizer (U : Set G)) ^ 3 = 1 := Subtype.ext hz3
    show U.normalizerMonoidHom ⟨z, hzN⟩ ^ 3 = 1
    rw [← map_pow, this, map_one]
  have hu3 : u ^ (r ^ 3) = u := by
    have := pow_apply_of_apply hσall 3 u
    rw [hσ3, MulAut.one_apply] at this
    exact this.symm
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exfalso
      apply hu1
      simpa using hu3.symm
    · exact h
  have hord : orderOf u = 3 ^ a := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu]
    exact hU
  have hupow : u ^ (r ^ 3 - 1) = 1 := by
    have h1 : u ^ (r ^ 3 - 1) * u = 1 * u := by
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hr1)]
      exact hu3
    exact (mul_left_inj u).1 h1
  have hdvd : 3 ^ a ∣ r ^ 3 - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hupow
  have hdvd3 : 3 ^ a ∣ 3 * (r - 1) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h1 := three_pow_pred_dvd_sub_one hr1 hdvd
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [pow_succ, mul_comm]
      exact mul_dvd_mul_left 3 (by simpa using h1)
  intro g hg
  have hconj : z * g * z⁻¹ = g ^ r := by
    have h1 : ((σ ⟨g, hg⟩ : U) : G) = z * g * z⁻¹ := hσ ⟨g, hg⟩
    have h2 := congrArg Subtype.val (hσall ⟨g, hg⟩)
    rw [← h1]
    simpa using h2
  have hcomm : z * g * z⁻¹ * g⁻¹ = g ^ (r - 1) := by
    rw [hconj]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp [pow_succ]
  rw [hcomm, ← pow_mul, mul_comm]
  obtain ⟨m, hm⟩ := hdvd3
  have hg3 : g ^ (3 ^ a) = 1 := by
    have h1 : (⟨g, hg⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
    have h2 : g ^ Nat.card U = 1 := congrArg Subtype.val h1
    rwa [hU] at h2
  rw [hm, pow_mul, hg3, one_pow]

end Cyclic

section Bound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem three_subgroup_card_le_of_centralizer (R : Subgroup G) [CFSG.IsElementaryAbelian 3 R]
    (hR : Nat.card R = 9) {b : ℕ}
    (hC : (Nat.card (Subgroup.centralizer (R : Set G))).factorization 3 ≤ b) (S : Subgroup G)
    (hSN : S ≤ Subgroup.normalizer (R : Set G)) (hS3 : IsPGroup 3 S) :
    Nat.card S ≤ 3 ^ (b + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : ↥S →* MulAut R := R.normalizerMonoidHom.comp (Subgroup.inclusion hSN)
  have h1 := card_le_three_mul_ker R hR hS3 ρ
  have hkerS : IsPGroup 3 ρ.ker := hS3.to_subgroup ρ.ker
  obtain ⟨m, hm⟩ := hkerS.exists_card_eq
  have hle : ρ.ker.map S.subtype ≤ Subgroup.centralizer (R : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h2 : ρ k = 1 := hk
    have h3 := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : G)) h2
    have e1 : ((ρ k ⟨r, hr⟩ : R) : G) = (k : G) * r * (k : G)⁻¹ := rfl
    simp only [e1, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hdvd : 3 ^ m ∣ Nat.card (Subgroup.centralizer (R : Set G)) := by
    rw [← hm, ← Subgroup.card_map_of_injective S.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hCne : Nat.card (Subgroup.centralizer (R : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hmb : m ≤ b :=
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hCne).1 hdvd).trans hC
  calc Nat.card S ≤ 3 * Nat.card ρ.ker := h1
    _ = 3 * 3 ^ m := by rw [hm]
    _ ≤ 3 * 3 ^ b := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hmb)
    _ = 3 ^ (b + 1) := by ring

end Bound

section SylowContra

variable {G : Type} [Group G] [Finite G]

theorem sylow_contra {N M P U : Subgroup G} {n : ℕ}
    (hbound : ∀ S : Subgroup G, S ≤ N → IsPGroup 3 S → Nat.card S ≤ 3 ^ n)
    (hMN : M ≤ N) (hMcard : Nat.card M = 3 ^ n) (hPN : P ≤ N) (hPcard : Nat.card P = 27)
    (hPexp : ∀ y ∈ P, y ^ 3 = 1) (hU : IsCyclic U) (hUM : U ≤ M)
    (hUcard : 3 * Nat.card U = Nat.card M) (hUn : ∀ m ∈ M, ∀ u ∈ U, m * u * m⁻¹ ∈ U) : False := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMpg : IsPGroup 3 (M.subgroupOf N) :=
    IsPGroup.of_card (n := n) (by rw [card_subgroupOf_of_le hMN, hMcard])
  have hPpg : IsPGroup 3 (P.subgroupOf N) :=
    IsPGroup.of_card (n := 3) (by rw [card_subgroupOf_of_le hPN, hPcard]; norm_num)
  obtain ⟨SM, hSM⟩ := hMpg.exists_le_sylow
  obtain ⟨SP, hSP⟩ := hPpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) SM SP
  have hSMle : Nat.card (SM : Subgroup ↥N) ≤ 3 ^ n := by
    have h1 : Nat.card ((SM : Subgroup ↥N).map N.subtype) ≤ 3 ^ n := by
      refine hbound _ ?_ (SM.isPGroup'.map N.subtype)
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    rwa [Subgroup.card_map_of_injective N.subtype_injective] at h1
  have hMSM : M.subgroupOf N = (SM : Subgroup ↥N) := by
    refine Subgroup.eq_of_le_of_card_ge hSM ?_
    rw [card_subgroupOf_of_le hMN, hMcard]
    exact hSMle
  have hconj : ∀ y : ↥N, y ∈ (SP : Subgroup ↥N) → g⁻¹ * y * g ∈ (SM : Subgroup ↥N) := by
    intro y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa [MulAut.smul_def, Subgroup.smul_def] using hy
  have hPM : ∀ y ∈ P, ((g : G))⁻¹ * y * (g : G) ∈ M := by
    intro y hy
    have h1 : (⟨y, hPN hy⟩ : ↥N) ∈ (SP : Subgroup ↥N) :=
      hSP (by rw [Subgroup.mem_subgroupOf]; exact hy)
    have h2 := hconj _ h1
    rw [← hMSM, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  set P' : Subgroup G := P.map (MulAut.conj ((g : G))⁻¹).toMonoidHom with hP'
  have hP'M : P' ≤ M := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hPM y hy
  have hP'card : Nat.card P' = 27 := by
    rw [hP', Subgroup.card_map_of_injective (MulAut.conj ((g : G))⁻¹).injective, hPcard]
  have hP'exp : ∀ w ∈ P', w ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    show ((g : G)⁻¹ * y * (g : G)⁻¹⁻¹) ^ 3 = 1
    rw [conj_pow, hPexp y hy, mul_one, mul_inv_cancel]
  have hUnorm : (U.subgroupOf M).Normal :=
    ⟨fun u hu m => by
      rw [Subgroup.mem_subgroupOf] at hu ⊢
      exact hUn m m.2 u hu⟩
  let f : ↥P' →* ↥M ⧸ U.subgroupOf M :=
    (QuotientGroup.mk' (U.subgroupOf M)).comp (Subgroup.inclusion hP'M)
  have hqcard : Nat.card (↥M ⧸ U.subgroupOf M) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (U.subgroupOf M)
    rw [card_subgroupOf_of_le hUM] at h
    have hpos : 0 < Nat.card U := Nat.card_pos
    have : 3 * Nat.card U = Nat.card (↥M ⧸ U.subgroupOf M) * Nat.card U := by
      rw [hUcard]
      exact h
    exact (Nat.eq_of_mul_eq_mul_right hpos this).symm
  have hker := card_eq_range_mul_ker f
  have hrange : Nat.card f.range ≤ 3 := (Subgroup.card_le_card_group _).trans hqcard.le
  rw [hP'card] at hker
  have hkerge : 9 ≤ Nat.card f.ker := by
    by_contra hlt
    have h8 : Nat.card f.ker ≤ 8 := by omega
    have := Nat.mul_le_mul hrange h8
    omega
  have hKU : f.ker.map P'.subtype ≤ U := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : f k = 1 := hk
    have h2 : (Subgroup.inclusion hP'M k : ↥M) ∈ U.subgroupOf M := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    exact h2
  have : IsCyclic ↥(f.ker.map P'.subtype) :=
    isCyclic_of_injective (Subgroup.inclusion hKU) (Subgroup.inclusion_injective hKU)
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(f.ker.map P'.subtype))
  have hKcard : Nat.card (f.ker.map P'.subtype) = Nat.card f.ker :=
    Subgroup.card_map_of_injective P'.subtype_injective
  have hy3 : y ^ 3 = 1 := Subtype.ext (hP'exp _ (Subgroup.map_subtype_le _ y.2))
  have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  have : orderOf y ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

end SylowContra

end CFSG.RankThree.PartOne.N143
