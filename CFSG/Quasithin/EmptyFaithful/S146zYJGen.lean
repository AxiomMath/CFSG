module

public import CFSG.Quasithin.Vol2.F134J1Local

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Walter.J1 CFSG.Walter.J1Props CFSG.Quasithin.F134

section Janko

variable {G : Type} [Group G] [Finite G]

theorem janko_not_commute_t_five (h : JankoHyp₀ G) {y s : G} (hy : orderOf y = 5)
    (hs : s * s = 1) (hs1 : s ≠ 1) (hst : s ≠ h.t) (hsc : s * h.t = h.t * s)
    (hyt : y * h.t = h.t * y) (hys : y * s = s * y) : False := by
  have hyF : y ∈ h.F :=
    h.mem_F_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hyt) (by rw [hy]; decide)
  have key : ∃ f ∈ h.F, f * f = 1 ∧ f ≠ 1 ∧ y * f = f * y := by
    rcases h.mem_centralizer_t.mp (Subgroup.mem_centralizer_singleton_iff.mpr hsc) with
      hF | hF
    · exact ⟨s, hF, hs, hs1, hys⟩
    · refine ⟨h.t * s, hF, ?_, ?_, ?_⟩
      · calc h.t * s * (h.t * s) = h.t * (s * h.t) * s := by group
          _ = (h.t * h.t) * (s * s) := by rw [hsc]; group
          _ = 1 := by rw [h.t_mul_t, hs, one_mul]
      · intro he
        apply hst
        calc s = h.t⁻¹ * (h.t * s) := by group
          _ = h.t⁻¹ := by rw [he, mul_one]
          _ = h.t := inv_eq_of_mul_eq_one_left h.t_mul_t
      · calc y * (h.t * s) = (y * h.t) * s := by group
          _ = h.t * (y * s) := by rw [hyt]; group
          _ = h.t * s * y := by rw [hys]; group
  obtain ⟨f, hfF, hf2, hf1, hyf⟩ := key
  have hy1 : y ≠ 1 := fun he => by rw [he, orderOf_one] at hy; omega
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hmem := A5Sub.mem_zpowers_of_commute_five h.iso hyF hfF hy5 hy1 hyf
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hf5 : (y ^ k) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  have hf2' : (y ^ k) ^ 2 = 1 := by rw [sq]; exact hf2
  have hord : orderOf (y ^ k) ∣ Nat.gcd 5 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf5) (orderOf_dvd_of_pow_eq_one hf2')
  rw [show Nat.gcd 5 2 = 1 from rfl, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact hf1 hord

theorem janko_not_commute_four_five (h : JankoHyp₀ G) {y s₁ s₂ : G} (hy : orderOf y = 5)
    (h1 : s₁ * s₁ = 1) (h1' : s₁ ≠ 1) (h2 : s₂ * s₂ = 1) (h2' : s₂ ≠ 1) (h12 : s₁ ≠ s₂)
    (hc : s₁ * s₂ = s₂ * s₁) (hy1 : y * s₁ = s₁ * y) (hy2 : y * s₂ = s₂ * y) : False := by
  have hs₁ : orderOf s₁ = 2 := orderOf_eq_prime (by rw [sq]; exact h1) h1'
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hs₁
  have hy5 : orderOf (g * y * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  refine janko_not_commute_t_five h hy5 (s := g * s₂ * g⁻¹) ?_ ?_ ?_ ?_ ?_ ?_
  · calc g * s₂ * g⁻¹ * (g * s₂ * g⁻¹) = g * (s₂ * s₂) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · intro he
    apply h2'
    calc s₂ = g⁻¹ * (g * s₂ * g⁻¹) * g := by group
      _ = 1 := by rw [he]; group
  · intro he
    apply h12
    calc s₁ = g⁻¹ * (g * s₁ * g⁻¹) * g := by group
      _ = g⁻¹ * (g * s₂ * g⁻¹) * g := by rw [hg, he]
      _ = s₂ := by group
  · rw [← hg]
    exact conj_commute g s₂ s₁ hc.symm
  · rw [← hg]
    exact conj_commute g y s₁ hy1
  · exact conj_commute g y s₂ hy2

end Janko

section Order

variable {G : Type} [Group G]

theorem card_eq_40 {B U : Subgroup G} {y : G} (hG : Nat.card G = 175560) (hUc : Nat.card U = 8)
    (hUB : U ≤ B) (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) (hyB : y ∈ B)
    (hy : orderOf y = 5) : Nat.card B = 40 := by
  have hdvd : Nat.card B ∣ 40 * 4389 := by
    rw [show 40 * 4389 = 175560 by norm_num, ← hG]
    exact Subgroup.card_subgroup_dvd_card B
  have hcop : Nat.Coprime (Nat.card B) 4389 := Nat.coprime_of_dvd fun k hk hkB hk4 => by
    rcases hB k hk hkB with rfl | rfl <;> norm_num at hk4
  have h40 : Nat.card B ∣ 40 := hcop.dvd_of_dvd_mul_right hdvd
  have h8 : 8 ∣ Nat.card B := hUc ▸ Subgroup.card_dvd_of_le hUB
  have h5 : 5 ∣ Nat.card B := hy ▸ Subgroup.orderOf_dvd_natCard B hyB
  have : 40 ∣ Nat.card B := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h5
  exact Nat.dvd_antisymm h40 this

theorem conj_mem_zpowers_of_card_forty {B : Subgroup G} {y : G} (hB : Nat.card B = 40)
    (hyB : y ∈ B) (hy : orderOf y = 5) : ∀ b ∈ B, b * y * b⁻¹ ∈ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  set y' : B := ⟨y, hyB⟩ with hy'
  have hy'o : orderOf y' = 5 := by rw [hy', Subgroup.orderOf_mk, hy]
  have hcard : Nat.card (Subgroup.zpowers y') = 5 := by rw [Nat.card_zpowers, hy'o]
  have hP : IsPGroup 5 (Subgroup.zpowers y') :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  have hidx : (Subgroup.zpowers y').index = 8 := by
    have h1 := (Subgroup.zpowers y').card_mul_index
    rw [hcard, hB] at h1
    omega
  have hnd : ¬ 5 ∣ (Subgroup.zpowers y').index := by rw [hidx]; norm_num
  let P : Sylow 5 B := hP.toSylow hnd
  have hn : Nat.card (Sylow 5 B) = 1 := by
    have h1 : Nat.card (Sylow 5 B) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 B
    have h2 : Nat.card (Sylow 5 B) ∣ 8 := by
      have := P.card_dvd_index
      rwa [show (P : Subgroup B).index = 8 from hidx] at this
    obtain ⟨n, hn⟩ : ∃ n, n = Nat.card (Sylow 5 B) := ⟨_, rfl⟩
    rw [← hn] at h1 h2 ⊢
    have h3 : n ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    unfold Nat.ModEq at h1
    interval_cases n <;> omega
  have : Subsingleton (Sylow 5 B) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hN : (P : Subgroup B).Normal := Sylow.normal_of_subsingleton P
  intro b hb
  have hmem : (⟨b, hb⟩ : B) * y' * (⟨b, hb⟩ : B)⁻¹ ∈ Subgroup.zpowers y' :=
    hN.conj_mem y' (Subgroup.mem_zpowers y') ⟨b, hb⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem conj_eq_or_inv_of_orderOf_five {y u : G} (hy : orderOf y = 5) (hu : u * u = 1)
    (hmem : u * y * u⁻¹ ∈ Subgroup.zpowers y) : u * y * u⁻¹ = y ∨ u * y * u⁻¹ = y⁻¹ := by
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  obtain ⟨j, hj, hjy⟩ : ∃ j : ℕ, j < 5 ∧ y ^ j = u * y * u⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hmod : y ^ (k % 5) = y ^ k := by
      have := zpow_mod_orderOf y k
      rwa [hy] at this
    have hk0 : 0 ≤ k % 5 := Int.emod_nonneg _ (by norm_num)
    have hk5 : k % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
    refine ⟨(k % 5).toNat, by omega, ?_⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg hk0, hmod, hk]
  have hsq : y ^ (j * j) = y ^ 1 := by
    calc y ^ (j * j) = (y ^ j) ^ j := pow_mul y j j
      _ = (u * y * u⁻¹) ^ j := by rw [hjy]
      _ = u * y ^ j * u⁻¹ := conj_pow
      _ = u * (u * y * u⁻¹) * u⁻¹ := by rw [hjy]
      _ = y ^ 1 := by
        rw [pow_one, hui]
        calc u * (u * y * u) * u = (u * u) * y * (u * u) := by simp only [mul_assoc]
          _ = y := by rw [hu, one_mul, mul_one]
  have hmodeq := (pow_eq_pow_iff_modEq).1 hsq
  rw [hy] at hmodeq
  unfold Nat.ModEq at hmodeq
  interval_cases j
  · omega
  · left
    rw [pow_one] at hjy
    exact hjy.symm
  · omega
  · omega
  · right
    rw [← hjy]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy5)

theorem card_le_two_mul_of_mul_mem {H K : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ K, a ∉ H → b ∉ H → a * b ∈ H) :
    Nat.card K ≤ 2 * Nat.card (H ⊓ K : Subgroup G) := by
  have hmul := Subgroup.relIndex_mul_card H K
  have hle : H.relIndex K ≤ 2 := by
    by_cases hKH : K ≤ H
    · rw [(Subgroup.relIndex_eq_one).2 hKH]
      norm_num
    · obtain ⟨a, haK, haH⟩ := IsConcreteLE.not_le_iff_exists.1 hKH
      refine (Subgroup.relIndex_eq_two_iff.2 ⟨a, haK, fun b hb => ?_⟩).le
      by_cases hbH : b ∈ H
      · refine Or.inr ⟨hbH, fun hba => haH ?_⟩
        have := H.mul_mem (H.inv_mem hbH) hba
        simpa using this
      · exact Or.inl ⟨h b hb a haK hbH haH, hbH⟩
  calc Nat.card K = H.relIndex K * Nat.card (H ⊓ K : Subgroup G) := hmul.symm
    _ ≤ 2 * Nat.card (H ⊓ K : Subgroup G) := Nat.mul_le_mul_right _ hle

end Order

section Main

variable {G : Type} [Group G] [Finite G]

theorem janko_no_five (h : JankoHyp₀ G) (hG : Nat.card G = 175560) {U B : Subgroup G} {y : G}
    (hU : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index) (hUB : U ≤ B)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) (hyB : y ∈ B)
    (hy : orderOf y = 5) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUc : Nat.card U = 8 := h.card_sylow (hU.toSylow hUi)
  have hB40 : Nat.card B = 40 := card_eq_40 hG hUc hUB hB hyB hy
  have hnorm := conj_mem_zpowers_of_card_forty hB40 hyB hy
  have hsq : ∀ v ∈ U, v * v = 1 := fun v hv => janko_mul_self_of_sylow h (hU.toSylow hUi) hv
  have hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have := h.abelian_sylow (hU.toSylow hUi)
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hdich : ∀ u ∈ U, u * y * u⁻¹ = y ∨ u * y * u⁻¹ = y⁻¹ := fun u hu =>
    conj_eq_or_inv_of_orderOf_five hy (hsq u hu) (hnorm u (hUB hu))
  have hinv : ∀ a ∈ U, a ∉ Subgroup.centralizer ({y} : Set G) → a * y * a⁻¹ = y⁻¹ := by
    intro a ha haC
    refine (hdich a ha).resolve_left fun he => haC ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hmulmem : ∀ a ∈ U, ∀ b ∈ U, a ∉ Subgroup.centralizer ({y} : Set G) →
      b ∉ Subgroup.centralizer ({y} : Set G) → a * b ∈ Subgroup.centralizer ({y} : Set G) := by
    intro a ha b hb haC hbC
    have hai := hinv a ha haC
    have hbi := hinv b hb hbC
    have h1 : a * y⁻¹ * a⁻¹ = y := by
      rw [show a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ by group, hai, inv_inv]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * b * y = a * (b * y * b⁻¹) * b := by group
      _ = a * y⁻¹ * b := by rw [hbi]
      _ = (a * y⁻¹ * a⁻¹) * (a * b) := by group
      _ = y * (a * b) := by rw [h1]
  set V : Subgroup G := Subgroup.centralizer ({y} : Set G) ⊓ U with hV
  have hV4 : 4 ≤ Nat.card V := by
    have h2 : Nat.card U ≤ 2 * Nat.card V := card_le_two_mul_of_mul_mem hmulmem
    omega
  obtain ⟨s₁, hs₁V, hs₁⟩ : ∃ s₁ ∈ V, s₁ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hall
    rw [this, Subgroup.card_bot] at hV4
    omega
  have hz : Subgroup.zpowers s₁ < V := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hs₁V) fun he => ?_
    have hc := Nat.card_zpowers s₁
    rw [he] at hc
    have h2 : orderOf s₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq s₁ hs₁V.2)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨s₂, hs₂V, hs₂⟩ := IsConcreteLE.exists_of_lt hz
  have hs₂1 : s₂ ≠ 1 := fun he => hs₂ (he ▸ Subgroup.one_mem _)
  have hs₁₂ : s₁ ≠ s₂ := fun he => hs₂ (he ▸ Subgroup.mem_zpowers _)
  exact janko_not_commute_four_five h hy (hsq s₁ hs₁V.2) hs₁ (hsq s₂ hs₂V.2) hs₂1 hs₁₂
    (hab s₁ hs₁V.2 s₂ hs₂V.2) (Subgroup.mem_centralizer_singleton_iff.mp hs₁V.1).symm
    (Subgroup.mem_centralizer_singleton_iff.mp hs₂V.1).symm

end Main

end CFSG.Quasithin.S146zY
