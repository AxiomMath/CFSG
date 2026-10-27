module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off11
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3AutWrap

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin

theorem klein_gen {G : Type*} [Group G] [Finite G] {N : Subgroup G} (hN : IsKleinFour ↥N)
    {a b : G} (ha : a ∈ N) (hb : b ∈ N) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Subgroup.closure ({a, b} : Set G) = N := by
  set M := Subgroup.closure ({a, b} : Set G) with hM
  have hMN : M ≤ N := (Subgroup.closure_le _).2 (by
    rintro y (rfl | rfl)
    exacts [ha, hb])
  have haM : a ∈ M := Subgroup.subset_closure (by simp)
  have hbM : b ∈ M := Subgroup.subset_closure (by simp)
  refine Subgroup.eq_of_le_of_card_ge hMN ?_
  have h4 := hN.card_four
  have hdvd : Nat.card M ∣ 2 ^ 2 := by
    have := Subgroup.card_dvd_of_le hMN
    rwa [h4, show (4 : ℕ) = 2 ^ 2 by norm_num] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k
  · exfalso
    have : M = ⊥ := Subgroup.card_eq_one.1 (by simpa using hk')
    exact ha1 (Subgroup.mem_bot.1 (this ▸ haM))
  · exfalso
    have h2 : Nat.card M = 2 := by simpa using hk'
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥M)).1 h2
    have e1 : (⟨a, haM⟩ : ↥M) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
    have e2 : (⟨b, hbM⟩ : ↥M) = y := huniq _ (fun h => hb1 (congrArg Subtype.val h))
    exact hab (congrArg Subtype.val (e1.trans e2.symm))
  · rw [h4, hk']
    norm_num

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.s4Data (h : Hyp3 H S x) : S4Data S x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htS, htQ, ht2, htc, n₁, hn₁, hmove⟩ := h.exists_t
  have hNn : (nQ H x).Normal := h.sig.nQ_normal h.ord
  have hN4 : Nat.card (nQ H x) = 4 := h.offender.1
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : H, n₂ = t * n₁ * t⁻¹ := ⟨_, rfl⟩
  have hn₂N : n₂ ∈ nQ H x := hn₂ ▸ hNn.conj_mem n₁ hn₁ t
  have hsq : ∀ y ∈ nQ H x, y * y = 1 := fun y hy => (mem_oneCenter.1 (nQ_le x hy)).2.1
  have hcomm : ∀ y ∈ nQ H x, ∀ z ∈ nQ H x, y * z = z * y := fun y hy z hz =>
    elem_comm (nQ_elem x) hy hz
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hn₁inv : n₁⁻¹ = n₁ := inv_eq_of_mul_eq_one_right (hsq n₁ hn₁)
  have hn₁1 : n₁ ≠ 1 := by
    intro h1
    apply hmove
    rw [h1]
    group
  have hn₂1 : n₂ ≠ 1 := by
    intro h1
    apply hn₁1
    have h3 : t * n₁ * t⁻¹ = 1 := hn₂ ▸ h1
    calc n₁ = t⁻¹ * (t * n₁ * t⁻¹) * t := by group
      _ = 1 := by rw [h3]; group
  have hn₁₂ : n₁ ≠ n₂ := fun h12 => hmove (by rw [← hn₂]; exact h12.symm)
  have hρ2 : (n₁ * t) ^ 2 = n₁ * n₂ := by
    calc (n₁ * t) ^ 2 = n₁ * (t * n₁ * t⁻¹) * (t * t) := by rw [pow_two]; group
      _ = n₁ * n₂ := by rw [ht2, mul_one, hn₂]
  have hρ4 : (n₁ * t) ^ 4 = 1 := by
    calc (n₁ * t) ^ 4 = ((n₁ * t) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (n₁ * n₂) * (n₁ * n₂) := by rw [hρ2, pow_two]
      _ = (n₁ * n₁) * (n₂ * n₂) := by
        calc (n₁ * n₂) * (n₁ * n₂) = n₁ * (n₂ * n₁) * n₂ := by group
          _ = n₁ * (n₁ * n₂) * n₂ := by rw [hcomm n₂ hn₂N n₁ hn₁]
          _ = (n₁ * n₁) * (n₂ * n₂) := by group
      _ = 1 := by rw [hsq n₁ hn₁, hsq n₂ hn₂N, one_mul]
  have hρ2' : (n₁ * t) ^ 2 ≠ 1 := by
    rw [hρ2]
    intro h1
    apply hn₁₂
    have : n₂ = n₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hn₁inv]
  have hord : orderOf (n₁ * t) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hρ2') (by simpa using hρ4)
    simpa using this
  have hrel : t * (n₁ * t) * t⁻¹ = (n₁ * t)⁻¹ := by
    calc t * (n₁ * t) * t⁻¹ = t * n₁ := by group
      _ = t⁻¹ * n₁⁻¹ := by rw [htinv, hn₁inv]
      _ = (n₁ * t)⁻¹ := (mul_inv_rev _ _).symm
  have hρ3 : (n₁ * t) ^ 3 = n₂ * t := by
    calc (n₁ * t) ^ 3 = (n₁ * t) ^ 2 * (n₁ * t) := pow_succ _ _
      _ = (n₁ * n₂) * (n₁ * t) := by rw [hρ2]
      _ = (n₂ * n₁) * (n₁ * t) := by rw [hcomm n₁ hn₁ n₂ hn₂N]
      _ = n₂ * (n₁ * n₁) * t := by group
      _ = n₂ * t := by rw [hsq n₁ hn₁, mul_one]
  have hnot : t ∉ Subgroup.zpowers (n₁ * t) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : (n₁ * t) ^ (k % 4) = t := by
      have := zpow_mod_orderOf (n₁ * t) k
      rw [hord] at this
      rw [show ((4 : ℕ) : ℤ) = 4 by norm_num] at this
      rw [this, hk]
    have hcases : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hcases with e | e | e | e
    · rw [e, zpow_zero] at hk'
      exact htQ (hk' ▸ (oQ H).one_mem)
    · rw [e, zpow_one] at hk'
      apply hn₁1
      exact mul_right_cancel (hk'.trans (one_mul t).symm)
    · rw [e, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hρ2] at hk'
      exact htQ (hk' ▸ (oQ H).mul_mem (oneCenter_le (nQ_le x hn₁))
        (oneCenter_le (nQ_le x hn₂N)))
    · rw [e, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hρ3] at hk'
      apply hn₂1
      exact mul_right_cancel (hk'.trans (one_mul t).symm)
  obtain ⟨eD⟩ := CFSG.LieType.SteinbergBR.AutGL32.nonempty_closure_pair_mulEquiv_dihedralGroup
    (ρ := n₁ * t) (σ := t) (by rw [pow_two]; exact ht2) hrel hnot
  rw [hord] at eD
  set D : Subgroup H := Subgroup.closure ({n₁ * t, t} : Set H) with hD
  have htD : t ∈ D := Subgroup.subset_closure (by simp)
  have hρD : n₁ * t ∈ D := Subgroup.subset_closure (by simp)
  have hn₁D : n₁ ∈ D := by
    have := D.mul_mem hρD (D.inv_mem htD)
    simpa using this
  have hn₂D : n₂ ∈ D := by
    rw [hn₂]
    exact D.mul_mem (D.mul_mem htD hn₁D) (D.inv_mem htD)
  have hND : nQ H x ≤ D := by
    rw [← klein_gen h.isKleinFour_nQ hn₁ hn₂N hn₁1 hn₂1 hn₁₂]
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | rfl)
    exacts [hn₁D, hn₂D]
  have hDS : D ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | rfl)
    exacts [S.mul_mem (nQ_le_S h.sig hn₁) htS, htS]
  have hDc : ∀ d ∈ D, ∀ q ∈ q0Sub H x, d * q = q * d := by
    intro d hd q hq
    have hDle : D ≤ Subgroup.centralizer {q} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro y (rfl | rfl)
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc n₁ * t * q = n₁ * (t * q) := mul_assoc _ _ _
          _ = n₁ * (q * t) := by rw [htc q hq]
          _ = (n₁ * q) * t := (mul_assoc _ _ _).symm
          _ = (q * n₁) * t := by rw [nQ_q0_comm hn₁ hq]
          _ = q * (n₁ * t) := mul_assoc _ _ _
      · exact Subgroup.mem_centralizer_singleton_iff.2 (htc q hq)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hDle hd)
  have hcardD : Nat.card D = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hDQ : D ⊓ oQ H = nQ H x := by
    have hle : nQ H x ≤ D ⊓ oQ H := le_inf hND ((nQ_le x).trans oneCenter_le)
    have hcard : Nat.card ↥(D ⊓ oQ H) ∣ 2 ^ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ oQ H ≤ D)
      rwa [hcardD, show (8 : ℕ) = 2 ^ 3 by norm_num] at this
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hcard
    have hge : 4 ≤ Nat.card ↥(D ⊓ oQ H) := hN4 ▸ Subgroup.card_le_of_le hle
    interval_cases k
    · rw [pow_zero] at hk'
      omega
    · rw [pow_one] at hk'
      omega
    · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk', hN4]; norm_num)).symm
    · exfalso
      have hDeq : D ⊓ oQ H = D :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardD, hk']; norm_num)
      exact htQ (inf_eq_left.1 hDeq htD)
  have hDQ0 : D ⊓ q0Sub H x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyQ0⟩
    have hyN : y ∈ nQ H x := hDQ ▸ (⟨hyD, q0Sub_le_Q hyQ0⟩ : y ∈ D ⊓ oQ H)
    exact Subgroup.mem_bot.2 (h.nQ_inf_q0 hyN hyQ0)
  have hsup : D ⊔ q0Sub H x = S := by
    refine le_antisymm (sup_le hDS (q0Sub_le_Q.trans h.sig.Q_le_S)) ?_
    intro s hs
    rcases h.sig.mul_inv_mem hs htS htQ with h1 | h1
    · obtain ⟨n, hn, q₀, hq₀, rfl⟩ := h.decomp h1
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hND hn)) (Subgroup.mem_sup_right hq₀)
    · obtain ⟨n, hn, q₀, hq₀, hnq⟩ := h.decomp h1
      have hs' : s = n * q₀ * t := by
        calc s = (s * t⁻¹) * t := by group
          _ = n * q₀ * t := by rw [hnq]
      rw [hs']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hND hn))
        (Subgroup.mem_sup_right hq₀)) (Subgroup.mem_sup_left htD)
  exact ⟨h.sig.gen h.ord, nQ H x, D, q0Sub H x, h.isKleinFour_nQ, hND, hDS,
    q0Sub_le_Q.trans h.sig.Q_le_S, hDc, hDQ0, hsup, ⟨eD⟩,
    fun q hq => (mem_q0Sub.1 hq).2.symm, fun v hv => hNn.conj_mem v hv x⟩

end CFSG.Quasithin.Fan86.Sigma3
