module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Perf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private theorem s16c1_G47_oddCore_eq_pPrimeCore_two (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  simp_rw [Nat.coprime_two_left]

private instance s16c1_G47_oddCore_characteristic (H : Type*) [Group H] :
    (CFSG.oddCore H).Characteristic := by
  rw [s16c1_G47_oddCore_eq_pPrimeCore_two]
  infer_instance

private theorem s16c1_G47_odd_card_oddCore (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [s16c1_G47_oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

private theorem s16c1_G47_normalizer_zpowers_card {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = 120) {u g : X} (hu : orderOf u = 5)
    (hgu : g * u * g⁻¹ ∉ Subgroup.zpowers u) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers u : Set X)) = 20 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Subgroup X := Subgroup.zpowers u
  have hPcard : Nat.card P = 5 := by
    show Nat.card (Subgroup.zpowers u) = 5
    rw [Nat.card_zpowers, hu]
  have hPidx : P.index = 24 := by
    have h := Subgroup.index_mul_card (H := P)
    rw [hPcard] at h
    have h' : P.index * 5 = 120 := by rwa [hcard] at h
    omega
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  let Ps : Sylow 5 X := hP5.toSylow (by rw [hPidx]; norm_num)
  have hPs_coe : (Ps : Subgroup X) = P :=
    IsPGroup.toSylow_coe (hP1 := hP5) (hP2 := by rw [hPidx]; norm_num)
  haveI : Finite (Sylow 5 X) :=
    Finite.of_injective (fun Q : Sylow 5 X => (Q : Set X))
      (fun Q R h => SetLike.coe_injective h)
  have hg_smul_ne : g • Ps ≠ Ps := by
    intro hsmul
    have hgmem : g ∈ Subgroup.normalizer (Ps : Set X) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hsmul
    have huPs : u ∈ (Ps : Subgroup X) := by
      rw [hPs_coe]
      exact Subgroup.mem_zpowers u
    have hmemP : g * u * g⁻¹ ∈ P := by
      have hmem : g * u * g⁻¹ ∈ (Ps : Subgroup X) :=
        (Subgroup.mem_normalizer_iff.mp hgmem u).mp huPs
      rwa [hPs_coe] at hmem
    exact hgu hmemP
  have hn_ne_one : Nat.card (Sylow 5 X) ≠ 1 := by
    intro hn1
    haveI : Subsingleton (Sylow 5 X) := (Nat.card_eq_one_iff_unique.mp hn1).1
    exact hg_smul_ne (Subsingleton.elim _ _)
  have hn_dvd : Nat.card (Sylow 5 X) ∣ 24 := by
    have h := Sylow.card_dvd_index Ps
    have hPsidx : Ps.index = 24 := by
      show (Ps : Subgroup X).index = 24
      rw [hPs_coe, hPidx]
    rw [hPsidx] at h
    exact h
  have hn_mod : Nat.card (Sylow 5 X) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 X
  have hn_eq6 : Nat.card (Sylow 5 X) = 6 := by
    have hd : Nat.card (Sylow 5 X) ∈ (Finset.Icc 1 24).filter (fun k => k ∣ 24) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.card_pos, Nat.le_of_dvd (by norm_num) hn_dvd⟩, hn_dvd⟩
    have hset : (Finset.Icc 1 24).filter (fun k => k ∣ 24) =
        ({1, 2, 3, 4, 6, 8, 12, 24} : Finset ℕ) := by decide
    rw [hset] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h | h | h | h | h | h
    · exact False.elim (absurd h hn_ne_one)
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
    · exact h
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
    · rw [h] at hn_mod; norm_num [Nat.ModEq] at hn_mod
  have hidx : (Subgroup.normalizer (P : Set X)).index = 6 := by
    have h1 := Sylow.card_eq_index_normalizer Ps
    rw [hn_eq6] at h1
    have hset : (Ps : Set X) = (P : Set X) :=
      congrArg (fun S : Subgroup X => (S : Set X)) hPs_coe
    rw [← hset]
    exact h1.symm
  have h3 := Subgroup.index_mul_card (H := Subgroup.normalizer (P : Set X))
  rw [hidx, hcard] at h3
  have : Nat.card (Subgroup.normalizer (P : Set X)) = 20 := by omega
  exact this

private theorem s16c1_G47_five_dvd_contra {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = 120) {K : Subgroup X} (hK : K.Normal)
    {u g : X} (hu : orderOf u = 5)
    (hgu : g * u * g⁻¹ ∉ Subgroup.zpowers u)
    (hKc : Nat.card K = 5 ∨ Nat.card K = 15) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Subgroup X := Subgroup.zpowers u
  have hPcard : Nat.card P = 5 := by
    show Nat.card (Subgroup.zpowers u) = 5
    rw [Nat.card_zpowers, hu]
  have hPidx : P.index = 24 := by
    have h := Subgroup.index_mul_card (H := P)
    rw [hPcard] at h
    have h' : P.index * 5 = 120 := by rwa [hcard] at h
    omega
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  let Ps : Sylow 5 X := hP5.toSylow (by rw [hPidx]; norm_num)
  have hPs_coe : (Ps : Subgroup X) = P :=
    IsPGroup.toSylow_coe (hP1 := hP5) (hP2 := by rw [hPidx]; norm_num)
  haveI : Finite (Sylow 5 X) :=
    Finite.of_injective (fun Q : Sylow 5 X => (Q : Set X))
      (fun Q R h => SetLike.coe_injective h)
  have hdvdK : 5 ∣ Nat.card (↥K) :=
    hKc.elim (fun h => by rw [h] <;> norm_num) (fun h => by rw [h] <;> norm_num)
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 hdvdK
  have hy0ord : orderOf (y : X) = 5 := by rw [Subgroup.orderOf_coe, hyord]
  let A : Subgroup X := Subgroup.zpowers (y : X)
  have hAcard : Nat.card A = 5 := by
    show Nat.card (Subgroup.zpowers (y : X)) = 5
    rw [Nat.card_zpowers, hy0ord]
  have hA5 : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
  have hA_le_K : A ≤ K := by
    show Subgroup.zpowers (y : X) ≤ K
    rw [Subgroup.zpowers_le]
    exact y.2
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (p := 5) hA5
  have hQcard : Nat.card Q = 5 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have h5dvd : 5 ∣ Nat.card Q := by
      have h := Subgroup.card_dvd_of_le hAQ
      rwa [hAcard] at h
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      rw [hk, hk0'] at h5dvd
      norm_num at h5dvd
    have hknle : k ≤ 1 := by
      by_contra hkn
      have hk2 : 2 ≤ k := by omega
      have hdvd : Nat.card Q ∣ 120 := by
        simpa [hcard] using Subgroup.card_subgroup_dvd_card (Q : Subgroup X)
      rw [hk] at hdvd
      have hdvd2 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 hk2
      have : 5 ^ 2 ∣ 120 := hdvd2.trans hdvd
      norm_num at this
    have hk1 : k = 1 := by omega
    rw [hk, hk1]
    norm_num
  have hQA : A = Q := Subgroup.eq_of_le_of_card_ge hAQ (by rw [hQcard, hAcard])
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq X Q Ps
  have huPs : u ∈ (Ps : Subgroup X) := by
    rw [hPs_coe]
    exact Subgroup.mem_zpowers u
  have hu_map : u ∈ (Q : Subgroup X).map (MulAut.conj h) := by
    have hmem : u ∈ ((h • Q : Sylow 5 X) : Subgroup X) := by
      rw [hh]
      exact huPs
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmem
  obtain ⟨q, hqQ, hqeq⟩ := Subgroup.mem_map.mp hu_map
  have hqA : q ∈ A := by
    rw [← hQA] at hqQ
    exact hqQ
  have hqK : q ∈ K := hA_le_K hqA
  have huK : u ∈ K := by
    have hconj : h * q * h⁻¹ ∈ K := hK.conj_mem q hqK h
    rw [← hqeq]
    simpa [MulAut.conj_apply] using hconj
  have hu'K : g * u * g⁻¹ ∈ K := hK.conj_mem u huK g
  have hu'ord : orderOf (g * u * g⁻¹) = 5 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu] using h
  let A2 : Subgroup X := Subgroup.zpowers u
  let B2 : Subgroup X := Subgroup.zpowers (g * u * g⁻¹)
  have hA2card : Nat.card A2 = 5 := by
    show Nat.card (Subgroup.zpowers u) = 5
    rw [Nat.card_zpowers, hu]
  have hB2card : Nat.card B2 = 5 := by
    show Nat.card (Subgroup.zpowers (g * u * g⁻¹)) = 5
    rw [Nat.card_zpowers, hu'ord]
  have hA2K : A2 ≤ K := by
    show Subgroup.zpowers u ≤ K
    rw [Subgroup.zpowers_le]
    exact huK
  have hB2K : B2 ≤ K := by
    show Subgroup.zpowers (g * u * g⁻¹) ≤ K
    rw [Subgroup.zpowers_le]
    exact hu'K
  have hA2_ne_B2 : A2 ≠ B2 := by
    intro heq
    have hmem : g * u * g⁻¹ ∈ A2 := by
      rw [heq]
      exact Subgroup.mem_zpowers (g * u * g⁻¹)
    exact hgu (show g * u * g⁻¹ ∈ Subgroup.zpowers u from hmem)
  rcases hKc with hK5 | hK15
  · have hA2_eq : A2 = K := Subgroup.eq_of_le_of_card_ge hA2K (by rw [hA2card, hK5])
    have hB2_eq : B2 = K := Subgroup.eq_of_le_of_card_ge hB2K (by rw [hB2card, hK5])
    exact hA2_ne_B2 (hA2_eq.trans hB2_eq.symm)
  · have hKcard15 : Nat.card (↥K) = 15 := hK15
    let A' : Subgroup ↥K := A2.subgroupOf K
    let B' : Subgroup ↥K := B2.subgroupOf K
    have hA'card : Nat.card A' = 5 := by
      show Nat.card (A2.subgroupOf K) = 5
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2K).toEquiv, hA2card]
    have hB'card : Nat.card B' = 5 := by
      show Nat.card (B2.subgroupOf K) = 5
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB2K).toEquiv, hB2card]
    have hA'5 : IsPGroup 5 A' := IsPGroup.of_card (n := 1) (by rw [hA'card]; norm_num)
    have hB'5 : IsPGroup 5 B' := IsPGroup.of_card (n := 1) (by rw [hB'card]; norm_num)
    have hA'idx : A'.index = 3 := by
      have h := Subgroup.index_mul_card (H := A')
      rw [hA'card, hKcard15] at h
      omega
    have hB'idx : B'.index = 3 := by
      have h := Subgroup.index_mul_card (H := B')
      rw [hB'card, hKcard15] at h
      omega
    let A's : Sylow 5 ↥K := hA'5.toSylow (by rw [hA'idx]; norm_num)
    let B's : Sylow 5 ↥K := hB'5.toSylow (by rw [hB'idx]; norm_num)
    have hA's_ne : A's ≠ B's := by
      intro heq
      have hsub : A' = B' := by
        have h1 : (A's : Subgroup ↥K) = (B's : Subgroup ↥K) :=
          congrArg (fun S : Sylow 5 ↥K => (S : Subgroup ↥K)) heq
        rwa [show (A's : Subgroup ↥K) = A' from
              IsPGroup.toSylow_coe (hP1 := hA'5) (hP2 := by rw [hA'idx]; norm_num),
             show (B's : Subgroup ↥K) = B' from
              IsPGroup.toSylow_coe (hP1 := hB'5) (hP2 := by rw [hB'idx]; norm_num)] at h1
      have h2 : A2 = B2 := by
        have := Subgroup.subgroupOf_inj.mp hsub
        rwa [inf_eq_left.mpr hA2K, inf_eq_left.mpr hB2K] at this
      exact hA2_ne_B2 h2
    haveI : Finite (Sylow 5 ↥K) :=
      Finite.of_injective (fun S : Sylow 5 ↥K => (S : Set ↥K))
        (fun S T h => SetLike.coe_injective h)
    have hm_mod : Nat.card (Sylow 5 ↥K) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 ↥K
    have hm_dvd : Nat.card (Sylow 5 ↥K) ∣ 3 := by
      have hAsIdx : (A's : Subgroup ↥K).index = 3 := by
        rw [show (A's : Subgroup ↥K) = A' from
              IsPGroup.toSylow_coe (hP1 := hA'5) (hP2 := by rw [hA'idx]; norm_num)]
        exact hA'idx
      have h := Sylow.card_dvd_index A's
      rw [show A's.index = 3 from hAsIdx] at h
      exact h
    have hm_eq1 : Nat.card (Sylow 5 ↥K) = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hm_dvd with h | h
      · exact h
      · rw [h] at hm_mod; norm_num [Nat.ModEq] at hm_mod
    haveI : Subsingleton (Sylow 5 ↥K) := (Nat.card_eq_one_iff_unique.mp hm_eq1).1
    exact hA's_ne (Subsingleton.elim _ _)

theorem s16c1_G47_sl2five_odd_normal {X : Type} [Group X] (hX : IsSL2Prime X 5)
    {K : Subgroup X} (hK : K.Normal) (hodd : Odd (Nat.card K)) : K = ⊥ := by
  classical
  obtain ⟨hcard, hperf, u, t, g, hu, ht, hgu⟩ := s16c1_sl2five_facts hX
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 (by simpa [commutator_def] using hperf)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnorm_card : Nat.card (Subgroup.normalizer (Subgroup.zpowers u : Set X)) = 20 :=
    s16c1_G47_normalizer_zpowers_card hcard hu hgu
  have hdvd120 : Nat.card K ∣ 120 := by
    simpa [hcard] using Subgroup.card_subgroup_dvd_card K
  have hcop8 : Nat.Coprime (Nat.card K) 8 := by
    have h2 : Nat.Coprime (Nat.card K) 2 := Nat.coprime_two_right.mpr hodd
    simpa using h2.pow_right 3
  have hdvd15 : Nat.card K ∣ 15 := by
    have h8 : Nat.card K ∣ 8 * 15 := by
      rw [show (8 * 15 : ℕ) = 120 by norm_num]
      exact hdvd120
    exact (hcop8.dvd_mul_left).1 h8
  have hno5 : ¬ 5 ∣ Nat.card K := by
    intro h5dvd
    have hKc : Nat.card K = 5 ∨ Nat.card K = 15 := by
      have hd : Nat.card K ∈ (Finset.Icc 1 15).filter (fun k => k ∣ 15) := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.card_pos, Nat.le_of_dvd (by norm_num) hdvd15⟩, hdvd15⟩
      have hset : (Finset.Icc 1 15).filter (fun k => k ∣ 15) =
          ({1, 3, 5, 15} : Finset ℕ) := by decide
      rw [hset] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with h | h | h | h
      · rw [h] at h5dvd; norm_num at h5dvd
      · rw [h] at h5dvd; norm_num at h5dvd
      · exact Or.inl h
      · exact Or.inr h
    exact s16c1_G47_five_dvd_contra hcard hK hu hgu hKc
  have hno3 : Nat.card K ≠ 3 := by
    intro hK3
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hdvd3 : 3 ∣ Nat.card (↥K) := by
      rw [hK3]
    obtain ⟨c, hcorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 hdvd3
    have hcomm : ∀ x ∈ (⊤ : Subgroup X), ∀ k ∈ (K : Set X), x * k * x⁻¹ = k :=
      s16c1_G47_perfect_comm (Γ := X) (X := (⊤ : Subgroup X)) (W := K)
        (hX := inferInstance)
        (hXW := by rw [Subgroup.normalizer_eq_top_iff.mpr hK])
        (hW := by rw [hK3]; norm_num)
    let c0 : X := (c : X)
    have hc0K : c0 ∈ K := c.2
    have hc0ord : orderOf c0 = 3 := by
      show orderOf (c : X) = 3
      rw [Subgroup.orderOf_coe, hcorder]
    have hcu : Commute u c0 := by
      have h := hcomm u (Subgroup.mem_top u) c0 hc0K
      show u * c0 = c0 * u
      calc u * c0 = u * c0 * u⁻¹ * u := by group
        _ = c0 * u := by rw [h]
    have hw_order : orderOf (u * c0) = 15 := by
      have hco : Nat.Coprime (orderOf u) (orderOf c0) := by rw [hu, hc0ord]; norm_num
      have h := hcu.orderOf_mul_eq_mul_orderOf_of_coprime hco
      rw [hu, hc0ord] at h
      norm_num at h
      exact h
    have hc0_central : c0 ∈ Subgroup.centralizer (Subgroup.zpowers u : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : p ∈ Subgroup.zpowers u := hp
      rw [Subgroup.mem_zpowers_iff] at hp'
      obtain ⟨k, rfl⟩ := hp'
      exact (hcu.zpow_left k).eq
    have hc0_norm : c0 ∈ Subgroup.normalizer (Subgroup.zpowers u : Set X) :=
      Subgroup.centralizer_le_normalizer _ hc0_central
    have hu_norm : u ∈ Subgroup.normalizer (Subgroup.zpowers u : Set X) :=
      (Subgroup.zpowers u).le_normalizer (Subgroup.mem_zpowers u)
    have hw_norm : u * c0 ∈ Subgroup.normalizer (Subgroup.zpowers u : Set X) :=
      mul_mem hu_norm hc0_norm
    have hw_dvd : orderOf (u * c0) ∣
        Nat.card (Subgroup.normalizer (Subgroup.zpowers u : Set X)) :=
      Subgroup.orderOf_dvd_natCard _ hw_norm
    rw [hw_order, hnorm_card] at hw_dvd
    norm_num at hw_dvd
  have hmem : Nat.card K ∈ ({1, 3, 5, 15} : Finset ℕ) := by
    have hd : Nat.card K ∈ (Finset.Icc 1 15).filter (fun k => k ∣ 15) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.card_pos, Nat.le_of_dvd (by norm_num) hdvd15⟩, hdvd15⟩
    have hset : (Finset.Icc 1 15).filter (fun k => k ∣ 15) =
        ({1, 3, 5, 15} : Finset ℕ) := by decide
    rwa [hset] at hd
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h3 | h5 | h15
  · exact Subgroup.eq_bot_of_card_eq K h1
  · exact (hno3 h3).elim
  · exact (hno5 (by rw [h5] <;> norm_num)).elim
  · exact (hno5 (by rw [h15] <;> norm_num)).elim

theorem s16c1_G47_oddNormal {Hs : Type} [Group Hs] [Finite Hs] {Ys Xs N : Subgroup Hs}
    (hY : Ys.Normal) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5) (hN : N ≤ Ys)
    (hNn : (N.subgroupOf Ys).Normal) (hNodd : Odd (Nat.card N)) :
    ∃ N₀ : Subgroup Hs, N₀.Normal ∧ Odd (Nat.card N₀) ∧ N ≤ N₀ ∧ N₀ ≤ Ys ∧ Xs ⊓ N₀ = ⊥ := by
  classical
  haveI : Ys.Normal := hY
  let N₀ : Subgroup Hs := (CFSG.oddCore ↥Ys).map Ys.subtype
  have hN₀norm : N₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal g y, ?_, ?_⟩
    · have hchar : (CFSG.oddCore ↥Ys).Characteristic := s16c1_G47_oddCore_characteristic ↥Ys
      have h := hchar.fixed (MulAut.conjNormal g)
      have hy' : y ∈ (CFSG.oddCore ↥Ys).comap (MulAut.conjNormal g).toMonoidHom := by
        rw [h]
        exact hy
      exact Subgroup.mem_comap.mp hy'
    · exact MulAut.conjNormal_apply g y
  have hN₀odd' : Odd (Nat.card N₀) := by
    have h : Odd (Nat.card (CFSG.oddCore ↥Ys)) := s16c1_G47_odd_card_oddCore ↥Ys
    show Odd (Nat.card ((CFSG.oddCore ↥Ys).map Ys.subtype))
    rw [Subgroup.card_map_of_injective Ys.subtype_injective]
    exact h
  have hNN₀ : N ≤ N₀ := by
    have hNsub : N.subgroupOf Ys ≤ CFSG.oddCore ↥Ys := by
      refine le_sSup (s := {M : Subgroup ↥Ys | M.Normal ∧ Odd (Nat.card M)}) ⟨hNn, ?_⟩
      have hcard : Nat.card (N.subgroupOf Ys) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
      rw [hcard]
      exact hNodd
    calc N = (N.subgroupOf Ys).map Ys.subtype := (Subgroup.map_subgroupOf_eq_of_le hN).symm
      _ ≤ (CFSG.oddCore ↥Ys).map Ys.subtype := Subgroup.map_mono hNsub
  have hN₀le : N₀ ≤ Ys := Subgroup.map_subtype_le (CFSG.oddCore ↥Ys)
  have hinf : Xs ⊓ N₀ = ⊥ := by
    have hKsub_normal : ((Xs ⊓ N₀).subgroupOf Xs).Normal := by
      refine ⟨fun k hk x => ?_⟩
      have hk' : (k : Hs) ∈ Xs ⊓ N₀ := Subgroup.mem_subgroupOf.mp hk
      have hxN : (x : Hs) * (k : Hs) * (x : Hs)⁻¹ ∈ Xs ⊓ N₀ := by
        refine Subgroup.mem_inf.2
          ⟨?_, hN₀norm.conj_mem (k : Hs) (Subgroup.mem_inf.1 hk').2 (x : Hs)⟩
        exact Xs.mul_mem (Xs.mul_mem x.2 (Subgroup.mem_inf.1 hk').1) (Xs.inv_mem x.2)
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hxN)
    have hKsub_odd : Odd (Nat.card ((Xs ⊓ N₀).subgroupOf Xs)) := by
      have hcard : Nat.card ((Xs ⊓ N₀).subgroupOf Xs) = Nat.card ↥(Xs ⊓ N₀) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : Xs ⊓ N₀ ≤ Xs)).toEquiv
      rw [hcard]
      exact hN₀odd'.of_dvd_nat
        (Subgroup.card_dvd_of_le (inf_le_right : Xs ⊓ N₀ ≤ N₀))
    have hKsub_bot : (Xs ⊓ N₀).subgroupOf Xs = ⊥ :=
      s16c1_G47_sl2five_odd_normal (X := ↥Xs) hX hKsub_normal hKsub_odd
    have hdis : Disjoint (Xs ⊓ N₀) Xs := Subgroup.subgroupOf_eq_bot.mp hKsub_bot
    exact hdis.eq_bot_of_le inf_le_left
  exact ⟨N₀, hN₀norm, hN₀odd', hNN₀, hN₀le, hinf⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
